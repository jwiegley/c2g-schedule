{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Control.Arrow (second)
import Control.Exception (assert)
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy qualified as BL
import Data.Char (isDigit, toLower)
import Data.Csv (FromNamedRecord, decodeByName)
import Data.Foldable
import Data.List (genericLength, intercalate, nub, sortOn, tails)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Proxy
import Data.Reflection
import Data.SBV
import Data.Time
import Data.Vector qualified as V
import GHC.Generics
import System.Environment (getArgs)
import Text.Show.Pretty (pPrint)
import Prelude hiding (pi)

type Time = Word16

type Size = Word8

data Available = Available
  { availDayOfWeek :: DayOfWeek,
    availStartTime :: Time
  }
  deriving (Show, Ord, Eq)

data Group = Group
  { gName :: String,
    gAvail :: Available
  }
  deriving (Show, Ord, Eq)

type Rank = Word8

data RawParticipant = RawParticipant
  { firstName :: String,
    lastName :: String,
    worldExperience :: String,
    slotOne :: String,
    slotTwo :: String,
    slotThree :: String,
    affinity :: String,
    aversion :: String,
    facilitator :: String
  }
  deriving (Show, Eq, Generic)

instance FromNamedRecord RawParticipant

data Participant = Participant
  { pName :: String,
    pIsFacilitator :: Bool,
    pIsBlack :: Bool,
    pAvailability :: [Available],
    pPairWith :: [String],
    pDoNotPairWith :: [String],
    pPrefereredMinGroupSize :: Maybe Size,
    pPrefereredMaxGroupSize :: Maybe Size,
    pFixed :: Maybe Int
  }
  deriving (Show, Eq)

-- | A solution is a sequence of group assignments for each participant
data Solution s v = Solution
  { solAssignments :: [v], -- participants -> group number
    solBlackFacilitators :: [v], -- groups -> black facilitator count
    solFacilitators :: [v], -- groups -> total facilitator count
    solBlackParticipants :: [v], -- groups -> black participant count
    solParticipants :: [v] -- groups -> participant count
  }
  deriving (Show)

-- We inject the length of the group list, and the length of the participant
-- list, in order to know how to group the constant variables coming from the
-- solver.
instance
  (SatModel v, Reifies s (Int, Int)) =>
  SatModel (Solution s v)
  where
  parseCVs as = do
    let (glen, plen) = reflect (Proxy :: Proxy s)
    (a, bs) <- parseCVs as
    return
      ( Solution
          (take plen a)
          (take glen (drop plen a))
          (take glen (drop (glen + plen) a))
          (take glen (drop (glen + glen + plen) a))
          (take glen (drop (glen + glen + glen + plen) a)),
        bs
      )

-- Create a group for every time slot where there's an available facilitator.
-- The schedule will not assign anyone to groups that fail to meet the
-- necessary criteria.
determineGroups :: [Participant] -> [(Group, [Participant])]
determineGroups ps =
  Map.assocs $
    foldl'
      (\acc p -> Map.unionWith (++) acc (f p))
      Map.empty
      ps
  where
    f :: Participant -> Map Group [Participant]
    f p =
      availability (pIsFacilitator p) (pAvailability p)
      where
        availability ::
          Bool -> [Available] -> Map Group [Participant]
        availability isFacilitator avails =
          (\f -> foldl' f Map.empty avails) $ \acc a ->
            let dow = availDayOfWeek a
                time = availStartTime a
             in Map.unionWith (++) acc $
                  Map.fromList
                    [ ( Group
                          { gName = show dow ++ " " ++ show time,
                            gAvail = a
                          },
                        [p]
                      )
                    ]

-- Given a list of participants, determine the list of "pair ups" -- either
-- participants with each other, or with a stated group.
pairings :: (Participant -> [String]) -> [Participant] -> [(Int, Int)]
pairings accessor =
  nub
    . g
    . foldr f Map.empty
    . zipWith
      ( \pi i ->
          Map.fromList
            ( map
                (,[pi])
                (map toLower (pName i) : accessor i)
            )
      )
      [0 ..]
  where
    f :: Map String [Int] -> Map String [Int] -> Map String [Int]
    f = Map.unionWithKey (const (++))

    g :: Map String [Int] -> [(Int, Int)]
    g = foldr (\x -> (pairs x ++)) [] . Map.elems
      where
        pairs :: [a] -> [(a, a)]
        pairs l = [(x, y) | (x : ys) <- tails l, y <- ys]

isValid ::
  Size ->
  Size ->
  [Group] ->
  [Participant] ->
  Solution s SWord8 ->
  SBool
isValid minGroupSize maxGroupSize g p s =
  assert
    ( length (solAssignments s) == length p
        && length (solBlackFacilitators s) == length g
        && length (solFacilitators s) == length g
        && length (solParticipants s) == length g
    )
    $
    -- Every participant is assigned to an applicable group, and the
    -- constraints hold for being associated with that group
    ala
      sAnd
      solAssignments
      ( \pi x ->
          x .>= 0
            .&& x .< genericLength g
            .&& sAll
              ( \gi ->
                  fromIntegral gi .== x
                    .=> eachParticipant (p !! pi) x (g !! gi) gi
              )
              [0 .. length g - 1]
      )
      -- Track how many facilitators are in each group
      .&& ala sAnd solFacilitators (\gi x -> x .== facilitators gi)
      -- Track how many black facilitators are in each group
      .&& ala sAnd solBlackFacilitators (\gi x -> x .== blackFacilitators gi)
      -- Track how many participants are in each group
      .&& ala sAnd solParticipants (\gi x -> x .== participants gi)
      -- Track how many black participants are in each group
      .&& ala sAnd solBlackParticipants (\gi x -> x .== blackParticipants gi)
      -- Ensure correct group sizes
      .&& sAll
        ( \gi ->
            (participants gi .== 0 .&& facilitators gi .== 0)
              .|| ( participants gi .> 0
                      .&& participants gi .>= fromIntegral minGroupSize
                      .&& participants gi .<= fromIntegral maxGroupSize
                      .&& facilitators gi .> 0
                      -- jww (2023-08-23): TODO
                      -- .&& blackFacilitators gi .> 0
                  )
        )
        [0 .. length g - 1]
      -- All pairings are honored
      .&& sAll
        ( \(i, j) ->
            solAssignments s !! i .== solAssignments s !! j
        )
        (pairings pPairWith p)
      .&& sAll
        ( \(i, j) ->
            solAssignments s !! i ./= solAssignments s !! j
        )
        (pairings pDoNotPairWith p)
  where
    -- jww (2023-08-23): TODO:
    -- - Ensure total facilitator skill level is above a threshold
    -- - Ensure there are not too many facilitator assistants
    -- - Facilitators and assistants can be in multiple sessions

    eachParticipant Participant {..} x Group {..} gi =
      fromBool (gAvail `elem` pAvailability)
        .&& maybe
          minBound
          fromIntegral
          pPrefereredMinGroupSize
          .<= solParticipants s !! gi
        .&& maybe
          maxBound
          fromIntegral
          pPrefereredMaxGroupSize
          .>= solParticipants s !! gi
        .&& x .== maybe x fromIntegral pFixed

    ala k acc f = k (zipWith f [0 ..] (acc s))

    participants = countParticipants (const True)
    blackParticipants = countParticipants pIsBlack
    facilitators = countParticipants pIsFacilitator
    blackFacilitators =
      countParticipants (\i -> pIsFacilitator i && pIsBlack i)

    countParticipants :: (Participant -> Bool) -> Int -> SWord8
    countParticipants f gi =
      ala
        sum
        solAssignments
        ( \pi a ->
            oneIf
              ( fromIntegral gi .== a
                  .&& fromBool (f (p !! pi))
              )
        )

showSchedule :: [Group] -> [Participant] -> Solution s Word8 -> String
showSchedule g p s =
  unlines $ intercalate [""] $ map f assigned
  where
    assigned = nub (solAssignments s)

    f :: Word8 -> [String]
    f gi =
      [ gName (g !! fromIntegral gi),
        "===================="
      ]
        ++ concat
          ( zipWith
              (\pi i -> [getName (p !! pi) | i == gi])
              [0 ..]
              (solAssignments s)
          )

    getName i =
      ( if pIsBlack i
          then "*"
          else " "
      )
        ++ ( if pIsFacilitator i
               then "F"
               else " "
           )
        ++ " "
        ++ pName i

scheduleGroups :: Size -> Size -> [Participant] -> IO ()
scheduleGroups minGroupSize maxGroupSize p = do
  let g = determineGroups p
  putStrLn "Finding scheduling solution..."
  putStrLn $ show (length p) ++ " participants"
  putStrLn $ show minGroupSize ++ " is the minimum group size"
  putStrLn $ show maxGroupSize ++ " is the maximum group size"
  putStrLn $ show (length g) ++ " groups selected by facilitators"
  putStrLn $ show (length g) ++ " eligible groups after initial filtering:"
  forM_ (sortOn (gAvail . fst) g) $ \(grp, ps) -> do
    putStrLn $ "  " ++ gName grp ++ " (" ++ show (length ps) ++ ")"
  reify (length g, length p) $ \(Proxy :: Proxy s) -> do
    LexicographicResult res <- optimize Lexicographic $ do
      solAssignments <- mkFreeVars (length p)
      solBlackFacilitators <- mkFreeVars (length g)
      solFacilitators <- mkFreeVars (length g)
      solBlackParticipants <- mkFreeVars (length g)
      solParticipants <- mkFreeVars (length g)
      constrain $ isValid minGroupSize maxGroupSize (map fst g) p Solution {..}
      minimize "number-facilitators" $ foldl' smax 0 solFacilitators
      maximize "balance-participants" $ foldl' smin 0 solBlackParticipants
    case extractModel res :: Maybe (Solution s Word8) of
      Nothing -> error "No model found"
      Just model -> dispSolution (map fst g) p model
  where
    dispSolution :: [Group] -> [Participant] -> Solution s Word8 -> IO ()
    dispSolution g p' model = do
      putStr $ showSchedule g p' model
      putStrLn $
        "\nValid: "
          ++ show (isValid minGroupSize maxGroupSize g p' (literalize model))
      where
        literalize s =
          s
            { solAssignments = map literal (solAssignments s),
              solBlackFacilitators = map literal (solBlackFacilitators s),
              solFacilitators = map literal (solFacilitators s),
              solBlackParticipants = map literal (solBlackParticipants s),
              solParticipants = map literal (solParticipants s)
            }

-- Given a CSV file of the proper schedule, generate and display an updated
-- version of that CSV file which assigns participants to groups.
readParticipants :: FilePath -> IO [Participant]
readParticipants path = do
  csv <- BL.readFile path
  let rawParticipants = readRawParticipants csv
  return $ map cookParticipant rawParticipants
  where
    readRawParticipants :: ByteString -> [RawParticipant]
    readRawParticipants bs = case decodeByName bs of
      Left err -> error err
      Right (_, vec) -> V.toList vec

cookParticipant :: RawParticipant -> Participant
cookParticipant raw@RawParticipant {..} = Participant {..}
  where
    pName = firstName ++ " " ++ lastName
    pIsFacilitator = facilitator == "yes"
    pIsBlack = worldExperience /= ""
    pAvailability = fromSlot slotOne ++ fromSlot slotTwo ++ fromSlot slotThree
    pPairWith = []
    -- jww (2023-08-23): TODO
    -- pPairWith = [map toLower affinity | affinity /= ""]
    pDoNotPairWith = []
    -- jww (2023-08-23): TODO
    -- pDoNotPairWith = [map toLower aversion | aversion /= ""]
    pPrefereredMinGroupSize = Nothing
    pPrefereredMaxGroupSize = Nothing
    pFixed = Nothing
    pPossibleGroups = []

    fromSlot :: String -> [Available]
    fromSlot "" = []
    fromSlot s =
      [ Available
          { availDayOfWeek = dow (take 3 s),
            availStartTime =
              let rest = drop 4 s
                  hour = takeWhile isDigit rest
                  ampm = dropWhile isDigit rest
               in if ampm == "a" && hour == "12"
                    then 0
                    else
                      read hour * 100
                        + ( if ampm /= "a" && hour == "12"
                              then 0
                              else 1200
                          )
          }
      ]

    dow :: String -> DayOfWeek
    dow "Sun" = Sunday
    dow "Mon" = Monday
    dow "Tue" = Tuesday
    dow "Wed" = Wednesday
    dow "Thu" = Thursday
    dow "Fri" = Friday
    dow "Sat" = Saturday
    dow _ = error $ "Could not parse slot for: " ++ show raw

main :: IO ()
main = do
  (path : _) <- getArgs
  -- putStrLn "=== pairings pPairWith participants ==="
  -- pPrint $ pairings pPairWith participants
  -- putStrLn "=== pairings pDoNotPairWith participants ==="
  -- pPrint $ pairings pDoNotPairWith participants
  scheduleGroups 2 40 =<< readParticipants path
