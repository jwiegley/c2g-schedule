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
import Control.Monad (unless)
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy qualified as BL
import Data.Char (isDigit, toLower)
import Data.Csv (FromNamedRecord, decodeByName)
import Data.Foldable
import Data.Function (on)
import Data.List (delete, genericLength, groupBy, intercalate, nub, sort, sortOn, tails)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Ord (comparing)
import Data.Proxy
import Data.Reflection
import Data.SBV
import Data.Time
import Data.Vector qualified as V
import Debug.Trace
import GHC.Generics
import System.Environment (getArgs)
import Text.Read (readEither)
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
    slotFour :: String,
    slotFive :: String,
    slotSix :: String,
    affinity :: String,
    aversion :: String,
    facilitator :: String,
    attending :: String
  }
  deriving (Show, Eq, Generic)

instance FromNamedRecord RawParticipant

data Participant = Participant
  { pName :: String,
    pInstance :: Int,
    pFacilitatorLevel :: Int,
    pIsBlack :: Bool,
    pAvailability :: [Available],
    pCanAttend :: Int,
    pPairWith :: [String],
    pDoNotPairWith :: [String],
    pPreferredMinGroupSize :: Maybe Size,
    pPreferredMaxGroupSize :: Maybe Size
  }
  deriving (Show, Eq)

-- | A solution is a sequence of group assignments for each participant
data Solution s v = Solution
  { solAssignments :: [v], -- participants -> group number
    solBlackFacilitators :: [v], -- groups -> black facilitator count
    solFacilitators :: [v], -- groups -> total facilitator count
    solTotalFacilitatorLevel :: [v], -- groups -> total facilitator level
    solNonFacilitators :: [v], -- groups -> total non-facilitator count
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
          (take glen (drop (glen + glen + glen + plen) a))
          (take glen (drop (glen + glen + glen + glen + plen) a))
          (take glen (drop (glen + glen + glen + glen + glen + plen) a)),
        bs
      )

-- Create a group for every time slot where there's an available facilitator.
-- The schedule will not assign anyone to groups that fail to meet the
-- necessary criteria.
determineGroups :: Size -> [Participant] -> [(Group, [Participant])]
determineGroups minGroupSize ps =
  checkParticipants $
    filter (\(g, p) -> length p >= fromIntegral minGroupSize) $
      Map.assocs $
        foldl'
          (\acc p -> Map.unionWith (++) acc (f p))
          Map.empty
          ps
  where
    checkParticipants :: [(Group, [Participant])] -> [(Group, [Participant])]
    checkParticipants gps =
      let avails = map (gAvail . fst) gps
       in if all
            ( \p ->
                any (`elem` avails) (pAvailability p)
                  || trace (pName p ++ " does not fit") True
            )
            ps
            then gps
            else []

    f :: Participant -> Map Group [Participant]
    f p = (\f -> foldl' f Map.empty (pAvailability p)) $ \acc a ->
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
        && length (solTotalFacilitatorLevel s) == length g
        && length (solNonFacilitators s) == length g
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
      .&& attrMatch solFacilitators facilitators
      -- Track how many facilitators are in each group
      .&& attrMatch solTotalFacilitatorLevel totalFacilitatorLevel
      -- Track how many non-facilitators are in each group
      .&& attrMatch solNonFacilitators nonFacilitators
      -- Track how many black facilitators are in each group
      .&& attrMatch solBlackFacilitators blackFacilitators
      -- Track how many participants are in each group
      .&& attrMatch solParticipants participants
      -- Track how many black participants are in each group
      .&& attrMatch solBlackParticipants blackParticipants
      -- Ensure correct group sizes
      .&& sAll
        ( \gi ->
            participants gi .== 0
              .|| ( participants gi .>= fromIntegral (max 1 minGroupSize)
                      .&& participants gi .<= fromIntegral maxGroupSize
                      .&& facilitators gi .> 0
                      .&& nonFacilitators gi .> 2
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
    attrMatch f g = ala sAnd f ((.==) . g)

    ala k acc f = k (zipWith f [0 ..] (acc s))

    eachParticipant Participant {..} x Group {..} gi =
      fromBool (gAvail `elem` pAvailability)
        .&& maybe
          minBound
          fromIntegral
          pPreferredMinGroupSize
          .<= solParticipants s !! gi
        .&& maybe
          maxBound
          fromIntegral
          pPreferredMaxGroupSize
          .>= solParticipants s !! gi

    participants = countParticipants (const True)
    blackParticipants = countParticipants pIsBlack

    isFacilitator p = pFacilitatorLevel p >= 3
    isNonFacilitator p = pFacilitatorLevel p == 0
    facilitators = countParticipants isFacilitator
    nonFacilitators = countParticipants isNonFacilitator
    blackFacilitators = countParticipants (\i -> isFacilitator i && pIsBlack i)

    totalFacilitatorLevel :: Int -> SWord8
    totalFacilitatorLevel gi =
      ala
        sum
        solAssignments
        ( \pi a ->
            ite
              (fromIntegral gi .== a)
              (fromIntegral (pFacilitatorLevel (p !! pi)))
              0
        )

    countParticipants :: (Participant -> Bool) -> Int -> SWord8
    countParticipants f gi =
      ala
        sum
        solAssignments
        ( \pi a ->
            oneIf (fromIntegral gi .== a .&& fromBool (f (p !! pi)))
        )

saveSchedule :: [Group] -> [Participant] -> Solution s Word8 -> IO ()
saveSchedule g p s =
  forM_ (nub (solAssignments s)) $ \gi -> do
    let name = gName (g !! fromIntegral gi)
    writeFile (name ++ ".csv") $
      concat $
        concat
          ( zipWith
              (\pi i -> [getName (p !! pi) | i == gi])
              [0 ..]
              (solAssignments s)
          )
  where
    getName i =
      ( if pIsBlack i
          then "non-white"
          else ""
      )
        ++ ","
        ++ show (pFacilitatorLevel i)
        ++ ","
        ++ pName i
        ++ "\n"

pcount :: [Participant] -> Int
pcount = length . groupBy ((==) `on` pName)

scheduleGroups :: Size -> Size -> [Participant] -> IO ()
scheduleGroups minGroupSize maxGroupSize p = do
  let g = determineGroups minGroupSize p
      g' = map fst g
      p' = nub (concatMap snd g)
  putStrLn "Finding scheduling solution..."
  putStrLn $ show (pcount p') ++ " participants"
  putStrLn $
    show (pcount (filter (\x -> pFacilitatorLevel x > 0) p'))
      ++ " facilitators"
  putStrLn $ show minGroupSize ++ " is the minimum group size"
  putStrLn $ show maxGroupSize ++ " is the maximum group size"
  putStrLn $ show (length g') ++ " groups selected by facilitators"
  putStrLn $ show (length g') ++ " eligible groups after initial filtering:"
  forM_ (sortOn (gAvail . fst) g) $ \(grp, ps) -> do
    putStrLn $ "  " ++ gName grp ++ " (" ++ show (length ps) ++ ")"
  work g' p'
  where
    work g p = do
      reify (length g, length p) $ \(Proxy :: Proxy s) -> do
        LexicographicResult res <- optimize Lexicographic $ do
          solAssignments <- mkFreeVars (length p)
          solBlackFacilitators <- mkFreeVars (length g)
          solFacilitators <- mkFreeVars (length g)
          solTotalFacilitatorLevel <- mkFreeVars (length g)
          solNonFacilitators <- mkFreeVars (length g)
          solBlackParticipants <- mkFreeVars (length g)
          solParticipants <- mkFreeVars (length g)
          constrain $
            isValid minGroupSize maxGroupSize g p Solution {..}
          maximize "number-facilitators" $ foldl' smin 0 solFacilitators
          maximize "facilitator-level" $ foldl' smin 0 solTotalFacilitatorLevel
          maximize "number-non-facilitators" $ foldl' smin 0 solNonFacilitators
          maximize "balance-participants" $ foldl' smin 0 solBlackParticipants
        case extractModel res :: Maybe (Solution s Word8) of
          Nothing -> putStrLn "No model found"
          Just model -> dispSolution g p model
    dispSolution :: [Group] -> [Participant] -> Solution s Word8 -> IO ()
    dispSolution g p' model = do
      saveSchedule g p' model
      putStrLn $
        "\nValid: "
          ++ show (isValid minGroupSize maxGroupSize g p' (literalize model))
      where
        literalize s =
          s
            { solAssignments = map literal (solAssignments s),
              solBlackFacilitators = map literal (solBlackFacilitators s),
              solFacilitators = map literal (solFacilitators s),
              solTotalFacilitatorLevel = map literal (solTotalFacilitatorLevel s),
              solNonFacilitators = map literal (solNonFacilitators s),
              solBlackParticipants = map literal (solBlackParticipants s),
              solParticipants = map literal (solParticipants s)
            }

-- Given a CSV file of the proper schedule, generate and display an updated
-- version of that CSV file which assigns participants to groups.
readParticipants :: FilePath -> IO [Participant]
readParticipants path = do
  csv <- BL.readFile path
  let rawParticipants = readRawParticipants csv
  return $ concatMap (expandParticipant . cookParticipant) rawParticipants
  where
    readRawParticipants :: ByteString -> [RawParticipant]
    readRawParticipants bs = case decodeByName bs of
      Left err -> error err
      Right (_, vec) -> V.toList vec

facilitatorLevel :: String -> Int
facilitatorLevel "facilitator trainee" = 1
facilitatorLevel "new facilitator" = 2
facilitatorLevel "C facilitator" = 3
facilitatorLevel "C+ facilitator" = 4
facilitatorLevel "B facilitator" = 5
facilitatorLevel "B+ facilitator" = 6
facilitatorLevel "A facilitator" = 7
facilitatorLevel "A+ facilitator" = 8
facilitatorLevel "team coordinator" = 9
facilitatorLevel _ = 0

expandParticipant :: Participant -> [Participant]
expandParticipant p = [p]

-- expandParticipant p =
--   zipWith (\i p' -> p' {pInstance = i}) [1 ..] (replicate (pCanAttend p) p)

cookParticipant :: RawParticipant -> Participant
cookParticipant raw@RawParticipant {..} = Participant {..}
  where
    pName = firstName ++ " " ++ lastName
    pInstance = 0
    pFacilitatorLevel = facilitatorLevel facilitator
    pIsBlack = worldExperience /= ""
    pCanAttend = read attending
    pAvailability =
      fromSlot slotOne
        ++ fromSlot slotTwo
        ++ fromSlot slotThree
        ++ fromSlot slotFour
        ++ fromSlot slotFive
        ++ fromSlot slotSix
    pPairWith = []
    -- pPairWith = [map toLower affinity | affinity /= ""]
    pDoNotPairWith = []
    -- jww (2023-08-23): TODO
    -- pDoNotPairWith = [map toLower aversion | aversion /= ""]
    pPreferredMinGroupSize = Nothing
    pPreferredMaxGroupSize = Nothing

    fromSlot :: String -> [Available]
    fromSlot "" = []
    fromSlot s =
      [ Available
          { availDayOfWeek = dow (take 3 s),
            availStartTime =
              let rest = drop 4 s
                  hour = takeWhile isDigit rest
                  ampm = dropWhile isDigit rest
               in if ampm == "am" && hour == "12"
                    then 0
                    else
                      either
                        ( \msg ->
                            error $
                              "Failed to read hour from '"
                                ++ s
                                ++ "': "
                                ++ msg
                        )
                        id
                        (readEither hour)
                        * 100
                        + ( if ampm /= "am" && hour == "12"
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
  participants <- readParticipants path
  -- pPrint participants
  putStrLn "=== pairings pPairWith participants ==="
  pPrint $ pairings pPairWith participants
  -- putStrLn "=== pairings pDoNotPairWith participants ==="
  -- pPrint $ pairings pDoNotPairWith participants
  scheduleGroups 6 60 participants
