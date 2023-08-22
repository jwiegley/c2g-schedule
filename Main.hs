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

-- import Data.Csv

import Control.Exception (assert)
import Data.ByteString
import Data.Foldable
import Data.List (genericLength, intercalate, nub, tails)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Proxy
import Data.Reflection
import Data.SBV
import Data.Time
import GHC.Generics
import Prelude hiding (pi)

type Time = Word16

type Size = Word8

data Group = Group
  { gName :: String,
    gDayOfWeek :: DayOfWeek,
    gStartTime :: Time
  }
  deriving (Show)

type Rank = Word8

data Available = Available
  { availDayOfWeek :: DayOfWeek,
    availStartTime :: Time,
    availEndTime :: Time
  }
  deriving (Show, Eq)

data RawParticipant = RawParticipant
  { firstName :: String,
    lastName :: String,
    worldExperience :: String,
    slotOne :: String,
    slotTwo :: String,
    slotThree :: String,
    affinity :: String
  }
  deriving (Show, Eq, Generic)

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
determineGroups :: [Participant] -> [Group]
determineGroups = map g . Map.keys . foldMap f
  where
    f :: Participant -> Map (DayOfWeek, Time) ()
    f p = availability (pIsFacilitator p) (pAvailability p)
      where
        availability :: Bool -> [Available] -> Map (DayOfWeek, Time) ()
        availability isFacilitator = foldMap $ \a ->
          Map.fromList
            [ ((availDayOfWeek a, hour), ())
              | hour <-
                  [ actualStart isFacilitator a,
                    actualStart isFacilitator a + 50
                    .. actualEnd isFacilitator a - 200
                  ]
            ]
    g :: (DayOfWeek, Time) -> Group
    g (dow, time) =
      Group
        { gName = show dow ++ " " ++ show time,
          gDayOfWeek = dow,
          gStartTime = time
        }

actualStart :: Bool -> Available -> Time
actualStart isFacilitator a =
  availStartTime a
    + if isFacilitator
      then 100
      else 0

actualEnd :: Bool -> Available -> Time
actualEnd isFacilitator a =
  availEndTime a
    - if isFacilitator
      then 100
      else 0

canMeet :: Bool -> Time -> Available -> Bool
canMeet isFacilitator t a =
  t >= actualStart isFacilitator a
    && t < actualEnd isFacilitator a - 200

-- Given a list of participants, determine the list of "pair ups" -- either
-- participants with each other, or with a stated group.
pairings :: (Participant -> [String]) -> [Participant] -> [(Int, Int)]
pairings accessor =
  nub
    . g
    . foldr f Map.empty
    . zipWith
      (\pi i -> Map.fromList (map (,[pi]) (pName i : accessor i)))
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
  [Group] ->
  [Participant] ->
  Solution s SWord8 ->
  SBool
isValid maxGroupSize g p s =
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
                      .&& participants gi .<= fromIntegral maxGroupSize
                      .&& facilitators gi .>= 2
                      .&& blackFacilitators gi .>= 1
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
    -- TODO: Ensure total facilitator skill level is above a threshold
    -- TODO: Ensure there are not too many facilitator assistants
    -- TODO: Facilitators and assistants can be in multiple sessions

    eachParticipant Participant {..} x Group {..} gi =
      fromBool
        ( gDayOfWeek
            `elem` map
              availDayOfWeek
              pAvailability
            && any
              (canMeet pIsFacilitator gStartTime)
              pAvailability
        )
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

showSchedule :: [Participant] -> [Group] -> Solution s Word8 -> String
showSchedule p g s =
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

scheduleGroups :: Size -> [Participant] -> IO ()
scheduleGroups maxGroupSize p = do
  let g = determineGroups p
  putStrLn "Finding scheduling solution...\n"
  reify (length g, length p) $ \(Proxy :: Proxy s) -> do
    LexicographicResult res <- optimize Lexicographic $ do
      solAssignments <- mkFreeVars (length p)
      solBlackFacilitators <- mkFreeVars (length g)
      solFacilitators <- mkFreeVars (length g)
      solBlackParticipants <- mkFreeVars (length g)
      solParticipants <- mkFreeVars (length g)
      constrain $ isValid maxGroupSize g p Solution {..}
      minimize "number-facilitators" $ foldl' smax 0 solFacilitators
      maximize "balance-participants" $ foldl' smin 0 solBlackParticipants
    case extractModel res :: Maybe (Solution s Word8) of
      Nothing -> error "No model found"
      Just model -> dispSolution g model
  where
    dispSolution :: [Group] -> Solution s Word8 -> IO ()
    dispSolution g model = do
      putStr $ showSchedule p g model
      putStrLn $
        "\nValid: "
          ++ show (isValid maxGroupSize g p (literalize model))
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
c2gSchedule :: FilePath -> IO ()
c2gSchedule _ = undefined

readParticipants :: ByteString -> [Participant]
readParticipants = undefined

main :: IO ()
main = do
  -- print $ pairings pPairWith participants
  -- print $ pairings pDoNotPairWith participants
  scheduleGroups 20 participants
  where
    participants =
      [ Participant
          { pName = "Aaron",
            pIsFacilitator = True,
            pIsBlack = False,
            pAvailability =
              [ Available Thursday 1200 2000,
                Available Friday 1200 2000,
                Available Saturday 1200 2000
              ],
            pPairWith = ["Susan"],
            pDoNotPairWith = [],
            pPrefereredMinGroupSize = Nothing,
            pPrefereredMaxGroupSize = Nothing,
            pFixed = Nothing
          },
        Participant
          { pName = "Regina",
            pIsFacilitator = True,
            pIsBlack = True,
            pAvailability =
              [ Available Thursday 1200 2000,
                Available Friday 1200 2000,
                Available Saturday 1200 2000
              ],
            pPairWith = [],
            pDoNotPairWith = [],
            pPrefereredMinGroupSize = Nothing,
            pPrefereredMaxGroupSize = Nothing,
            pFixed = Nothing
          },
        Participant
          { pName = "John",
            pIsFacilitator = True,
            pIsBlack = False,
            pAvailability =
              [ Available Monday 1200 2000,
                Available Tuesday 1200 2000,
                Available Wednesday 1200 2000,
                Available Thursday 1200 2000
              ],
            pPairWith = [],
            pDoNotPairWith = [],
            pPrefereredMinGroupSize = Nothing,
            pPrefereredMaxGroupSize = Nothing,
            pFixed = Nothing
          },
        Participant
          { pName = "Cherlynn",
            pIsFacilitator = True,
            pIsBlack = True,
            pAvailability =
              [ Available Monday 1200 2000,
                Available Tuesday 1200 2000,
                Available Wednesday 1200 2000
              ],
            pPairWith = [],
            pDoNotPairWith = [],
            pPrefereredMinGroupSize = Nothing,
            pPrefereredMaxGroupSize = Nothing,
            pFixed = Nothing
          },
        Participant
          { pName = "Susan",
            pIsFacilitator = True,
            pIsBlack = False,
            pAvailability =
              [ Available Monday 1200 2000,
                Available Tuesday 1200 2000,
                Available Wednesday 1200 2000,
                Available Thursday 1200 2000,
                Available Friday 1200 2000,
                Available Saturday 1200 2000
              ],
            pPairWith = [],
            pDoNotPairWith = [],
            pPrefereredMinGroupSize = Nothing,
            pPrefereredMaxGroupSize = Nothing,
            pFixed = Nothing
          }
      ]
