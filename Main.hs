{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

-- import Data.Csv

import Control.Exception (assert)
import Data.List (genericLength)
import Data.Maybe (fromMaybe)
import Data.Proxy
import Data.Reflection
import Data.SBV
import Text.Show.Pretty hiding (reify)
import Prelude hiding (pi)

data DayOfWeek = Sun | Mon | Tue | Wed | Thu | Fri | Sat
  deriving (Enum)

mkSymbolicEnumeration ''DayOfWeek

type Hour = Word8

type Size = Word16

data Group = Group
  { gName :: String,
    gDayOfWeek :: DayOfWeek,
    gStartHour :: Hour,
    gMaxSize :: Maybe Size,
    gNote :: [String]
  }
  deriving (Show)

type Rank = Word8

data Available = Available
  { availDayOfWeek :: DayOfWeek,
    availStartHour :: Hour,
    availEndHour :: Hour,
    availRank :: Rank
  }
  deriving (Show)

data Participant = Participant
  { pName :: String,
    pIsFacilitator :: Bool,
    pIsBlack :: Bool,
    pAvailability :: [Available],
    pNote :: [String],
    pPrefereredMinGroupSize :: Maybe Size,
    pPrefereredMaxGroupSize :: Maybe Size,
    pFixed :: Bool
  }
  deriving (Show)

-- | A solution is a sequence of group assignments for each participant
data Solution s v = Solution
  { solAssignments :: [v], -- participants -> group number
    solBlackFacilitators :: [v], -- groups -> black facilitator count
    solFacilitators :: [v], -- groups -> total facilitator count
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
          (take glen (drop (glen + glen + plen) a)),
        bs
      )

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
    -- Every participant assignment is to an applicable group
    sAnd
      ( zipWith
          ( \pi x ->
              sAnd
                ( zipWith
                    ( \gi grp ->
                        gi ./= x
                          .|| fromBool
                            ( gDayOfWeek grp
                                `elem` map
                                  availDayOfWeek
                                  (pAvailability (p !! pi))
                            )
                    )
                    [0 ..]
                    g
                )
                .&& x .>= 0
                .&& x .< genericLength g
          )
          [0 ..]
          (solAssignments s)
      )
      -- Every group has at least one black facilitator
      .&& sAnd
        ( zipWith
            ( \gi x ->
                x
                  .== sum
                    ( zipWith
                        ( \pi a ->
                            oneIf
                              ( gi .== a
                                  .&& fromBool (pIsFacilitator (p !! pi))
                                  .&& fromBool (pIsBlack (p !! pi))
                              )
                        )
                        [0 ..]
                        (solAssignments s)
                    )
                  .&& x .>= 1
            )
            [0 ..]
            (solBlackFacilitators s)
        )
      -- Every group has at least two facilitators
      .&& sAnd
        ( zipWith
            ( \gi x ->
                x
                  .== sum
                    ( zipWith
                        ( \pi a ->
                            oneIf
                              ( gi .== a
                                  .&& fromBool (pIsFacilitator (p !! pi))
                              )
                        )
                        [0 ..]
                        (solAssignments s)
                    )
                  .&& x .>= 2
            )
            [0 ..]
            (solFacilitators s)
        )
      -- Every group does not exceed its maximum group size
      .&& sAnd
        ( zipWith
            ( \gi x ->
                x
                  .== sum
                    ( map
                        (\a -> oneIf (fromIntegral gi .== a))
                        (solAssignments s)
                    )
                  .&& x
                    .<= fromIntegral
                      ( fromMaybe
                          maxGroupSize
                          (gMaxSize (g !! gi))
                      )
            )
            [0 ..]
            (solParticipants s)
        )

scheduleGroups :: Size -> [Group] -> [Participant] -> IO ()
scheduleGroups maxGroupSize g p = do
  putStrLn "Finding all scheduling solutions.."
  reify (length g, length p) $ \(Proxy :: Proxy s) -> do
    res <- sat $ do
      solAssignments <- mkFreeVars (length p)
      solBlackFacilitators <- mkFreeVars (length g)
      solFacilitators <- mkFreeVars (length g)
      solParticipants <- mkFreeVars (length g)
      let sol :: Solution s SWord8 = Solution {..}
      constrain $ isValid maxGroupSize g p sol
    -- putStrLn $ "satisfiability = " ++ show res
    case extractModel res :: Maybe (Solution s Word8) of
      Nothing -> error "No model found"
      Just model -> dispSolution model
  where
    dispSolution :: Solution s Word8 -> IO ()
    dispSolution model = do
      pPrint model
      putStrLn $
        " (Valid: "
          ++ show (isValid maxGroupSize g p (literalize model))
          ++ ")"
      where
        literalize s =
          s
            { solAssignments = map literal (solAssignments s),
              solBlackFacilitators = map literal (solBlackFacilitators s),
              solFacilitators = map literal (solFacilitators s),
              solParticipants = map literal (solParticipants s)
            }

-- Given a CSV file of the proper schedule, generate and display an updated
-- version of that CSV file which assigns participants to groups.
c2gSchedule :: FilePath -> IO ()
c2gSchedule _ = undefined

main :: IO ()
main = do
  scheduleGroups
    20
    [ Group
        { gName = "Mon7p",
          gDayOfWeek = Mon,
          gStartHour = 19,
          gMaxSize = Nothing,
          gNote = []
        },
      Group
        { gName = "Thu4p",
          gDayOfWeek = Thu,
          gStartHour = 16,
          gMaxSize = Nothing,
          gNote = []
        }
    ]
    [ Participant
        { pName = "Aaron",
          pIsFacilitator = True,
          pIsBlack = False,
          pAvailability =
            [ Available Thu 12 20 0,
              Available Fri 12 20 0,
              Available Sat 12 20 0
            ],
          pNote = [],
          pPrefereredMinGroupSize = Nothing,
          pPrefereredMaxGroupSize = Nothing,
          pFixed = False
        },
      Participant
        { pName = "Regina",
          pIsFacilitator = True,
          pIsBlack = True,
          pAvailability =
            [ Available Thu 12 20 0,
              Available Fri 12 20 0,
              Available Sat 12 20 0
            ],
          pNote = [],
          pPrefereredMinGroupSize = Nothing,
          pPrefereredMaxGroupSize = Nothing,
          pFixed = False
        },
      Participant
        { pName = "John",
          pIsFacilitator = True,
          pIsBlack = False,
          pAvailability =
            [ Available Mon 12 20 0,
              Available Tue 12 20 0,
              Available Wed 12 20 0
            ],
          pNote = [],
          pPrefereredMinGroupSize = Nothing,
          pPrefereredMaxGroupSize = Nothing,
          pFixed = False
        },
      Participant
        { pName = "Cherlynn",
          pIsFacilitator = True,
          pIsBlack = True,
          pAvailability =
            [ Available Mon 12 20 0,
              Available Tue 12 20 0,
              Available Wed 12 20 0
            ],
          pNote = [],
          pPrefereredMinGroupSize = Nothing,
          pPrefereredMaxGroupSize = Nothing,
          pFixed = False
        },
      Participant
        { pName = "Susan",
          pIsFacilitator = True,
          pIsBlack = False,
          pAvailability =
            [ Available Mon 12 20 0,
              Available Tue 12 20 0,
              Available Wed 12 20 0,
              Available Thu 12 20 0,
              Available Fri 12 20 0,
              Available Sat 12 20 0
            ],
          pNote = [],
          pPrefereredMinGroupSize = Nothing,
          pPrefereredMaxGroupSize = Nothing,
          pFixed = False
        }
    ]
