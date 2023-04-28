{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import Data.SBV

-- | A solution is a sequence of group assignments for each participant
type Solution = [SWord8]

isValid :: [Group] -> [Participant] -> Solution -> SBool
isValid _ _ _ = undefined

scheduleGroups :: [Group] -> [Participant] -> IO ()
scheduleGroups _ _ = undefined

-- Given a CSV file of the proper schedule, generate and display an updated
-- version of that CSV file which assigns participants to groups.
c2gSchedule :: FilePath -> IO ()
c2gSchedule _ = undefined

main :: IO ()
main = undefined
