{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Core theory
import Preorder
import GraphViz
import MeetExample

-- Examples (includes both .agda and .lagda.md files)
import examples.ApplesAndBuckets  -- Now a .lagda.md file!
import examples.SimplePreorder
import examples.VisualizeDiamond
