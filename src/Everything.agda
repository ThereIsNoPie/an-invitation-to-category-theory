{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Core constructs
import core-constructs.Preorder
import core-constructs.GraphViz

-- Exercises
import exercises.GaloisTheorems

-- Examples
import examples.ApplesAndBuckets
import examples.MeetExample
import examples.SimplePreorder
import examples.VisualizeDiamond
