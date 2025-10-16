{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Definitions
import definitions.EquivalenceRelation
import definitions.Partition
import definitions.Preorder
import definitions.Relation

-- Exercises
import exercises.GaloisTheorems

-- Examples
import examples.ApplesAndBuckets

-- Non-textbook
import non-textbook.GraphViz
import non-textbook.MeetExample
import non-textbook.SimplePreorder
import non-textbook.VisualizeDiamond