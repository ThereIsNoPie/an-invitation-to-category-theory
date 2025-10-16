{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Definitions
import definitions.ClosureOperator
import definitions.Composition
import definitions.EquivalenceRelation
import definitions.Function
import definitions.GaloisConnection
import definitions.Graph
import definitions.Isomorphism
import definitions.MeetJoin
import definitions.MonotoneMap
import definitions.Partition
import definitions.Preorder
import definitions.Quotient
import definitions.Relation

-- Exercises
import exercises.GaloisTheorems

-- Examples
import examples.ApplesAndBuckets
import examples.PreciseAndForgetful

-- Non-textbook
import non-textbook.GraphViz
import non-textbook.MeetExample
import non-textbook.SimplePreorder
import non-textbook.VisualizeDiamond