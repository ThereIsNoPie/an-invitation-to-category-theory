{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Core theory
import Preorder
import GraphViz
import MeetExample

-- Examples
import examples.ApplesAndBuckets
import examples.SimplePreorder
import examples.VisualizeDiamond
