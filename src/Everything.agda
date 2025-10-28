{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Plumbing
import plumbing.ClassicalPostulates
import plumbing.EquationalReasoning

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

-- Chapter 2 Definitions
import definitions.chapter2.SymmetricMonoidalPreorder

-- Propositions
import propositions.AdjointFunctorTheorem
import propositions.AdjointsPreserveMeetsJoins
import propositions.GaloisUnitCounit
import propositions.MonotoneIdentityComposition
import propositions.MonotoneUpperSetCorrespondence
import propositions.PartitionEquivalenceCorrespondence
import propositions.SubsetMeetJoinMonotonicity

-- Exercises
import exercises.GaloisGivesClosure
import exercises.ClosureAdjunctionExample

-- Chapter 2 Exercises
import exercises.chapter2.IntegersWithMultiplication

-- Examples
import examples.AdjunctionFromClosure
import examples.ApplesAndBuckets
import examples.ComputationAsRewriting
import examples.ModalOperators

-- Chapter 2 Examples
import examples.chapter2.IntegersWithAddition
import examples.chapter2.CommutativeMonoidAsSymmetricMonoidalPreorder

-- Non-textbook
import non-textbook.GraphViz
import non-textbook.MeetExample
import non-textbook.SimplePreorder
import non-textbook.VisualizeDiamond