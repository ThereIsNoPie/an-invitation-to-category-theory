{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Plumbing
import plumbing.ClassicalPostulates
import plumbing.EquationalReasoning

-- Chapter 1 Definitions
import definitions.chapter1.ClosureOperator
import definitions.chapter1.Composition
import definitions.chapter1.EquivalenceRelation
import definitions.chapter1.Function
import definitions.chapter1.GaloisConnection
import definitions.chapter1.Graph
import definitions.chapter1.Isomorphism
import definitions.chapter1.MeetJoin
import definitions.chapter1.MonotoneMap
import definitions.chapter1.Partition
import definitions.chapter1.Preorder
import definitions.chapter1.Quotient
import definitions.chapter1.Relation

-- Chapter 2 Definitions
import definitions.chapter2.SymmetricMonoidalPreorder

-- Chapter 1 Propositions
import propositions.chapter1.AdjointFunctorTheorem
import propositions.chapter1.AdjointsPreserveMeetsJoins
import propositions.chapter1.GaloisUnitCounit
import propositions.chapter1.MonotoneIdentityComposition
import propositions.chapter1.MonotoneUpperSetCorrespondence
import propositions.chapter1.PartitionEquivalenceCorrespondence
import propositions.chapter1.SubsetMeetJoinMonotonicity

-- Chapter 1 Exercises
import exercises.chapter1.GaloisGivesClosure
import exercises.chapter1.ClosureAdjunctionExample

-- Chapter 2 Exercises
import exercises.chapter2.IntegersWithMultiplication
import exercises.chapter2.WiringDiagramProof
import exercises.chapter2.ChemicalReactions
import exercises.chapter2.PowerSetIntersection 

-- Chapter 1 Examples
import examples.chapter1.AdjunctionFromClosure
import examples.chapter1.ApplesAndBuckets
import examples.chapter1.ComputationAsRewriting
import examples.chapter1.ModalOperators

-- Chapter 2 Examples
import examples.chapter2.IntegersWithAddition
import examples.chapter2.CommutativeMonoidAsSymmetricMonoidalPreorder
import examples.chapter2.Cost

-- Non-textbook
import non-textbook.GraphViz
import non-textbook.MeetExample
import non-textbook.SimplePreorder
import non-textbook.VisualizeDiamond