{-# OPTIONS --guardedness #-}

-- Main entry point for HTML generation
-- This file imports all modules to ensure complete HTML generation

module Everything where

-- Plumbing
import plumbing.ClassicalPostulates
import plumbing.EquationalReasoning
import plumbing.Reals

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
import definitions.chapter2.MonoidalMonotone
import definitions.chapter2.VCategory
import definitions.chapter2.MetricSpace
import definitions.chapter2.LawvereMetricSpace
import definitions.chapter2.VFunctor
import definitions.chapter2.VProduct
import definitions.chapter2.MonoidalClosed
import definitions.chapter2.Quantale
import definitions.chapter2.ChangeOfBase

-- Chapter 1 Propositions
import propositions.chapter1.AdjointFunctorTheorem
import propositions.chapter1.AdjointsPreserveMeetsJoins
import propositions.chapter1.GaloisUnitCounit
import propositions.chapter1.MonotoneIdentityComposition
import propositions.chapter1.MonotoneUpperSetCorrespondence
import propositions.chapter1.PartitionEquivalenceCorrespondence
import propositions.chapter1.SubsetMeetJoinMonotonicity

-- Chapter 2 Propositions
import propositions.chapter2.OppositeSymmetricMonoidalPreorder
import propositions.chapter2.PreorderBoolCategoryCorrespondence
import propositions.chapter2.ClosedMonoidalProperties
import propositions.chapter2.JoinsIffMeets

-- Chapter 1 Exercises
import exercises.chapter1.GaloisGivesClosure
import exercises.chapter1.ClosureAdjunctionExample

-- Chapter 2 Exercises
import exercises.chapter2.IntegersWithMultiplication
import exercises.chapter2.WiringDiagramProof
import exercises.chapter2.ChemicalReactions
import exercises.chapter2.PowerSetIntersection
import exercises.chapter2.MonoidalMonotoneBoolToCost
import exercises.chapter2.MonoidalMonotoneCostToBool
import exercises.chapter2.BoolOr
import exercises.chapter2.OppositeDaggerSkeletal
import exercises.chapter2.BoolIsMonoidalClosed
import exercises.chapter2.NMYCategory

-- Chapter 1 Examples
import examples.chapter1.AdjunctionFromClosure
import examples.chapter1.ApplesAndBuckets
import examples.chapter1.ComputationAsRewriting
import examples.chapter1.ModalOperators

-- Chapter 2 Examples
import examples.chapter2.IntegersWithAddition
import examples.chapter2.CommutativeMonoidAsSymmetricMonoidalPreorder
import examples.chapter2.Cost
import examples.chapter2.PreorderAsBoolCategory
import examples.chapter2.RealsAsMetricSpace
import examples.chapter2.BoolAnd
import examples.chapter2.CostToBoolMonotone
import examples.chapter2.BoolFunctorsAreMonotone
import examples.chapter2.CostFunctorsAreLipschitz
import examples.chapter2.CostIsMonoidalClosed
import examples.chapter2.BoolOrNotClosed
import examples.chapter2.CostIsQuantale

-- Non-textbook
import non-textbook.GraphViz
import non-textbook.MeetExample
import non-textbook.SimplePreorder
import non-textbook.VisualizeDiamond