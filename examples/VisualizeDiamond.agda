{-# OPTIONS --guardedness #-}

module VisualizeDiamond where

open import SimplePreorder
open import IO
open import Data.String using (String)
open import Data.Unit.Polymorphic using (⊤)

main : Main
main = run (putStrLn diamondDot)
