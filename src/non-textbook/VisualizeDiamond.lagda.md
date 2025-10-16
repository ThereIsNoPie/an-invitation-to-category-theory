---
layout: agda
title: "Visualize Diamond"
section: "Not In Textbook"
chapter: 1
number: 4
---

```agda
{-# OPTIONS --guardedness #-}

module non-textbook.VisualizeDiamond where

open import non-textbook.SimplePreorder
open import IO
open import Data.String using (String)
open import Data.Unit.Polymorphic using (⊤)

main : Main
main = run (putStrLn diamondDot)
```
