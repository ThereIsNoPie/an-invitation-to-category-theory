---
layout: agda
title: "VisualizeDiamond"
---

```agda
{-# OPTIONS --guardedness #-}

module examples.VisualizeDiamond where

open import examples.SimplePreorder
open import IO
open import Data.String using (String)
open import Data.Unit.Polymorphic using (⊤)

main : Main
main = run (putStrLn diamondDot)
```
