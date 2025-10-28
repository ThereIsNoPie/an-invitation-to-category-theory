---
layout: default
title: Home
---

<div class="hero" markdown="1">

# An Invitation to Category Theory

Formalized in Agda with clickable, interactive code

</div>

<div class="section" markdown="1">

## Introduction

Advantages of Agda:

* It will tell you **precisely** where you are wrong.
* When you **forget** a definition you can just click on the type signature. 

## Decisions Made for this Website

* I avoided [universe levels](https://agda.readthedocs.io/en/latest/language/universe-levels.html) as much as possible. They make type signatures confusing for beginners.
* I split **type signatures** (i.e. the proposition/problem) from the **function implementation** (i.e. the proof/solution)
* I made some assumptions in [classical postulates]({{ '/docs/plumbing.ClassicalPostulates.html' | relative_url }}). This avoids using [Cubical Agda](https://agda.readthedocs.io/en/latest/language/cubical.html) which is not beginner friendly.

In general, I want readers to be able to grasp the concept of the file within 30s of opening it, and then expand sections to go into finer grained details.

## Where to start

Check out [Proposition 1.14]({{ '/docs/propositions.chapter1.PartitionEquivalenceCorrespondence.html' | relative_url }}). Click on the agda code to navigate.

</div>


<footer markdown="1">

Generated with [Agda](https://github.com/agda/agda) • Formalization based on _An Invitation to Applied Category Theory_

[View Original Textbook](http://www.brendanfong.com/fong_spivak_an_invitation.pdf)

[Check Out The Code](https://github.com/ThereIsNoPie/an-invitation-to-category-theory)

</footer>
