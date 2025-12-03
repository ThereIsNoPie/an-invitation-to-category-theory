Analyse _includes/sidebar.html to understand how .lagda.md files should be structured. 

Based on the proposition provided, add a module .lagda.md file to src/propositions. 

After creating a proposition use agda to compile to ensure the proposition is correct.

Avoid the use of levels. Instead just use Set and Set₁ etc.

Ensure to check other definitions in the src/definitions folder. Always prefer a proposition in this folder over a standard library construct.
Ensure to check the src/plumbing folder for tools. Esepcially src/plumbing/ClassicalPostulates.lagda.md which will have the postulates you need to using classical logic. 

Do not overbuild the proposition. Keep it as simple as possible while still adhering to the text.

New modules must be added to src/Everything.agda

Separate the proposition from the proof (i.e. type signature separated from function implementation). Use different codeblocks. Always make sure the type signature compiles before trying to implement the proof.

If a proof contains many steps that are logical to differentiate between, ensure that you separate the proposition from the proof from each step.

Prefer function signatures for the propositions rather than modules. 



```
Theorem 2.32. There is a one-to-one correspondence between preorders and Bool-
categories.
```

Context

```
Our colleague Peter Gates has called category theory “a primordial ooze,” because so
much of it can be defined in terms of other parts of it. There is nowhere to rightly call
the beginning, because that beginning can be defined in terms of something else. So be
it; this is part of the fun.

Here we find ourselves in the ooze, because we are saying that preorders are the same
as Bool-categories, whereas Bool is itself a preorder. “So then Bool is like . . . enriched
in itself?” Yes, every preorder, including Bool, is enriched in Bool, as we shall now see.
Proof of Theorem 2.32. Let’s check that we can construct a preorder from any Bool-
category. Since B = {false, true}, Definition 2.30 says a Bool-category consists of
two things:
(i) a set Ob(X),
(ii) for every x, y ∈ Ob(X) an element X(x, y) ∈ B, i.e. the element X(x, y) is either
true or false.
We will use these two things to begin forming a preorder whose elements are the objects
of X. So let’s call the preorder (X, ≤), and let X := Ob(X). For the ≤ relation, let’s
declare x ≤ y iff X(x, y) = true. We have the makings of a preorder, but for it to
work, the ≤ relation must be reflexive and transitive. Let’s see if we get these from the
properties guaranteed by Definition 2.30:
58 Resource Theories: Monoidal Preorders and Enrichment
(a) for every element x ∈ X we have true ≤ X(x, x),
(b) for every three elements x, y, z ∈ X we have X(x, y) ∧ X(y, z) ≤ X(x, z).
For b ∈ Bool, if true ≤ b then b = true, so the first statement says X(x, x) =
true, which means x ≤ x. For the second statement, one can consult Eq. (2.16). Since
false ≤ b for all b ∈ B, the only way statement (b) has any force is if X(x, y) = true
and X(y, z) = true, in which case it forces X(x, z) = true. This condition exactly
translates as saying that x ≤ y and y ≤ z implies x ≤ z. Thus we have obtained
reflexivity and transitivity from the two axioms of Bool-categories
```