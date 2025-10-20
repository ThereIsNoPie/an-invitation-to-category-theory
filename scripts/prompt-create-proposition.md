Analyse _includes/sidebar.html to understand how .lagda.md files should be structured. 

Based on the proposition provided, add a module .lagda.md file to src/propositions. 

After creating a proposition use agda to compile to ensure the proposition is correct.

Avoid the use of levels. Instead just use Set and Set₁ etc.

Ensure to check other definitions in the src/definitions folder. Always prefer a proposition in this folder over a standard library construct.
Ensure to check the src/plumbing folder for tools. Esepcially src/plumbing/ClassicalPostulates.lagda.md which will have the postulates you need to using classical logic. 

Do not overbuild the proposition. Keep it as simple as possible while still adhering to the text.

New modules must be added to src/Everything.agda

Separate the proposition from the proof (i.e. type signature separated from function implementation). Use different codeblocks. Always make sure the type signature compiles before trying to implement the proof.

Prefer function signatures for the propositions rather than modules. 

