Analyse _includes/sidebar.html to understand how .lagda.md files should be structured. 

Based on the definition provided, add a module .lagda.md file to src/definitions. 

After creating a definition use agda to compile to ensure the definition is correct.

Avoid the use of levels. Instead just use Set and Set₁ etc.

Ensure to check other definitions in the definitions folder. Always prefer a definition in this folder over a standard library construct.

Do not overbuild the definition. Keep it as simple as possible while still adhering to the text.

New modules must be added to src/Everything.agda