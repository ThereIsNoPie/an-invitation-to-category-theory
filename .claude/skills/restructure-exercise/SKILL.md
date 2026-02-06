Restructure an exercise file into problem/solution format.

The file path is: $ARGUMENTS

## Steps

1. **Read the file** completely.

2. **Identify the structure**: Find the module declaration, imports, type signatures, and implementations.

3. **Split into sections**:
   - **Textbook Exercise**: Quote from the textbook with LaTeX math
   - **Agda Setup**: Module declaration, imports, shared definitions
   - **Problem**: Type signatures and any necessary supporting definitions/records in one code block. No postulates or holes — just the signatures. The reader can attempt to implement them.
   - **Solution**: Strategy comment explaining the proof approach, then full implementations in a later code block. Since the file is literate Agda, the type signature in the Problem block and the implementation in the Solution block are in the same module — this compiles naturally.

4. **Compile**: Run `agda` on the restructured file to verify it type-checks.

5. **Report**: Show what changed.

See `src/exercises/chapter2/PowerSetIntersection.lagda.md` for a reference example.
