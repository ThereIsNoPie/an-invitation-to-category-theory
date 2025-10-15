# Graph Visualization Guide

This document explains how to visualize Agda graphs using the provided visualization tools.

## Overview

The project includes a GraphViz module that allows you to generate visual representations of graphs defined in Agda. The visualization is output in DOT format (Graphviz), which can be viewed in various ways.

## Quick Start

To visualize the diamond graph example, run the visualization script from the project root:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/visualize-simple.ps1
```

## What the Script Does

The visualization script performs the following steps:

1. **Compiles the Agda module** - Converts the Agda code to Haskell and then to a native executable (.exe)
2. **Runs the executable** - Executes the compiled program which outputs DOT format text
3. **Saves DOT file** - Saves the output to `examples/diamond.dot`
4. **Generates SVG** (optional) - If Graphviz is installed, converts the DOT file to SVG format
5. **Opens in VS Code** - Opens the resulting visualization file

## Understanding the Output Files

### MAlonzo Directory
When Agda compiles your code with `--compile`, it:
- Translates Agda code to Haskell (stored in `MAlonzo/`)
- Uses GHC to compile the Haskell to a native executable

The `MAlonzo/` directory contains generated Haskell code and is automatically created during compilation. It's git-ignored as it's a build artifact.

### Executable (.exe)
The compiled Agda program (e.g., `VisualizeDiamond.exe`) runs the `main` function defined in the Agda module, which outputs the graph in DOT format.

### DOT File (.dot)
DOT is a graph description language used by Graphviz. The `.dot` file contains a textual representation of your graph structure.

You can view DOT files online at: https://dreampuf.github.io/GraphvizOnline/

### SVG File (.svg)
If Graphviz is installed on your system, the script automatically converts the DOT file to SVG format, which can be viewed in VS Code or any web browser.

## Installing Graphviz (Optional)

For automatic SVG generation, install Graphviz:
- **Windows**: Download from https://graphviz.org/download/
- **Linux**: `sudo apt install graphviz` (Ubuntu/Debian) or equivalent
- **macOS**: `brew install graphviz`

After installation, make sure the `dot` command is available in your PATH.

## Project Structure

```
.
├── GraphViz.agda              # Graph visualization library
├── Preorder.agda              # Preorder definitions
├── examples/                  # Example Agda files
│   ├── SimplePreorder.agda    # Diamond graph example
│   ├── VisualizeDiamond.agda  # Executable visualization module
│   └── diamond.dot            # Generated visualization (git-ignored)
└── scripts/
    └── visualize-simple.ps1   # Visualization script
```

## Creating Your Own Visualizations

To visualize your own graph:

1. Define your graph in Agda using the `Graph` record from `GraphViz.agda`
2. Create a `GraphVizConfig` with:
   - `showVertex`: Function to convert vertices to strings
   - `vertices`: List of all vertices
   - `edges`: List of all edges as pairs
3. Use `graphToDot` to generate DOT format
4. Create an executable module similar to `VisualizeDiamond.agda`

### Example

```agda
open import GraphViz
open import Data.String using (String)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

-- Define your graph configuration
myGraphConfig : GraphVizConfig MyVertexType
myGraphConfig = record
  { showVertex = myShowFunction
  ; vertices = myVertexList
  ; edges = myEdgeList
  }

-- Generate DOT output
myGraphDot : String
myGraphDot = graphToDot myGraphConfig
```

## Troubleshooting

### "Agda compilation failed"
- Ensure Agda is installed and available in your PATH
- Check that all module dependencies are present
- Run `agda --version` to verify installation

### "Module not found" errors
- The script includes both the current directory and parent directory in the module search path
- Ensure you're running the script from the project root

### Script execution policy errors
Windows may block script execution by default. Use:
```powershell
powershell -ExecutionPolicy Bypass -File scripts/visualize-simple.ps1
```

Or permanently set the execution policy (requires admin):
```powershell
Set-ExecutionPolicy RemoteSigned
```

## Additional Resources

- [Graphviz Documentation](https://graphviz.org/documentation/)
- [Agda Documentation](https://agda.readthedocs.io/)
- [Online Graphviz Viewer](https://dreampuf.github.io/GraphvizOnline/)
