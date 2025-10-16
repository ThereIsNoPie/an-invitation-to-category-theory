module core-constructs.GraphViz where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Product using (_×_; _,_)

-- Graph structure: vertices and edges
record Graph : Set₁ where
  field
    Vertex : Set
    Edge   : Vertex → Vertex → Set  -- base edges only

-- Helper to build a string from a list of strings
joinStrings : String → List String → String
joinStrings sep [] = ""
joinStrings sep (x ∷ []) = x
joinStrings sep (x ∷ xs) = x ++ sep ++ joinStrings sep xs

-- Configuration for visualization
record GraphVizConfig (V : Set) : Set where
  field
    showVertex : V → String
    vertices : List V
    edges : List (V × V)

-- Generate DOT format for Graphviz
-- You can paste the output into https://dreampuf.github.io/GraphvizOnline/
-- or use the 'dot' command-line tool
graphToDot : {V : Set} → GraphVizConfig V → String
graphToDot config =
  "digraph G {\n" ++
  "  rankdir=TB;\n" ++
  "  node [shape=circle];\n\n" ++
  vertexDecls ++
  "\n" ++
  edgeDecls ++
  "}\n"
  where
    open GraphVizConfig config

    -- Declare all vertices
    vertexDecls : String
    vertexDecls = joinStrings "\n"
      (foldr (λ v acc → ("  " ++ showVertex v ++ ";") ∷ acc) [] vertices)

    -- Declare all edges
    edgeDecls : String
    edgeDecls = joinStrings "\n"
      (foldr (λ { (v1 , v2) acc →
        ("  " ++ showVertex v1 ++ " -> " ++ showVertex v2 ++ ";") ∷ acc
      }) [] edges)

-- Generate simple text representation
graphToText : {V : Set} → GraphVizConfig V → String
graphToText config =
  "Graph:\n" ++
  "Vertices: " ++ joinStrings ", " (foldr (λ v acc → showVertex v ∷ acc) [] vertices) ++ "\n" ++
  "Edges:\n" ++ edgeList
  where
    open GraphVizConfig config

    edgeList : String
    edgeList = joinStrings "\n"
      (foldr (λ { (v1 , v2) acc →
        ("  " ++ showVertex v1 ++ " → " ++ showVertex v2) ∷ acc
      }) [] edges)
