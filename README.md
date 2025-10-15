# An Invitation to Category Theory

A formalization of category-theoretic concepts in Agda, focusing on preorders, Galois connections, and adjoint functors. This project features interactive HTML documentation with clickable, syntax-highlighted code similar to [1lab](https://1lab.dev/).

## Features

- ✅ Fully type-checked proofs in Agda
- ✅ Clickable identifiers that link to their definitions
- ✅ Syntax highlighting for better readability
- ✅ Automatic deployment to GitHub Pages
- ✅ Dark mode support
- ✅ Responsive design

## Contents

### Core Theory

- **src/Preorder.agda** - Defines preorders, monotonic functions, Galois connections, and proves key theorems including the Adjoint Functor Theorem for preorders (Theorem 1.108)
- **src/GraphViz.agda** - Utilities for visualizing preorders and graphs using GraphViz DOT format
- **src/MeetExample.agda** - Demonstrates meet and join operations in preorders

### Examples

- **src/examples/ApplesAndBuckets.agda** - Example 1.109: Demonstrates three adjoint functors induced by a function
- **src/examples/SimplePreorder.agda** - A concrete example of a diamond-shaped preorder with 4 elements
- **src/examples/VisualizeDiamond.agda** - Executable module for generating GraphViz visualizations

## Key Theorems

- **Proposition 1.101**: Equivalence between Galois connections and unit/counit conditions
- **Proposition 1.104**: Right adjoints preserve meets, left adjoints preserve joins
- **Theorem 1.108**: Adjoint Functor Theorem for Preorders
- **Example 1.109**: Apples and Buckets - three adjoint functors induced by a function

## Building Locally

### Prerequisites

- [Agda](https://agda.readthedocs.io/en/latest/getting-started/installation.html) (tested with version 2.6.3+)
- [Agda standard library](https://github.com/agda/agda-stdlib)

### Generate HTML

```bash
# Generate HTML documentation
agda --html --html-dir=docs --html-highlight=auto src/Everything.agda

# Copy custom assets
cp site-assets/Agda.css docs/
cp site-assets/index.html docs/

# Open in browser
open docs/index.html  # macOS
# or
start docs/index.html  # Windows
# or
xdg-open docs/index.html  # Linux
```

Or use the provided script (Windows):
```powershell
.\build-site.ps1
```

Or (Linux/macOS):
```bash
chmod +x build-site.sh
./build-site.sh
```

## Deploying to GitHub Pages

This project is configured to automatically deploy to GitHub Pages using GitHub Actions.

### Setup Instructions

1. **Enable GitHub Pages**:
   - Go to your repository settings
   - Navigate to **Pages** in the sidebar
   - Under **Source**, select **GitHub Actions**

2. **Push to main branch**:
   ```bash
   git add .
   git commit -m "Add Agda documentation site"
   git push origin main
   ```

3. **Wait for deployment**:
   - Go to the **Actions** tab in your repository
   - Wait for the "Build and Deploy Agda Documentation" workflow to complete
   - Your site will be available at `https://<username>.github.io/<repository-name>/`

### Manual Deployment

If you prefer to deploy manually:

1. Generate the HTML locally (see above)
2. Push the `docs/` directory to GitHub
3. Enable GitHub Pages from the `docs/` folder in repository settings

## Project Structure

```
.
├── .github/
│   └── workflows/
│       └── deploy.yml              # GitHub Actions workflow
├── src/                            # All Agda source code
│   ├── examples/                   # Example Agda modules
│   │   ├── ApplesAndBuckets.agda
│   │   ├── SimplePreorder.agda
│   │   └── VisualizeDiamond.agda
│   ├── Everything.agda             # Main entry point for HTML generation
│   ├── Preorder.agda              # Core theory
│   ├── GraphViz.agda              # Visualization utilities
│   └── MeetExample.agda           # Meet/join examples
├── site-assets/                    # Custom CSS and landing page
│   ├── Agda.css                   # Custom styling (1lab-inspired)
│   └── index.html                 # Landing page
├── docs/                           # Generated HTML (git-ignored)
├── category-theory.agda-lib       # Agda library file
├── build-site.ps1                 # Build script (Windows)
├── build-site.sh                  # Build script (Linux/macOS)
└── README.md                      # This file
```

## Customization

### Styling

Edit `site-assets/Agda.css` to customize the appearance. The CSS includes:
- Color scheme variables for easy theming
- Dark mode support via `@media (prefers-color-scheme: dark)`
- Responsive design for mobile devices

### Landing Page

Edit `site-assets/index.html` to customize the landing page content.

### Adding New Modules

1. Create your new `.agda` file in `src/`
2. Add it to `src/Everything.agda`:
   ```agda
   import YourNewModule
   ```
3. Regenerate the HTML

### Embedding Code Snippets

Want to embed clickable Agda code snippets into your own webpages? See [EMBEDDING-GUIDE.md](./EMBEDDING-GUIDE.md) for detailed instructions on how to:

- Extract snippets from generated HTML
- Preserve clickable links to definitions
- Use JavaScript to dynamically load snippets
- Style embedded code examples

**Quick example:**
```html
<link rel="stylesheet" href="Agda.css">
<pre class="Agda"><a href="examples.ApplesAndBuckets.html#1595" class="Function">f!⊆→⊆f*</a> <a class="Symbol">:</a> <a class="Symbol">∀</a> <a class="Symbol">{</a><a href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a><a class="Symbol">}</a> <a class="Symbol">→</a> <a href="examples.ApplesAndBuckets.html#1096" class="Function">f!</a> <a href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a> <a class="Symbol">→</a> <a href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a href="examples.ApplesAndBuckets.html#907" class="Function">f*</a> <a href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a></pre>
```

Check out the live example on the [landing page](docs/index.html)!

## Viewing the Site

After deployment, visit your GitHub Pages site at:
```
https://<your-username>.github.io/an-invitation-to-category-theory/
```

## Credits

- Formalization based on [*An Invitation to Applied Category Theory*](https://www.cambridge.org/core/books/an-invitation-to-applied-category-theory/D4C5E5C2B019B2F9B8CE9A4E9E84D6BC) by Brendan Fong and David I. Spivak
- Styling inspired by [1lab](https://1lab.dev/)
- Built with [Agda](https://github.com/agda/agda)

## License

[Add your license here]
