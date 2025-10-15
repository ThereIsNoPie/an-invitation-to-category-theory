# Guide: Embedding Clickable Agda Snippets

This guide shows you how to embed clickable Agda code snippets from the generated HTML into other webpages.

## How Agda HTML Works

Agda generates HTML with:
- All code wrapped in `<pre class="Agda">...</pre>`
- Identifiers as `<a>` tags with `href` links to definitions
- CSS classes for syntax highlighting (`.Keyword`, `.Function`, `.Datatype`, etc.)
- Unique `id` attributes for anchor linking

## Method 1: Direct HTML Snippet Extraction

### Step 1: Find Your Code in the Generated HTML

Open the generated HTML file (e.g., `docs/examples.ApplesAndBuckets.html`) and find the code you want to embed. For example, the adjunction type signature:

```html
<a id="ApplesAndBucketsTheorem.f!⊆→⊆f*"></a>
<a id="1595" href="examples.ApplesAndBuckets.html#1595" class="Function">f!⊆→⊆f*</a>
<a id="1603" class="Symbol">:</a>
<a id="1605" class="Symbol">∀</a>
<a id="1607" class="Symbol">{</a>
<a id="1608" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a>
<a id="1611" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a>
<a id="1613" class="Symbol">}</a>
<a id="1615" class="Symbol">→</a>
<a id="1617" href="examples.ApplesAndBuckets.html#1096" class="Function">f!</a>
<a id="1620" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a>
<a id="1623" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a>
<a id="1625" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a>
<a id="1628" class="Symbol">→</a>
<a id="1630" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a>
<a id="1633" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a>
<a id="1635" href="examples.ApplesAndBuckets.html#907" class="Function">f*</a>
<a id="1638" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a>
```

### Step 2: Wrap in Code Block

Wrap the snippet in `<pre class="Agda">...</pre>`:

```html
<pre class="Agda"><a id="1595" href="examples.ApplesAndBuckets.html#1595" class="Function">f!⊆→⊆f*</a> <a id="1603" class="Symbol">:</a> <a id="1605" class="Symbol">∀</a> <a id="1607" class="Symbol">{</a><a id="1608" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1611" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a><a id="1613" class="Symbol">}</a> <a id="1615" class="Symbol">→</a> <a id="1617" href="examples.ApplesAndBuckets.html#1096" class="Function">f!</a> <a id="1620" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1623" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a id="1625" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a> <a id="1628" class="Symbol">→</a> <a id="1630" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1633" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a id="1635" href="examples.ApplesAndBuckets.html#907" class="Function">f*</a> <a id="1638" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a></pre>
```

### Step 3: Include in Your Page

```html
<!DOCTYPE html>
<html>
<head>
    <link rel="stylesheet" href="Agda.css">
</head>
<body>
    <h2>Example: Adjunction</h2>
    <p>The first adjunction states that for all subsets A' and B':</p>

    <pre class="Agda"><a id="1595" href="examples.ApplesAndBuckets.html#1595" class="Function">f!⊆→⊆f*</a> <a id="1603" class="Symbol">:</a> <a id="1605" class="Symbol">∀</a> <a id="1607" class="Symbol">{</a><a id="1608" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1611" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a><a id="1613" class="Symbol">}</a> <a id="1615" class="Symbol">→</a> <a id="1617" href="examples.ApplesAndBuckets.html#1096" class="Function">f!</a> <a id="1620" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1623" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a id="1625" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a> <a id="1628" class="Symbol">→</a> <a id="1630" href="examples.ApplesAndBuckets.html#1608" class="Bound">A'</a> <a id="1633" href="examples.ApplesAndBuckets.html#555" class="Function Operator">⊆</a> <a id="1635" href="examples.ApplesAndBuckets.html#907" class="Function">f*</a> <a id="1638" href="examples.ApplesAndBuckets.html#1611" class="Bound">B'</a></pre>

    <p>
        Click on <a href="examples.ApplesAndBuckets.html#1595">f!⊆→⊆f*</a>
        to see the full proof!
    </p>
</body>
</html>
```

## Method 2: Using JavaScript to Load Snippets

For a more maintainable approach, use JavaScript to extract snippets automatically:

```html
<!DOCTYPE html>
<html>
<head>
    <link rel="stylesheet" href="Agda.css">
    <style>
        .code-snippet {
            margin: 1rem 0;
            position: relative;
        }
        .snippet-caption {
            font-size: 0.9rem;
            color: var(--text-secondary);
            margin-top: 0.5rem;
        }
    </style>
</head>
<body>
    <div class="code-snippet"
         data-module="examples.ApplesAndBuckets"
         data-definition="f!⊆→⊆f*"
         data-lines="5">
        <!-- Snippet will be loaded here -->
        <div class="snippet-caption">
            From <a href="examples.ApplesAndBuckets.html#1595">ApplesAndBuckets.agda</a>
        </div>
    </div>

    <script>
        // Load and display code snippet
        document.querySelectorAll('.code-snippet[data-module]').forEach(async (el) => {
            const module = el.getAttribute('data-module');
            const def = el.getAttribute('data-definition');
            const lines = parseInt(el.getAttribute('data-lines') || '10');

            try {
                const response = await fetch(`${module}.html`);
                const html = await response.text();
                const parser = new DOMParser();
                const doc = parser.parseFromString(html, 'text/html');

                // Find the definition by ID or text content
                const anchor = Array.from(doc.querySelectorAll('a.Function'))
                    .find(a => a.textContent === def);

                if (anchor) {
                    // Extract surrounding context (simplified - you'd want more logic)
                    const pre = anchor.closest('pre');
                    const snippet = extractLines(anchor, lines);

                    const preEl = document.createElement('pre');
                    preEl.className = 'Agda';
                    preEl.innerHTML = snippet;
                    el.insertBefore(preEl, el.firstChild);
                }
            } catch (error) {
                console.error('Failed to load snippet:', error);
            }
        });

        function extractLines(startNode, numLines) {
            // Simple extraction - walk DOM and grab content
            // In practice, you'd want smarter line detection
            let html = '';
            let node = startNode;
            let count = 0;

            while (node && count < numLines * 80) {
                html += node.outerHTML || node.textContent;
                node = node.nextSibling;
                count++;
            }

            return html;
        }
    </script>
</body>
</html>
```

## Method 3: Custom Snippet Markers (Recommended)

Add special comments in your Agda code to mark snippets:

```agda
-- SNIPPET-START: adjunction-1
f!⊆→⊆f* : ∀ {A' B'} → f! A' ⊆ B' → A' ⊆ f* B'
f!⊆→⊆f* f!A'⊆B' {a} a∈A' = f!A'⊆B' (a , a∈A' , refl)
-- SNIPPET-END: adjunction-1
```

Then create a build script to extract these:

```python
#!/usr/bin/env python3
import re
from pathlib import Path
from html.parser import HTMLParser

def extract_snippets(html_file, output_dir):
    """Extract marked snippets from Agda HTML"""
    with open(html_file) as f:
        content = f.read()

    # Find snippet markers in comments
    snippet_pattern = r'<a[^>]*class="Comment"[^>]*>-- SNIPPET-START: ([^<]+)</a>(.*?)<a[^>]*class="Comment"[^>]*>-- SNIPPET-END: \1</a>'

    snippets = {}
    for match in re.finditer(snippet_pattern, content, re.DOTALL):
        name = match.group(1).strip()
        snippet_html = match.group(2)
        snippets[name] = snippet_html

    # Save each snippet
    for name, html in snippets.items():
        snippet_file = output_dir / f"{name}.html"
        with open(snippet_file, 'w') as f:
            f.write(f'<pre class="Agda">{html}</pre>')

    return snippets

# Usage
snippets = extract_snippets(
    Path('docs/examples.ApplesAndBuckets.html'),
    Path('docs/snippets')
)
```

## Tips for Embedding

1. **Always include `Agda.css`**: The styling and syntax highlighting depend on it

2. **Preserve the href structure**: Links are relative to the docs directory:
   ```html
   href="examples.ApplesAndBuckets.html#1595"
   ```

3. **Style snippet containers**:
   ```css
   .embedded-snippet {
       border-left: 4px solid var(--agda-function);
       padding-left: 1rem;
       margin: 1.5rem 0;
   }
   ```

4. **Add context**:
   ```html
   <div class="embedded-snippet">
       <h4>Adjunction 1: f! ⊣ f*</h4>
       <pre class="Agda"><!-- snippet here --></pre>
       <p class="snippet-link">
           View full module:
           <a href="examples.ApplesAndBuckets.html">ApplesAndBuckets.agda</a>
       </p>
   </div>
   ```

5. **Handle Unicode**: Make sure your HTML has `<meta charset="utf-8">` to display symbols like `∀`, `→`, `⊆` correctly

## Example: Full Integration

See the updated `site-assets/index.html` for a working example of embedded snippets!
