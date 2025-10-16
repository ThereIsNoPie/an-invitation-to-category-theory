#!/bin/bash
# Complete local build script for Agda documentation with Jekyll
# This mirrors what GitHub Actions does automatically

set -e  # Exit on any error

echo "════════════════════════════════════════════════════════════════"
echo "  Building Agda Documentation Site Locally"
echo "════════════════════════════════════════════════════════════════"
echo ""

# Step 1: Generate HTML from Agda
echo "Step 1/5: Generating HTML documentation from Agda..."
echo "Running: agda --html --html-dir=docs --html-highlight=auto src/Everything.agda"
agda --html --html-dir=docs --html-highlight=auto src/Everything.agda
echo "✓ Agda HTML generation complete"
echo ""

# Step 2: Copy custom CSS
echo "Step 2/4: Copying custom CSS and assets..."
if [ -d "site-assets" ]; then
    cp -r site-assets/* docs/
    echo "✓ Custom assets copied to docs/"
else
    echo "⚠ Warning: site-assets directory not found"
fi
echo ""

# Step 3: Build with Jekyll
echo "Step 3/4: Building site with Jekyll..."
if command -v bundle &> /dev/null; then
    bundle exec jekyll build
    echo "✓ Jekyll build complete"
else
    echo "✗ Error: bundle not found. Please install Ruby and run 'bundle install'"
    exit 1
fi
echo ""

# Step 4: Report results
echo "Step 4/4: Build summary"
echo "────────────────────────────────────────────────────────────────"
echo "✓ Site built successfully!"
echo ""
echo "Output directory: _site/"
echo ""

# Count files
html_count=$(find _site/docs -name "*.html" 2>/dev/null | wc -l)
echo "Generated files:"
echo "  - HTML files in docs/: $html_count"
echo "  - Homepage: _site/index.html"
echo ""

echo "════════════════════════════════════════════════════════════════"
echo "  Next Steps"
echo "════════════════════════════════════════════════════════════════"
echo ""
echo "To preview your site locally:"
echo "  $ bundle exec jekyll serve"
echo ""
echo "Then open: http://localhost:4000"
echo ""
echo "To clean up build artifacts:"
echo "  $ rm -rf _site .jekyll-cache"
echo ""
