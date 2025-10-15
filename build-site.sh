#!/bin/bash
# Bash script to generate HTML from Agda files
# Usage: ./build-site.sh

set -e

echo "Building Agda HTML documentation..."

# Check if docs directory exists
if [ ! -d "docs" ]; then
    mkdir -p docs
fi

# Generate HTML using Agda's built-in HTML generator
echo "Generating HTML from Agda files..."
agda --html --html-dir=docs --html-highlight=auto src/Everything.agda

echo "HTML generation completed successfully!"

# Copy custom CSS and assets
if [ -d "site-assets" ]; then
    echo "Copying custom assets..."
    cp -r site-assets/* docs/
fi

echo ""
echo "Site generated in docs/ directory"
echo "Open docs/Everything.html in your browser to view the site"
