#!/bin/bash
# Clean all build artifacts

echo "Cleaning build artifacts..."

# Remove Jekyll build outputs
rm -rf _site .jekyll-cache

# Remove Agda build cache
rm -rf _build

# Remove generated documentation
rm -rf docs

echo "✓ Clean complete!"
echo ""
echo "Build artifacts removed:"
echo "  - _site/         (Jekyll output)"
echo "  - .jekyll-cache/ (Jekyll cache)"
echo "  - _build/        (Agda cache)"
echo "  - docs/          (Generated HTML)"
echo ""
echo "To rebuild: ./build-local.sh"
