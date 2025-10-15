# PowerShell script to generate HTML from Agda files
# Usage: .\build-site.ps1

Write-Host "Building Agda HTML documentation..." -ForegroundColor Green

# Check if docs directory exists
if (-not (Test-Path "docs")) {
    New-Item -ItemType Directory -Path "docs" | Out-Null
}

# Generate HTML using Agda's built-in HTML generator
Write-Host "Generating HTML from Agda files..."
agda --html --html-dir=docs --html-highlight=auto src/Everything.agda

if ($LASTEXITCODE -eq 0) {
    Write-Host "HTML generation completed successfully!" -ForegroundColor Green

    # Copy custom CSS and assets
    if (Test-Path "site-assets") {
        Write-Host "Copying custom assets..."
        Copy-Item -Path "site-assets\*" -Destination "docs\" -Recurse -Force
    }

    Write-Host ""
    Write-Host "Site generated in docs/ directory" -ForegroundColor Cyan
    Write-Host "Open docs\Everything.html in your browser to view the site" -ForegroundColor Cyan
} else {
    Write-Host "Error generating HTML. Please check Agda compilation errors." -ForegroundColor Red
    exit 1
}
