# PowerShell script to visualize the diamond graph using Agda
# This script should be run from the project root directory

Write-Host "Visualizing Diamond Graph..." -ForegroundColor Cyan

# Get the script directory and project root
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$projectRoot = Split-Path -Parent $scriptDir
$examplesDir = Join-Path $projectRoot "examples"
$artifactsDir = Join-Path $scriptDir "visualize-artifacts"

# Ensure artifacts directory exists
if (-not (Test-Path $artifactsDir)) {
    New-Item -ItemType Directory -Path $artifactsDir | Out-Null
}

# Step 1: Compile the Agda module
Write-Host "[1/4] Compiling Agda module..." -ForegroundColor Yellow
Set-Location $examplesDir
agda --compile --compile-dir=$artifactsDir -i. -i.. VisualizeDiamond.agda
if ($LASTEXITCODE -ne 0) {
    Write-Host "Agda compilation failed!" -ForegroundColor Red
    Set-Location $projectRoot
    exit 1
}
Write-Host "Compilation successful" -ForegroundColor Green

# Step 2: Run the compiled executable to generate DOT output
Write-Host "[2/4] Generating DOT format..." -ForegroundColor Yellow
$exePath = Join-Path $artifactsDir "VisualizeDiamond.exe"
$dotOutput = & $exePath
Write-Host "DOT format generated" -ForegroundColor Green

# Step 3: Save DOT output to file
Write-Host "[3/4] Saving to diamond.dot..." -ForegroundColor Yellow
$outputPath = Join-Path $artifactsDir "diamond.dot"
$dotOutput | Out-File -FilePath $outputPath -Encoding utf8
Write-Host "Saved to $outputPath" -ForegroundColor Green

# Step 4: Try to generate SVG using Graphviz
Write-Host "[4/4] Attempting to generate SVG..." -ForegroundColor Yellow
$hasDot = Get-Command dot -ErrorAction SilentlyContinue
if ($hasDot) {
    $svgPath = Join-Path $artifactsDir "diamond.svg"
    dot -Tsvg $outputPath -o $svgPath
    Write-Host "Generated $svgPath" -ForegroundColor Green
    code $svgPath
} else {
    Write-Host "Graphviz not found. Opening DOT file..." -ForegroundColor Yellow
    code $outputPath
}

# Return to project root
Set-Location $projectRoot

Write-Host "Visualization complete!" -ForegroundColor Cyan
Write-Host "All artifacts saved to: $artifactsDir" -ForegroundColor Gray
