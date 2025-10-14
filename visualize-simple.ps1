# PowerShell script to visualize the diamond graph using Agda

Write-Host "Visualizing Diamond Graph..." -ForegroundColor Cyan

# Step 1: Compile the Agda module
Write-Host "[1/4] Compiling Agda module..." -ForegroundColor Yellow
agda --compile --compile-dir=. VisualizeDiamond.agda
if ($LASTEXITCODE -ne 0) {
    Write-Host "Agda compilation failed!" -ForegroundColor Red
    exit 1
}
Write-Host "Compilation successful" -ForegroundColor Green

# Step 2: Run the compiled executable to generate DOT output
Write-Host "[2/4] Generating DOT format..." -ForegroundColor Yellow
$dotOutput = & ".\VisualizeDiamond.exe"
Write-Host "DOT format generated" -ForegroundColor Green

# Step 3: Save DOT output to file
Write-Host "[3/4] Saving to diamond.dot..." -ForegroundColor Yellow
$dotOutput | Out-File -FilePath "diamond.dot" -Encoding utf8
Write-Host "Saved to diamond.dot" -ForegroundColor Green

# Step 4: Try to generate SVG using Graphviz
Write-Host "[4/4] Attempting to generate SVG..." -ForegroundColor Yellow
$hasDot = Get-Command dot -ErrorAction SilentlyContinue
if ($hasDot) {
    dot -Tsvg diamond.dot -o diamond.svg
    Write-Host "Generated diamond.svg" -ForegroundColor Green
    code diamond.svg
} else {
    Write-Host "Graphviz not found. Opening DOT file..." -ForegroundColor Yellow
    code diamond.dot
}

Write-Host "Visualization complete!" -ForegroundColor Cyan
