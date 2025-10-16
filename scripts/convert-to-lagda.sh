#!/bin/bash
# Convert remaining .agda files to .lagda.md

echo "Converting .agda files to .lagda.md..."

# Function to convert a file
convert_file() {
    local agda_file="$1"
    local lagda_file="${agda_file%.agda}.lagda.md"
    local module_name=$(basename "$agda_file" .agda)
    
    echo "Converting $agda_file..."
    
    # Create lagda.md with front matter and wrap code in agda blocks
    {
        echo "---"
        echo "layout: agda"
        echo "title: \"$module_name\""
        echo "---"
        echo ""
        echo '```agda'
        cat "$agda_file"
        echo '```'
    } > "$lagda_file"
    
    # Remove old .agda file
    rm "$agda_file"
}

# Convert exercises
if [ -f "src/exercises/GaloisTheorems.agda" ]; then
    convert_file "src/exercises/GaloisTheorems.agda"
fi

# Convert examples
for file in src/examples/*.agda; do
    [ -f "$file" ] || continue
    convert_file "$file"
done

echo "✓ Conversion complete"
