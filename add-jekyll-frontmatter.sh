#!/bin/bash
# Add Jekyll front matter to Agda-generated markdown files

for mdfile in docs/*.md; do
  if [ -f "$mdfile" ]; then
    # Check if file already has front matter
    if ! head -n 1 "$mdfile" | grep -q "^---$"; then
      # Extract module name from the file for a title
      filename=$(basename "$mdfile" .md)
      title=$(echo "$filename" | sed 's/\./: /g')

      # Create temporary file with front matter
      {
        echo "---"
        echo "layout: agda"
        echo "title: \"$title\""
        echo "---"
        echo ""
        cat "$mdfile"
      } > "$mdfile.tmp"

      # Replace original file
      mv "$mdfile.tmp" "$mdfile"
      echo "Added front matter to $mdfile"
    fi
  fi
done
