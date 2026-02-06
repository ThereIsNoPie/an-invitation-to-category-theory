#!/bin/bash

INPUT=$(cat)
FILE_PATH=$(echo "$INPUT" | jq -r '.tool_input.file_path // empty')

if [[ "$FILE_PATH" == *.agda ]] || [[ "$FILE_PATH" == *.lagda.md ]]; then
  agda "$FILE_PATH" 2>&1 | head -30
  exit ${PIPESTATUS[0]}
fi

exit 0