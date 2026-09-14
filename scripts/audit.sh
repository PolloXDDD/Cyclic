#!/usr/bin/env bash
set -euo pipefail

# Reject proof escape-hatch declarations/usages in project Lean sources.
if grep -RInE --include='*.lean' '^[[:space:]]*(axiom|constant|sorry|admit)([[:space:]]|$)' MillenniumSuite MillenniumSuite.lean; then
  echo "ERROR: prohibited proof escape hatch found" >&2
  exit 1
fi

lake build
