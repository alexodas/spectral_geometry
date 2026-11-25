#!/usr/bin/env python3
"""Static Palomar packaging checks; not a substitute for Lean / Comparator."""
import json
import pathlib
import sys
root=pathlib.Path(__file__).resolve().parent.parent
errors=[]
for f in sorted(root.rglob("*.lean")):
    if any(p in (".lake", ".git") for p in f.relative_to(root).parts):
        continue
    content=f.read_text(encoding="utf-8")
    if not content.lstrip().startswith("module"):
        errors.append(str(f.relative_to(root))+": missing module header")
    if len(content.splitlines())>10000:
        errors.append(str(f.relative_to(root))+": exceeds 10,000 lines")
for name in (
    "formalization.yaml",
    "palomar/dark-bright/comparator.json",
    "palomar/signed-bright-splitting/comparator.json",
    "palomar/exact-leakage-free-preparation/comparator.json",
    "palomar/signed-bright-splitting/formalization.yaml",
    "palomar/exact-leakage-free-preparation/formalization.yaml",
    "palomar/spectral-protection-during-coordinated-control/comparator.json",
    "palomar/spectral-protection-during-coordinated-control/formalization.yaml",
    "lake-manifest.json",
):
    try: json.loads((root/name).read_text(encoding="utf-8"))
    except (ValueError,OSError) as e: errors.append(name+": "+str(e))
if (root/"comparator.json").exists():
    errors.append("The root comparator.json must be removed; use per-theorem Palomar configs")
for error in errors: print("ERROR:",error,file=sys.stderr)
if errors: sys.exit(1)
print("Static module/header and JSON checks passed (NOT Lean or Comparator verification)")
