#!/usr/bin/env python3
"""Audit the active Mathlib-only Challenge and per-theorem Palomar configs.

This is a static packaging gate; the full Lean build and Comparator
perform actual kernel checking and independent statement comparison.
The prior unsubmitted dark/bright package is preserved as an archive.
"""
import json
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parent.parent
errors = []
challenge = root / "Challenge.lean"
solution = root / "Solution.lean"
config_path = root / "palomar/plateau-isolated-double-eigenvalue/comparator.json"
archived_config_path = root / "palomar/dark-bright/comparator.json"
try:
    statement = challenge.read_text(encoding="utf-8")
    config = json.loads(config_path.read_text(encoding="utf-8"))
    metadata = json.loads((root / "formalization.yaml").read_text(encoding="utf-8"))
    solution_text = solution.read_text(encoding="utf-8")
except (OSError, UnicodeError, ValueError) as error:
    print(f"Comparator packaging error: {error}", file=sys.stderr)
    sys.exit(1)

# Each candidate keeps its Comparator in its own Palomar directory.
# The root Comparator is intentionally absent.
if (root / "comparator.json").exists():
    errors.append("Root comparator.json must not exist")
per_theorem_configs = sorted(path.relative_to(root).as_posix()
    for path in (root / "palomar").glob("*/comparator.json"))
if per_theorem_configs != [
    "palomar/dark-bright/comparator.json",
    "palomar/exact-leakage-free-preparation/comparator.json",
    "palomar/plateau-isolated-double-eigenvalue/comparator.json",
    "palomar/protected-exact-preparation/comparator.json",
    "palomar/signed-bright-splitting/comparator.json",
    "palomar/spectral-protection-during-coordinated-control/comparator.json",
]:
    errors.append("Expected five predecessor Comparators and the active bounded-plateau Comparator")
try:
    archived_config = json.loads(archived_config_path.read_text(encoding="utf-8"))
    old_target = "SpectralGeometry.AmmannBeenker.crossingOneEdgeDarkBrightResponse"
    if archived_config.get("theorem_names", [])[-1:] != [old_target]:
        errors.append("Historical dark-bright Comparator target must be preserved")
    if archived_config.get("challenge_module") != "Challenge" or archived_config.get("solution_module") != "Solution":
        errors.append("Historical dark-bright Comparator module names changed")
    if not (root / "palomar/dark-bright/Challenge.lean").is_file():
        errors.append("Historical dark-bright Challenge snapshot is missing")
    if not (root / "palomar/dark-bright/Solution.lean").is_file():
        errors.append("Historical dark-bright Solution snapshot is missing")
except (OSError, UnicodeError, ValueError) as error:
    errors.append(f"Cannot inspect historical Comparator archive: {error}")

if config.get("challenge_module") != "Challenge" or config.get("solution_module") != "Solution":
    errors.append("Comparator must use root Challenge and Solution modules")
namespace = "SpectralGeometry.AmmannBeenker"
proof_module = "SpectralGeometry.AmmannBeenkerPlateauBulk"
# Preserve the previous spectral certificates and select the new preparation statements.
previous_sources = {
    "SpectralGeometry.AmmannBeenker.admitted_zero": "SpectralGeometry.AmmannBeenkerCutProject",
    "SpectralGeometry.AmmannBeenker.mate_involutive": "SpectralGeometry.AmmannBeenkerGraph",
    "SpectralGeometry.AmmannBeenker.compactA_mem_domain": "SpectralGeometry.AmmannBeenkerCompactModes",
    "SpectralGeometry.AmmannBeenker.compactB_mem_domain": "SpectralGeometry.AmmannBeenkerCompactModes",
    "SpectralGeometry.AmmannBeenker.centralLift_admitted": "SpectralGeometry.AmmannBeenkerCentralPatch",
    "SpectralGeometry.AmmannBeenker.coordinatedRingPair_adjacent": "SpectralGeometry.AmmannBeenkerCoordinatedRingControl",
    "SpectralGeometry.AmmannBeenker.coordinatedRing_disjoint": "SpectralGeometry.AmmannBeenkerCoordinatedRingControl",
    "SpectralGeometry.AmmannBeenker.coordinatedRing_matching": "SpectralGeometry.AmmannBeenkerCoordinatedRingControl",
    "SpectralGeometry.AmmannBeenker.coordinatedLevelRadius_eq_zero_iff": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedPlane_eigenvalue_iff": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedHamiltonian_plane_commutes": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedHamiltonian_complement_commutes": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedCluster_centered_condition_of_budget": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedCluster_centered_gap_ge": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedCluster_centered_isolation": "SpectralGeometry.AmmannBeenkerCoordinatedAxisDynamics",
    "SpectralGeometry.AmmannBeenker.coordinatedDurationAngle_scaled": "SpectralGeometry.AmmannBeenkerCoordinatedVariableDuration",
    "SpectralGeometry.AmmannBeenker.coordinatedProtocolStretch_bounds": "SpectralGeometry.AmmannBeenkerCoordinatedProtectedPreparation",
    "SpectralGeometry.AmmannBeenker.coordinatedProtectedSetting_of_budget": "SpectralGeometry.AmmannBeenkerCoordinatedProtectedPreparation",
    "SpectralGeometry.AmmannBeenker.coordinatedProtocol_protected_exact_preparation": "SpectralGeometry.AmmannBeenkerCoordinatedProtectedPreparation",
}

expected_sources = {
    "SpectralGeometry.AmmannBeenker.admitted_zero": "SpectralGeometry.AmmannBeenkerCutProject",
    "SpectralGeometry.AmmannBeenker.finite_norm_sublevel": "SpectralGeometry.AmmannBeenkerCutProject",
    "SpectralGeometry.AmmannBeenker.mate_involutive": "SpectralGeometry.AmmannBeenkerGraph",
    "SpectralGeometry.AmmannBeenker.canonicalPlateauHeight_ge_five": "SpectralGeometry.AmmannBeenkerPlateauOperator",
    "SpectralGeometry.AmmannBeenker.canonicalPlateauPotential_outside": "SpectralGeometry.AmmannBeenkerPlateauOperator",
    "SpectralGeometry.AmmannBeenker.plateauPotential_normalized_norm_le": "SpectralGeometry.AmmannBeenkerPlateauOperator",
    "SpectralGeometry.AmmannBeenker.sector_card": "SpectralGeometry.AmmannBeenkerCentralPatch",
    "SpectralGeometry.AmmannBeenker.compactA_inner_self": "SpectralGeometry.AmmannBeenkerCompactStates",
    "SpectralGeometry.AmmannBeenker.compactB_inner_self": "SpectralGeometry.AmmannBeenkerCompactStates",
    "SpectralGeometry.AmmannBeenker.compactA_inner_compactB": "SpectralGeometry.AmmannBeenkerCompactStates",
    "SpectralGeometry.AmmannBeenker.plateauHamiltonian_realSpectrum_gap": "SpectralGeometry.AmmannBeenkerPlateauSpectrum",
    "SpectralGeometry.AmmannBeenker.canonicalPlateauDefect_zero_outside": "SpectralGeometry.AmmannBeenkerPlateauBulk",
    "SpectralGeometry.AmmannBeenker.canonicalPlateau_isolated_double_eigenvalue": "SpectralGeometry.AmmannBeenkerPlateauBulk"
}
for filename in ("Challenge.lean", "Solution.lean", "formalization.yaml"):
    if (root / filename).read_bytes() != (config_path.parent / filename).read_bytes():
        errors.append(f"Active root {filename} differs from its candidate snapshot")
registered = root / "palomar/signed-bright-splitting"
for filename in ("Challenge.lean", "Solution.lean", "formalization.yaml", "comparator.json"):
    if not (registered / filename).is_file():
        errors.append(f"Registered L5 snapshot missing: {filename}")
registered_cfg = json.loads((registered / "comparator.json").read_text())
if registered_cfg.get("theorem_names", [])[-1:] != [f"{namespace}.crossing_final_signed_bright_spectral_splitting"]:
    errors.append("Registered L5 target must be preserved")
preparation = root / "palomar/exact-leakage-free-preparation"
for filename in ("Challenge.lean", "Solution.lean", "formalization.yaml", "comparator.json"):
    if not (preparation / filename).is_file():
        errors.append(f"Registered preparation snapshot missing: {filename}")
preparation_cfg = json.loads((preparation / "comparator.json").read_text())
if preparation_cfg.get("theorem_names", [])[-1:] != [f"{namespace}.coordinatedProtocol_exact_preparation"]:
    errors.append("Registered preparation target must be preserved")
protection = root / "palomar/spectral-protection-during-coordinated-control"
for filename in ("Challenge.lean", "Solution.lean", "formalization.yaml", "comparator.json"):
    if not (protection / filename).is_file():
        errors.append(f"Registered protection snapshot missing: {filename}")
protection_cfg = json.loads((protection / "comparator.json").read_text())
if protection_cfg.get("theorem_names", []) != list(previous_sources)[:-4]:
    errors.append("Registered spectral-protection theorem selection must be preserved")
readme = (root / "README.md").read_text(encoding="utf-8")
previous_summary = readme.split("### Spectral protection during coordinated control\n\n", 1)[1].split("\n\nThe research direction was conceived", 1)[0]
if previous_summary != json.loads((protection / "formalization.yaml").read_text())["project"]["description"]:
    errors.append("Registered spectral-protection description must be preserved")
fifth = root / "palomar/protected-exact-preparation"
fifth_cfg = json.loads((fifth / "comparator.json").read_text())
if fifth_cfg.get("theorem_names", []) != list(previous_sources):
    errors.append("Registered fifth theorem selection must be preserved")
fifth_summary = readme.split("### Exact protected state preparation with arbitrarily weak controls\n\n", 1)[1].split("\n\n#### Visual summary of the fifth theorem", 1)[0]
if fifth_summary != json.loads((fifth / "formalization.yaml").read_text())["project"]["description"]:
    errors.append("Registered fifth description must be preserved")
summary = readme.split("### An isolated double eigenvalue without global confinement\n\n", 1)[1].split("\n\n#### Visual summary of the sixth theorem", 1)[0]
if summary != metadata.get("project", {}).get("description"):
    errors.append("Executive summary and formalization description differ")
names = config.get("theorem_names")
if names != list(expected_sources):
    errors.append("Select the bounded-plateau conclusions and their concrete model certificates")
aligned = metadata.get("alignment", {}).get("statements", [])
if (len(aligned) != len(expected_sources) or
        {s.get("lean"): s.get("module") for s in aligned} != expected_sources):
    errors.append("formalization.yaml must map each Comparator theorem to its proof module")
if metadata.get("status", {}).get("axioms") != config.get("permitted_axioms"):
    errors.append("formalization.yaml and Comparator must report the same permitted axioms")
if config.get("definition_names") != []:
    errors.append("Concrete model definitions must be compared by body, with no definition holes")
for key in ("theorem_names", "definition_names"):
    names = config.get(key)
    if not isinstance(names, list) or not all(isinstance(n, str) for n in names):
        errors.append(f"{key} must be a list of qualified names")
    elif len(names) != len(set(names)) or (key == "theorem_names" and not names):
        errors.append(f"{key} has duplicates or an empty selection")

headers = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", statement, re.MULTILINE)
if headers != ["Mathlib"]:
    errors.append(f"Challenge must import exactly Mathlib, got {headers!r}")
if "import SpectralGeometry" in statement:
    errors.append("Challenge must never import substantive SpectralGeometry proofs")
solution_imports = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", solution_text, re.MULTILINE)
if solution_imports != [proof_module] or f"public import {proof_module}" not in solution_text:
    errors.append(f"Solution must publicly import exactly {proof_module}")
if len(statement.splitlines()) > 1000 or len(statement.encode("utf-8")) > 100 * 1024:
    errors.append("Challenge exceeds Palomar's 1000-line/100-KiB limits")

decls = {"theorem": set(), "definition": set()}
pattern = r"^\s*(?:@\[expose\]\s+)?(?:noncomputable\s+)?(theorem|def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
namespaces = []
for line in statement.splitlines():
    namespace = re.fullmatch(r"namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", line.strip())
    if namespace:
        namespaces.append(namespace.group(1))
    elif namespaces and line.strip() == "end " + namespaces[-1]:
        namespaces.pop()
    declaration = re.match(pattern, line)
    if declaration:
        kind, name = declaration.groups()
        decls["theorem" if kind == "theorem" else "definition"].add(".".join(namespaces + [name]))
for key, kind in (("theorem_names", "theorem"), ("definition_names", "definition")):
    for name in config.get(key, []) if isinstance(config.get(key), list) else []:
        if name not in decls[kind]:
            errors.append(f"{name}: missing standalone {kind} declaration in Challenge")

files = sorted(path.name for path in root.glob("comparator*.json"))
if files:
    errors.append(f"No root Comparator config is allowed, found {files}")

for error in errors:
    print("Comparator coverage error:", error, file=sys.stderr)
if errors:
    sys.exit(1)
print(f"Single Mathlib-only Challenge: {len(statement.splitlines())} lines, "
      f"{len(statement.encode('utf-8'))} bytes; "
      f"{len(config['theorem_names'])} selected theorem(s) and "
      f"{len(config['definition_names'])} selected definitions.")
