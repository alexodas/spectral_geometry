[← Main README and table of contents](../README.md)

## 7. Research methodology and maintenance rules

These rules apply to the README and its linked documentation chapters. Numbered section references retain their original meaning.

**Maintenance rules:** append each new verified result to §4 and to the
roadmap **without deleting earlier results or historical registrations**;
update the canonical §5 module list whenever source imports change;
update the **table of contents** whenever sections are added, renamed
or reorganized; and review the entire README for **obsolete statements**,
revising old status sentences and open-problem descriptions when later
theorems resolve them without erasing their historical context.
For Palomar, preserve a separate Comparator inside each
`palomar/<candidate>/` directory, preserve predecessor packages,
and never place a redundant Comparator at the repository root.

Keep the **entire README scientific, cumulative and readable in plain English**.
Explain each result's mathematical meaning, assumptions, exact conclusions,
limitations and relationship to earlier theorems. Retain formulas and Lean
declaration names where useful, but explain them in accessible language.
Do not include commit hashes, pull request references, numbered CI runs,
build logs, failed proof attempts or operational development chronology
in the README. Such provenance belongs in the repository history and CI
records, or in separate technical notes when needed. Keep existing Palomar
registry identifiers and links, because they identify independently
registered mathematical statements. Report verification status and scope
without operational identifiers. Never mark a result as verified before
the required checks have succeeded, and distinguish full Lean verification
from independent comparison of the selected Palomar statements.