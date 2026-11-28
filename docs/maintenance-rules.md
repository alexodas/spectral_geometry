[← Main README and table of contents](../README.md)

## 7. Research methodology and maintenance rules

The repository distinguishes established mathematics, open research, independent verification and registry review. The scientific chapters are cumulative; the roadmap is prospective. These rules apply to the README and all linked documentation.

### Scientific record and navigation

<a id="maintaining-sections"></a>

**Maintain the scientific record.** Append new verified results to the appropriate chapter of §4 and to [Verified milestones](verified-milestones.md). Explain the assumptions, precise conclusions, proof scope and limitations. Preserve previous results, historical registrations and original research objectives. Update the canonical §5 module list whenever source imports change. Review both indexes, preserve old anchors and check links when sections are added, renamed, archived or reorganized. Retain stable numbering; a gap in the active roadmap may indicate a completed section, not missing mathematics.

### Roadmap policy: remaining work only

- **Completed and documented:** remove the objective and its completed checklist from the active roadmap; retain the result in the scientific chapter and Verified milestones. Do not duplicate the proof narrative in the roadmap.
- **Partly completed:** keep only unresolved obligations and a short link to the established result when its scope or dependency matters.
- **Paused or deferred:** keep the unresolved goal and clearly label its priority; postponement is not cancellation.
- **Superseded or ruled out:** remove obsolete tasks from active work, record the reason and link to the theorem or decision. Preserve the historical proposal, not a misleading open checkbox.
- **History:** archive former cumulative roadmap material separately, with links from the current roadmap and compatibility anchors for former sections. Never erase a proved result or a genuinely open question while shortening the roadmap.

Apply this policy to [the general roadmap](research-roadmap.md), [the active L9 roadmap](multi-qubit-roadmap.md) and [the deferred control roadmap](bright-spectral-splitting-roadmap.md). The roadmap should show what remains to be proved, why it matters, its dependencies and current priority.

### Verification and Palomar packaging

<a id="palomar-packaging-rules"></a>

Never mark a result as verified before its required checks have succeeded. Distinguish full Lean/Mathlib proof checking, independent Comparator verification of the selected statements, registry review and independent human scientific assessment. None alone establishes novelty or experimental relevance.

Preserve a separate Comparator inside each `palomar/<candidate>/` directory, preserve predecessor packages, and never place a redundant Comparator at the repository root. Preserve registered executive-summary descriptions verbatim where the packaging audit compares them with historical metadata. Explicitly mark their historical scope and document later results separately. Do not edit archived metadata merely to make a changed historical summary pass. For a new candidate, keep its executive-summary description, active formalization description and candidate snapshot identical.

### Plain English and scientific documentation

<a id="scientific-documentation-rules"></a>

Keep the README and linked scientific documentation cumulative and readable in plain English. Explain each result's mathematical meaning, assumptions, exact conclusions, limitations and relationship to earlier theorems. Retain useful formulas and Lean declaration names, with accessible explanations. Distinguish established results from conjecture, exploratory computation and application hypotheses. Review obsolete status sentences and open-problem descriptions when later proofs resolve them without erasing historical context.

Do not include commit hashes, pull request references, numbered CI runs, build logs, failed proof attempts or operational development chronology in the README. Such provenance belongs in repository history, CI records or separate technical notes. Keep existing Palomar registry identifiers and links, since they identify independently registered mathematical statements. Report verification status and scope without operational identifiers.
