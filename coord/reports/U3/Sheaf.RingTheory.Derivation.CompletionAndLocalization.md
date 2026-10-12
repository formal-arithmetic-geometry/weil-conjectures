## What changed

Proved `Derivation.exists_completion_and_unique_localization` in
`lean/Sheaf/RingTheory/Derivation/CompletionAndLocalization.lean`, preserving its exact
signature, visibility, universes, and existing public imports.

The completion proof constructs the quotient additive maps after proving that derivations
lower ideal powers. It constructs the shifted coordinate map on the inverse limit, proves
compatibility and the Leibniz rule componentwise, and compares the raw module quotients
with Mathlib's `evalₐ`. All auxiliary constructions and lemmas are private and proved.
The quotient maps and evaluation identity actually hold also at n = 0, so the required
positive-index clauses follow without additional hypotheses. No finite generation,
Noetherianity, separatedness, or completeness of R is assumed.

Added the proof-only import `WeilConjectures.RingTheory.Derivation.Localization`.
Its proved square-zero extension construction supplies localization existence and its
extensionality lemma supplies uniqueness. The quotient formula is proved here using
`Derivation.leibniz_of_mul_eq_one` and localization identities.

Updated the existing DAG node's proof and proof_origin for this shorter localization route.
The completion definition remains its only DAG proof dependency. The unit's realized
statement and steps are untouched. No new public declarations or modules are delivered.

## Proved and sorry left

Closed the one original hole:
`Derivation.exists_completion_and_unique_localization`
(node `lem-weil-pbc-derivation-extends`).

Holes closed: 1. Holes added: 0. Split off: 0. No sorry remains in the delivered module.
This is a complete proof, not a decomposition through unproved statements.

The full module compiles without warnings through `lcompile.py`.
The delivery dry run checks the axioms of all delivered declarations.

## No longer needed

No original imports, DAG dependency nodes, or library modules are pruned.
The original localization plan's separate fraction well-definedness, additivity,
and multiplicativity expansions are unnecessary: the existing square-zero construction
already proves these facts. Its quotient rule still receives an explicit proof here.
No additional Sheaf statement modules are imported.

## Where the brief, the DAG or earlier work was wrong

The DAG's old searches overlooked the already proved source-library localization module
`WeilConjectures.RingTheory.Derivation.Localization`. Its additive-map interface needs
composition with the localization algebra map and integer-linearity when packaging it as
an absolute derivation. The target statement itself is correct and unchanged.

The local Stacks literature file was unavailable; read Tag 07PE directly at
https://stacks.math.columbia.edu/tag/07PE. The completion follows its construction,
including the omitted componentwise derivation verification. Edge cases I = bottom,
I = top, the zero ring, and localizations with 0 in the submonoid require no exceptions:
the quotient and localization identities used in the proof apply to them as stated.

## Second reading by U3

1. **No accidental visible changes.** Compared the delivered module with the repository version. The existing theorem statement, universes, visibility, and public imports are unchanged; the only module difference is the proof-only import of `WeilConjectures.RingTheory.Derivation.Localization` and the proof itself. The DAG node changes only its proof route and proof origin, with its statement and unit unchanged.

2. **Proof validity.** Compiled `CompletionAndLocalization.lean` through `lcompile.py` successfully. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and no definition contains a sorry. The target's remaining `sorryAx` dependencies come only from imported open declarations; the delivered theorem introduces no new hole.

3. **Statements and dependencies.** The target statement is byte-for-byte unchanged and has no split-off statements. The completion construction uses compatible quotient maps and the existing adic completion API. Localization uses the existing square-zero extension and extensionality declarations, with an explicit quotient-rule calculation. No new node or public declaration was added, and the DAG proof dependencies remain the completion definition node.

4. **Pruning and route.** The added localization import is proof-only. The route is shorter than the old fraction-by-fraction expansion because the already proved square-zero localization construction supplies existence and uniqueness; the quotient formula is still verified explicitly. No unit step is bypassed: the completion and localization clauses of the target are both proved, and the unit's realized record is unchanged.

5. **DAG agreement.** The node proof steps and proof origin now describe the compatible-coordinate completion construction and the square-zero localization route actually present in Lean. No obsolete proof dependency or module is removed, and no new node is required.

**Changes made during second reading:** added this review section; no Lean statement, definition, or proof correction was needed after compilation and comparison.
