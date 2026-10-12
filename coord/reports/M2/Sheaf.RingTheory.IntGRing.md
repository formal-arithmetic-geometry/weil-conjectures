## What changed

Proved `Int.isGRing` by the original zero-prime/nonzero-prime route, using
`Int.prime_localizations_dvr`, `IsLocalization.isRegular_and_fiber`, and
`AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero`.
The zero-prime completion map is an isomorphism and therefore a localization at
`{1}`. The nonzero-prime localization is a DVR; injectivity of the integer map
establishes characteristic zero, which passes to its fraction field.
Added proof-only imports `Sheaf.RingTheory.LocalizationRegular` and
`Mathlib.Algebra.CharP.Algebra`. Updated the existing parent node's proof route.
The existing statement, docstring, public import, and definitions are unchanged.

## Proved and sorry left

`Int.isGRing` is proved from the existing support declarations. No `sorry` remains
in the delivered module and no new declaration or split-off statement is added.
The imported support theorems remain open: `Int.prime_localizations_dvr`,
`IsLocalization.isRegular_and_fiber`, and
`AdicCompletion.isRegular_algebraMap_of_isDiscreteValuationRing_of_charZero`.
`#print axioms Int.isGRing` reports `propext`, `Classical.choice`, `Quot.sound`,
and `sorryAx` from those existing dependencies; this is a reduction, not an
axiom-free completion of the target closure.

## No longer needed

Removed `lem-weil-pbc-field-regular-ring` from the parent's direct `proof_deps`:
the field case now uses `lem-weil-pbc-localization-regular`. Field regularity
remains a dependency of that existing localization theorem, so no claim is made
that its node is globally unreachable. No original import or module is removed.
Removed the first worker's undelivered `Int.regular_local_completion` and its
new node `lem-weil-pbc-z-regular-local-completion`; neither is needed.

## Where the brief, the DAG or earlier work was wrong

The first worker moved all completion-map regularity to one new sorry theorem
and supplied only the standard Noetherian instance. This was effectively the
whole mathematical item restated, and its proof did not use the imported plan
lemmas. The new node also copied stale review/search metadata from the parent,
and the parent node had not been updated to match the proof. Replaced this with
a genuine case reduction using existing statements, eliminating the new node.
The original DAG's field case can use the already stated localization-regularity
theorem, rather than adding another completion-regularity statement.

## Second reading by M2

1. Compared the delivered module against the repository with `diff -u`.
   Verdict: `theorem isGRing : IsGRing ℤ` is byte-for-byte unchanged, as are its
   existing docstring and public imports. There are no changed definitions or
   new externally visible declarations, and no change record is needed.
2. Compiled the module locally with `lcompile.py`: no errors or warnings.
   Scanned all delivered Lean for sorry and forbidden constructs: none.
   Compiled a scratch copy with `#print axioms Int.isGRing`: exactly `propext`,
   `Classical.choice`, `Quot.sound`, `sorryAx`. Verdict: valid Lean reduction
   using still-open existing support statements, with no new axiom or sorry.
3. Reviewed the proposed split-off statement and rejected it as carrying almost
   the whole item. Searched with fresh wording using leanfinder, loogle, grep,
   and `rg` on the library. Mathlib provides `AdicCompletion.ofAlgEquiv` and
   localization-at-units infrastructure; the library already provides
   `IsLocalization.isRegular_and_fiber`. Verdict: no split-off needed. Checked
   both edge cases: zero gives a field with zero maximal ideal; every nonzero
   prime gives a DVR with characteristic-zero fraction field. The proof does
   not assume positive-characteristic DVR completions are regular.
4. Read top-down from `IsGRing` and followed the existing field/DVR route.
   Every import is used: GRing in the statement, integer localizations in both
   branches, localization regularity in the zero branch, DVR regularity and
   characteristic-zero transport in the nonzero branch. Inspected
   `dag/units/sk-thm-p1.json` and its `realized` fields; the parent is below the
   realized unit steps and none is bypassed or changed. Verdict: route kept,
   imports minimal, and the complete direct dependency pruning is recorded.
5. Updated only `proof`, `proof_deps`, `proof_origin` of
   `lem-weil-pbc-z-g-ring` to match the actual Lean argument. Its dependencies
   are precisely the G-ring definition, integer prime localizations, regularity
   of localization maps, and characteristic-zero DVR completion regularity.
   Verdict: DAG and Lean agree; no new node or change record is delivered.

Changed during second reading: removed the vacuous regularity split and its
node, wrote the prime-by-prime proof using existing support declarations, added
two proof-only imports, corrected the parent's DAG route, and replaced the
outdated report with the checked result.
