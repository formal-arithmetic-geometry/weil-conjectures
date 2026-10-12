## What changed
Replaced the hole in `Algebra.essentiallySmooth_factors_through_smooth` by a proof that unpacks
essential smoothness, factors through a principal localization, derives smoothness using Mathlib,
and transports the factorization through `ULift` and the presentation equivalence. The target's
signature is unchanged. Added the proof-only import `Sheaf.RingTheory.FactorsThroughLocalization`.

## Proved and sorry left
Hole closed: `Algebra.essentiallySmooth_factors_through_smooth` (1 of 1 original holes).
Hole added and still open: `Algebra.factors_through_principal_localization`, node
`lem-factors-through-localization-of-smooth`. This is a decomposition: one hole closed, one
strictly simpler hole added, net zero. The target still depends on `sorryAx` through this lemma.
No data definition or arbitrary witness choice was added.

## No longer needed
Removed the direct import `Sheaf.RingTheory.LocalizationColimitPrincipalLocalizations`.
The target no longer directly uses nodes `lem-weil-pbc-localization-colimit-principal-localizations`,
`def-weil-pbc-category-colimit`, and
`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`. Its proof uses an explicit
principal-stage factorization instead. No claim is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong
The first worker's split still asserted factorization through an unspecified smooth algebra,
and its docstring omitted the full proof and cited the parent's blueprint id. It also lacked
Mathlib search records and left the target's DAG metadata unchanged. Its local instances caused
compile warnings. The second reading repaired these issues. The denominator argument is below
unit level and does not bypass any node of `dag/units/sk-thm-p1.json`'s `realized` route.

## New nodes
`lem-factors-through-localization-of-smooth`: despite the historical filename, now records only
`Algebra.factors_through_principal_localization` in
`lean/Sheaf/RingTheory/FactorsThroughLocalization.lean`. It makes no smoothness assumption and
identifies the intermediate algebra as a principal localization. Its docstring gives the full
finite-generator/finite-relation denominator-clearing proof, including empty products and 0 in S.
Searches using grep, loogle and leanfinder found preservation/locality results, no matching
factorization theorem. LeanSearch was attempted but returned an Internal Server Error; its
unavailability is recorded without a mathematical verdict. No change record is needed: all existing signatures and definitions remain
unchanged, and the new statement has not been delivered before.

## Second reading by J2
1. Diffed the target against the repository. Every existing signature and docstring is byte for
byte unchanged; only its proof and proof-only imports differ. The new theorem is in a new module.
2. Both modules compile without warnings. The only remaining hole is the named theorem listed
above. There are no `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definitions.
Scratch-copy `#print axioms` checks returned exactly `propext`, `Classical.choice`,
`Quot.sound` and `sorryAx` for both declarations; the latter comes from the named open theorem.
3. Replaced the original near-restatement with principal-localization factorization, independent
of smoothness. Checked empty presentations, S={1}, and 0 in S: the denominator-clearing proof
works in each case. Searched Mathlib three ways and the library with alternative factor/lift terms;
no duplicate statement was found. Added its complete proof docstring and search records.
4. Preserved the target's presentation/principal-stage route and the unit's realized route.
Mathlib proves principal-localization smoothness and composition. Pruned the unused colimit import;
all old proof dependencies no longer used directly are listed above. The unresolved lower lemma
requires finite-presentation denominator descent, not the smooth-factorization conclusion.
5. Updated the target node's proof, proof_deps and proof_origin to match the actual Lean proof.
Updated the new node to match the more precise theorem and its denominator-clearing proof.

Second reading changed the split statement, the target reduction, warning-causing local instances,
imports, docstring, DAG metadata, search records, and progress accounting.
