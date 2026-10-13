## What changed

In `Sheaf.RingTheory.FiniteTypeApproximationFlatLoci`, defined the full flat loci explicitly
and proved their openness using Noetherian finite presentation and
`Module.isOpen_setOf_flat_localizedModule`. Proved persistence by turning each supplied
ring tensor comparison into `Algebra.IsPushout` and applying the existing proved
`Module.Flat.localizedModule_of_isPushout` with the supplied module tensor comparison.
A proved private helper `Algebra.localized_restrict_eq` compares the canonical localized
module action with the restricted action required by the unchanged statement.

The cover is reduced to the strictly smaller fixed-prime statement
`Algebra.exists_flat_finiteType_approximation_point` in the new module
`Sheaf.RingTheory.FiniteTypeApproximationFlatPoint`. It retains the supplied approximation
hypotheses and concludes only that a contracted prime is flat at some stage. It says
nothing about open subsets or persistence. Updated the parent node's proof route.
All existing public signatures and docstrings remain unchanged.

## Proved and sorry left

Closed the one original hole, `Algebra.exists_flat_finiteType_approximation_loci`
(node `lem-pc-finite-type-approximation-flat-loci`), by a complete Lean proof of openness,
membership and persistence plus the pointwise lemma for the cover. Added one hole:
`Algebra.exists_flat_finiteType_approximation_point`
(node `lem-pc-finite-type-approximation-flat-point`). This is a decomposition, with net
holes closed minus added equal to zero, and substantive openness/persistence glue proved.
No sorry remains in the original module; the new module contains exactly the named sorry.

All delivered modules compile through lcompile.py with no warnings. The unchanged
FlatLocalizedModuleBaseChange source was compiled alongside the files because its shared
olean has not yet appeared in the local compiled mirror; it contains no delivery changes.

## No longer needed

Removed direct imports from the original module:
`Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`,
`Sheaf.RingTheory.ColimitEventuallyFlat`, and `Sheaf.RingTheory.FlatModuleAtPrime`.
These move to the pointwise lemma's planned imports and are still needed for that step;
no module is claimed globally pruned.

The original node now directly uses the new point node and
`lem-weil-pbc-flat-localized-module-base-change`, together with its existing Noetherian,
finite-presentation and openness nodes. Its former direct dependencies
`def-weil-pbc-localization-at-prime`, `lem-pc-affine-flat-module-local-criterion`,
`lem-weil-pbc-colimit-eventually-flat`, `lem-weil-pbc-filtered-colimit-localization-at-prime`,
`lem-weil-pbc-filtered-colimit-modules-criterion`, `lem-weil-pbc-flat-over-localization`,
`lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-localization-tensor-over-base`, and
`lem-weil-pbc-localization-tensor-product` belong to the pointwise step.
`lem-weil-pbc-flat-module-base-change` is subsumed in the proved localized pushout theorem.
Thus none of these is asserted unnecessary in the entire target import closure.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction to the original statement was needed. The earlier DAG's
persistence argument is already packaged in the existing localized pushout theorem,
so it does not need to be rebuilt using individual localization/tensor lemmas.
The new pointwise statement is exactly the first paragraph's fixed-prime assertion in
Stacks Tag 02JO, read together with Tag 00R6. Its remaining work is localization of
supplied cocones and tensor comparisons, not a globally flat stage.

Searches: LeanFinder returned general flatness/localization results but no fixed-prime
result for a supplied diagram; Loogle found pushout equivalence tools; Mathlib grep
found no eventual-flatness theorem; LeanSearch returned an Internal Server Error and is
recorded unavailable. Blueprint search found no exact match. The library's
FlatPointNoetherianModel theorem chooses a new model and does not select a stage in this
supplied approximation.

Edge cases of the new pointwise statement: if S is the zero ring there are no primes
and the conclusion is vacuous; for a singleton constant diagram it reduces to preservation
of flatness by localization; the zero module is flat at every contracted prime.
The directed nonempty assumption permits common-stage fraction representatives.

## New nodes

`lem-pc-finite-type-approximation-flat-point`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-type-approximation-flat-point.json`, records
the remaining fixed-prime localized-colimit argument, with full unchanged approximation
hypotheses, source, proof steps, real search records and verbatim Lean signature.
No definition, target statement or interface is changed; no forced adaptation is needed.

## Second reading by S2

1. Compared every sandbox module against the repository. The loci theorem's existing
   signature is byte-for-byte unchanged, as is its docstring. The supporting
   FlatLocalizedModuleBaseChange file is identical and is only a local compile dependency;
   delivery excludes it. No definition or target interface changed. Verdict: pass.
2. Compiled all three files through lcompile.py without errors or warnings. Scanned for
   forbidden declarations and holes: only the named point theorem has `sorry`. A scratch
   copy with `#print axioms` shows propext, Classical.choice, Quot.sound, and sorryAx for
   the loci and point theorems; localizedModule_of_isPushout has only the three allowed
   axioms. No data is chosen from an unproved existence theorem. Verdict: pass.
3. Read the split-off statement, docstring, node, Stacks Tags 02JO and 00R6, and the
   existing ColimitEventuallyFlat and FlatPointNoetherianModel statements. The point
   theorem isolates the fixed-prime cover argument and omits openness and persistence;
   it is a strict part of the argument, not a renamed parent statement. Its localized
   cocone and tensor transport work cannot be closed by a short application of the
   available local-ring theorem. Independently searched LeanFinder for descent of
   flatness at a prime in a filtered colimit, Loogle for Module.Flat and LocalizedModule,
   and Mathlib grep for flat/colimit and exists_flat, plus repository rg. No duplicate
   supplied-diagram theorem was found. Checked the zero ring (no primes), zero module,
   and singleton constant diagram cases. Verdict: pass; one legitimate split hole.
4. Read the explicit flat-locus construction, module-action comparison, pushout
   construction and persistence proof. Every new import of the loci module is used and
   proof-only. The three removed direct imports and every removed old proof dependency
   are accounted for under No longer needed; dependencies of the point step remain in
   the target closure, so no global pruning is claimed. The unit's realized record has
   empty statement and step lists; this below-unit decomposition preserves its route.
   Verdict: pass; decomposition with net holes closed minus added zero.
5. Compared the parent node as parsed JSON: only proof, proof_deps and proof_origin
   changed. Their steps match the compiled Lean argument. Checked all required fields
   of the new node and its verbatim Lean signature, source and natural-language proof.
   Verdict: pass.

Changed after this reading: added this review record only. No Lean or DAG repair was
needed. Independent source checks: https://stacks.math.columbia.edu/tag/02JO and
https://stacks.math.columbia.edu/tag/00R6.
