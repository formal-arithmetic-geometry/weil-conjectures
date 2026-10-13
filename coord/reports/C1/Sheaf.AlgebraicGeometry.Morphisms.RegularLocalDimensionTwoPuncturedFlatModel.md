## What changed

Replaced the single `sorry` in
`AlgebraicGeometry.Scheme.exists_finite_flat_model_of_regular_local_dimension_two`
with a compiling proof, without changing its signature or public imports.
The proof computes depth at the closed-point stalk using its ring isomorphism with A
and a regular sequence of minimal maximal-ideal generators. The existing
`exists_finite_extension_of_depth_two` constructs the finite model and supplies its
source boundary depth. The proved new theorem
`AlgebraicGeometry.Scheme.flat_of_regular_local_surface_depth_two` makes that model
flat, and inversion of the supplied restriction isomorphism gives the required equation.
Locally Noetherian source follows from finite type over the Noetherian target.

The new module is `Sheaf.AlgebraicGeometry.Morphisms.RegularLocalSurfaceDepthTwoFlat`.
It proves flatness by the stalk criterion. At the boundary, quasi-finite
incomparability gives the source-dimension upper bound and zero-dimensional closed
fibre; depth gives the dimension lower bound. The existing miracle-flatness theorem
then applies. Its two private ring lemmas are proved entirely from Mathlib.
Only proof imports were added to the original module.

Sources read: [Stacks 0EY6](https://stacks.math.columbia.edu/tag/0EY6),
[0BMA](https://stacks.math.columbia.edu/tag/0BMA), and
[00R4](https://stacks.math.columbia.edu/tag/00R4).
The depth-two extension and miracle-flatness steps preserve the unit's classical
purity/depth-two extension inputs; no unit or chapter statement/step was bypassed.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.exists_finite_flat_model_of_regular_local_dimension_two`.
Proved the new theorem `AlgebraicGeometry.Scheme.flat_of_regular_local_surface_depth_two`
(node `lem-sbc-regular-local-surface-depth-two-flat`) and its private dimension lemmas.
No `sorry` remains in either delivered module. No new holes were added or split off.
The proof uses the existing depth-two extension, regular-generator, depth bound, and
miracle-flatness declarations; their dependencies remain separate items.

Both delivered modules compile cleanly through lcompile.py, with the original target
signature preserved. Edge cases: an empty source has no stalk points; the fibre
quotient in the local ring lemma is nontrivial because the maximal ideal's image is
proper. No normality, injectivity, nonempty cover, connectedness, or rank assumption
was introduced. The model is obtained inside a theorem, with no choice-based new definition.

## No longer needed

No original import was removed: the original five public imports are needed by its
statement. The original node's proof no longer uses the following planned nodes:

- `lem-weil-pbc-regular-local-localization`
  (`Sheaf.RingTheory.RegularLocalLocalization`): closed-point stalk isomorphism suffices.
- `lem-weil-pbc-regular-ring-normal`
  (`Sheaf.RingTheory.RegularRingNormal`): the depth-two construction needs no normality.
- `lem-weil-pbc-going-down-normal-integral` (Mathlib going-down leaf):
  quasi-finite incomparability supplies a dimension upper bound; depth supplies the lower bound.
- `lem-weil-pbc-serre-criterion-normal`
  (`Sheaf.RingTheory.SerreCriterionNormal`): the extension theorem supplies depth directly.

Miracle flatness remains needed through the new flatness module. No claim is made
that these four nodes are globally unreachable through other callers.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan invoked the 0BM9 global-normal-algebra construction without a
Lean declaration for that construction among its dependencies. The existing 0EY6(2)
depth-two extension theorem provides the needed finite model directly. The replacement
route proves the model's flatness using its supplied depth rather than proving normality
and going down first. The existing theorem docstring records the original normal-algebra
plan; the updated node records the proof actually implemented.

The broad regular-codimension-two extension/model theorems cannot be used here: their
imports reach this module through `RegularLocalPuncturedEtalePurity`. The delivered
proof imports neither, and does not use purity to prove the finite-flat-model input.
No existing declaration or definition was corrected, and no consumer adaptation is needed.

## New nodes

`lem-sbc-regular-local-surface-depth-two-flat`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-regular-local-surface-depth-two-flat.json`,
records the proved supplied-model flatness criterion. It constructs no model and
asserts only flatness of an already supplied finite morphism with boundary depth two.
Its module is `Sheaf.AlgebraicGeometry.Morphisms.RegularLocalSurfaceDepthTwoFlat`.
LeanSearch was unavailable (HTTP internal server error); LeanFinder, Loogle, and
Mathlib grep were run and recorded in searches.jsonl. No exact criterion was found.
Blueprint search for miracle flatness found no matching blueprint node. The existing
regular-generator, depth bound, and miracle-flatness nodes are generic commutative
algebra tools; no unit route was replaced. There are no change records.

## Second reading by C1

1. Compared the delivered target module with the repository version. The target theorem signature and all existing declarations are unchanged; only proof imports and proof bodies differ. Verdict: pass.
2. Compiled both delivered modules with lcompile.py. The target hole is closed, the new flatness theorem compiles, and there are no remaining `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. Reviewed the added flatness statement and its node. It asserts exactly the supplied finite-model flatness criterion used by the target, with no extra hypotheses or weakened conclusion; the argument handles empty sources and the local fibre edge case. Verdict: pass.
4. Checked pruning against the old node proof dependencies. The four listed normality/localization/going-down/Serre nodes are no longer used; the finite depth-two extension and miracle-flatness route remains. Verdict: pass.
5. Checked the DAG proof, proof dependencies, proof origin, unit route, and report against the Lean proof. The new node records the actual route and the unit's realized route is preserved. Verdict: pass.

Changed only the review record and `.check` marker; no Lean code or DAG statement was altered during second reading.
