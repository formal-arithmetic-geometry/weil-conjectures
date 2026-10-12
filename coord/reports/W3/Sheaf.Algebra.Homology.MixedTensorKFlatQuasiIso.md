## What changed

Proved `CochainComplex.mixedTensor_kFlat_quasiIso` with its existing signature and
visibility unchanged. Added the fully constructed natural restriction comparison in
`Sheaf.Algebra.Homology.MixedTensorRestrictionComparison` and its DAG node.

The coefficient isomorphism is Mathlib's `cancelBaseChange` followed by tensor symmetry.
Naturality is proved by tensor induction. Two applications of `isoOfComponents` give
the bicomplex isomorphism; `mapTotalIso` and `total.mapIso` give the total comparison.
Total functoriality proves naturality in both variables. The main theorem transports
ordinary-module K-flat tensor quasi-isomorphisms through the resulting arrow isomorphisms;
exact restriction detects quasi-isomorphisms.

The first clause uses the source library's `MorphismProperty.whiskerRight_of_kFlat`,
whose resolution hypothesis is supplied by `ModuleCat.hasFunctorialFlatResolution`.
The second uses `kFlat.whiskerLeft` directly. No sheaf/module equivalence is needed.
No definitions or existing statement interfaces were changed, and no other group's
module was adapted.

## Proved and sorry left

Closed the original hole in `CochainComplex.mixedTensor_kFlat_quasiIso` (node
`lem-pc-mixed-tensor-kflat-quasi-iso`). The new public theorem
`CochainComplex.exists_mixedTensor_restriction_iso` (node
`lem-pc-mixed-tensor-restriction-comparison`) is proved. All its private construction
helpers and naturality lemmas are proved. No sorry remains in the delivered modules;
no holes were added. This is a proof, not a decomposition.

Both delivered modules compile with the launcher. The delivery dry run checks every
declaration's axioms and the stage-3 preflight.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlatResolution`;
- `Sheaf.Algebra.Homology.KFlatTensorQuasiIso`;
- the redundant direct import `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`,
  already available through the existing public generic K-flat import.

This proof no longer needs nodes `lem-pc-kflat-resolution` or
`lem-pc-kflat-tensor-quasi-iso`, or their sheaf/one-point-site comparison route.
Their modules may still be needed by other proofs; this delivery only removes the
edges from this item's proof. The replacement uses the already proved generic
ordinary-module K-flat resolution machinery and the explicit mixed comparison.
The unit's realized statement and steps are empty in
`dag/units/sk-thm-picard-semicon.json`; no fixed unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

Step 1 called the restriction comparison elementary, but no existing complex-level
interface supplied it. This delivery constructs it explicitly instead of silently
assuming the compatibility with total differentials and both maps.

The original mixed bifunctor is already flipped before totalization, so its first
cochain degree is the R-complex degree. Consequently the comparison uses coefficient
symmetry inside each bidegree; no additional degree swap or sign is necessary.

The sheaf-only `kFlat_tensor_quasiIso` interface does not apply directly to the ordinary
module complexes of this theorem. The source library already proves the corresponding
generic monoidal result, so the one-point-site conversion can be pruned.

Read Stacks Tags 064L and 06Y6 on the official Stacks site; the local literature text is
absent on this clone. Checked small cases: identity and nonflat ring maps, zero rings,
zero complexes, and unbounded complexes. The comparison uses only balancing and
restriction's coproduct preservation; it imposes no flatness, boundedness or nonzero
hypothesis. The coefficient isomorphism and inverse are actual constructions.

Searches: LeanFinder returned `cancelBaseChange` and its pure-tensor formulas; Loogle
has no source-library `whiskerLeft_of_kFlat` identifier; LeanSearch returned HTTP 500
and is recorded unavailable. Mathlib and source-library grep found `mapTotalIso`,
its naturality, and the generic K-flat/resolution instances. Blueprint search found
no existing node for the restriction comparison.

## New nodes

`lem-pc-mixed-tensor-restriction-comparison` states the natural isomorphism between
restriction of mixed total tensor and ordinary total tensor with the restricted
second factor. It has no K-flat or quasi-isomorphism assumptions and is fully proved
in `lean/Sheaf/Algebra/Homology/MixedTensorRestrictionComparison.lean`.
Its node is `dag/nodes/sec-picard-framework/lem-pc-mixed-tensor-restriction-comparison.json`.
No change record is needed: existing signatures and definitions stay identical.

## Second reading by W3

1. Compared both delivered modules with the repository versions. The existing theorem signature and all existing declarations are byte-for-byte unchanged; only its proof and proof-only imports changed. The new comparison theorem is a separate declaration with its own node.

2. Compiled `MixedTensorKFlatQuasiIso.lean` and `MixedTensorRestrictionComparison.lean` with the launcher. Both compile cleanly and contain no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof uses only the permitted foundational axioms (any `sorryAx` visible from an isolated import belongs to still-open upstream declarations).

3. Checked the new comparison statement on the coefficient construction and its naturality in both variables. It makes no flatness or boundedness assumptions and uses the explicit `cancelBaseChange` isomorphism and tensor symmetry, so it is strictly the needed restriction comparison and does not restate the target. No duplicate declaration was found in the source library or Mathlib.

4. Reviewed the proof route from the target downward. The generic ordinary-module K-flat resolution and whiskering results give both clauses directly after transport through the explicit comparison; the former sheaf-resolution and sheaf tensor imports are no longer used and were removed. The comparison's public imports are required for its exposed homological-complex and monoidal interfaces; proof-only imports are private. The unit and its realized route remain unchanged.

5. Verified that the DAG nodes match the declarations and proof dependencies, including the new comparison node and its source/search metadata. The target node now records the comparison and ordinary K-flat dependency actually used by the Lean proof.

I changed only proof imports in the target, made the comparison's auxiliary imports private where possible, and added this second-reading record. No statements, definitions, or holes were added; the target hole and the comparison construction are fully proved.
