## What changed

Proved `AlgebraicGeometry.Scheme.exists_finiteGalois_germ_representative` in
`Sheaf.AlgebraicGeometry.Sites.FiniteGaloisGermRepresentative`, with its signature unchanged.
Two fully proved private helpers factor a separable embedding through Ks and construct
its finite intermediate image field as a pointed neighbourhood. The proof then constructs
E as the normal closure of P ⊔ L and applies stalk-map naturality to the pullback section.
No definitions, public signatures, instances, or other modules were changed.

Replaced the proof import of `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
with proof-only imports of `Mathlib.FieldTheory.PurelyInseparable.Basic` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`.
Updated the existing node's proof, proof_deps and proof_origin to reflect this route.
The original public imports supply the statement's field, etale-spectrum and point APIs.

Read the direct proof in [Stacks 04JM](https://stacks.math.columbia.edu/tag/04JM),
[02G8(1)](https://stacks.math.columbia.edu/tag/02G8),
[09DT](https://stacks.math.columbia.edu/tag/09DT), and
[0EXM](https://stacks.math.columbia.edu/tag/0EXM). The local literature tex files were absent,
so the tags were read on the Stacks website. Searches through msearch (LeanFinder,
Loogle and grep) and both library roots found the residue-field and normal-closure APIs;
Loogle was unavailable. No existing theorem of the required complete form was found.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.exists_finiteGalois_germ_representative`
(node `lem-exc-field-invariant-germ-representative-construction`): 1 of 1 original holes.
Added holes: none. Remaining holes in the delivered module: none.
Both private helpers are completely proved. This is a proof, not a decomposition.
The module compiles cleanly through lcompile.py. The delivery dry run checks the axioms
of every declaration against propext, Classical.choice and Quot.sound.

## No longer needed

Removed import and proof dependency:
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`,
node `lem-weil-pbc-etale-fibre-discrete-separable-points`.
The proof needs neither discreteness of the fibre nor an isomorphism from an open
singleton to its residue-field spectrum. The finite separable residue-field morphism
alone suffices. No other original dependency was removed: stalk maps and finite
Galois normal closures are still used. No explicit bases or conjugate-generator sets
are required. This pruning concerns this proof's edge; other consumers may still need
the pruned module. The unit `sk-prop-h2` has no realized nodes or steps to bypass.

## Where the brief, the DAG or earlier work was wrong

The original planned route was mathematically sound but stronger than necessary: a
pointed map from the finite residue-field spectrum already suffices to pull back the
section, so there is no need to identify an open component. The updated proof uses
`lem-sc-etale-residue-field-map-etale-tool` (unit sk-thm-br) as a proved source-library
tool; its theorem is sorry-free. The new other-unit dependencies for field-point
factorization and separably closed fields are Mathlib leaves. No unit route changes.

The argument works for L = K, P = K, an algebraically closed base, imperfect bases and
arbitrary characteristic. Factorization through Ks uses the actual algebraicity of
Ω/Ks, derived from Ω/K, and not perfection. A geometric lift supplies the image point
even when X is not affine or quasi-compact. No arbitrary data are chosen from an
unproved existence theorem: every theorem used in the construction is proved.

## Second reading by Q1

1. PASS. Compared the only delivered Lean module with the repository by diff and
   checked the existing theorem signature byte for byte. It is unchanged. There are
   no changed public definitions, instances, or other modules and no change records.
   Restored the existing theorem docstring, whose rewrite was unnecessary.
2. PASS. Compiled the module locally without errors or warnings. A scratch copy with
   `#print axioms` for `factor_separable_embedding`, `pointed_field_neighbourhood`, and
   `AlgebraicGeometry.Scheme.exists_finiteGalois_germ_representative` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound` for each. No sorry, axiom, unsafe,
   opaque, extern, implemented_by, or hollow definition is present. The choice of
   preimages is justified by a proved theorem and injectivity makes them unique.
3. PASS. No statements are split off and no nodes or holes are added. Read both
   private helper proofs: separability is preserved into Ω and up to Ks; algebraicity
   makes Ω/Ks purely inseparable; the field-point factorization preserves K-scalars.
   Checked L = K, P = K, separably closed K, imperfect K and arbitrary characteristic.
   The construction requires no affineness or quasi-compactness of X. Independent
   grep, LeanFinder and Loogle searches were run with alternate factorization queries;
   LeanFinder returned IsSepClosed.lift and separableClosure APIs, which do not alone
   preserve the specified embedding into Ω. A similar stronger helper in
   FieldEquivariantGermsOnePoint is private and cannot be reused. The present argument
   is shorter under this theorem's algebraicity assumption.
4. PASS. Read the proof from stalk joint surjectivity down through the residue field,
   image field, finite compositum, normal closure, and stalk naturality. Read Stacks
   04JM, 02G8(1), and 0EXM against these steps. Each public import supplies a notion
   or instance needed by the existing signature: etaleSpec, IsSepClosure, the finite
   separable etale instance, pointSmallEtale, and FiniteGaloisIntermediateField.
   Both new imports are proof-only. The removed discrete-fibre module and its node
   are completely listed in No longer needed; the two other old proof dependencies
   remain used. The sk-prop-h2 unit has empty realized statement/step lists, and its
   Kummer route is untouched. No shorter reusable public theorem was found.
5. PASS. Compared the delivered node JSON with the repository: only proof,
   proof_deps, and proof_origin differ. Their steps describe the actual Lean proof,
   including the residue-field and purely inseparable Mathlib APIs and the same
   finite-Galois normal-closure construction used by the old dependency. The original
   statement, stmt_deps, source, unit, chapter, and lean signature record are unchanged.

Second-reading changes: restored the existing theorem docstring and added this review.
The proof itself needed no repair. One original hole closed, no holes added or left.
