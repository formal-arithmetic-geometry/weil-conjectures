## What changed
Proved `AlgebraicGeometry.Etale.exists_higher_image_affine_class_eq_zero` by reducing it to local eventual vanishing, finite affine refinement, filteredness, transition coherence, and sheaf separatedness. Added `HigherDirectImageLocalClassVanishing.lean` with the strictly smaller local statement left as `sorry`.

## Proved and sorry left
Closed the original hole `AlgebraicGeometry.Etale.exists_higher_image_affine_class_eq_zero` by a checked reduction. Added one hole, `AlgebraicGeometry.Etale.exists_higher_image_local_class_eq_zero` (node `sbc-lem-higher-image-local-class-vanishing`). This is a decomposition: one hole closed, one added, net zero; the original result still depends on sorryAx through the local theorem and existing dependencies. No other holes or definitions were added.

## No longer needed
Removed direct proof imports `AbelianHigherDirectImagePresheaf`,
`EtaleComplexCohomologyLimit`, `EtaleQcqsCofinalFiniteCoverings`,
`InjectiveModuleAbelianAcyclic`, and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
The finite-cover dependency `lem-weil-pbc-etale-qcqs-cofinal-finite-coverings` is bypassed
by Mathlib compactness and the open ranges of etale morphisms; no affine refinement
of the witnessing cover is needed. The other removed imports remain reachable
through the local theorem or transition definitions.

All old proof_deps absent from the new affine proof are:
`lem-weil-pbc-filtered-category-exists-directed-final`,
`lem-weil-pbc-colimit-constant-connected-diagram`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-injective-module-abelian-acyclic`,
`lem-weil-pbc-etale-cohomology-limit-complex-systems`,
`sbc-lem-higher-direct-image-presheaf`,
`lem-weil-pbc-sheaves-colimit-sheafification`, and
`lem-weil-pbc-etale-qcqs-cofinal-finite-coverings`.
All except the last are retained as proof_deps of the local theorem. This report
asserts direct dependency pruning only, not removal from the whole target closure.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof described the complete local cohomology-continuity argument inline. That argument is strictly smaller and is now isolated as a local theorem, allowing the affine finite-cover assembly to be fully proved here.

## New nodes
Added `sbc-lem-higher-image-local-class-vanishing`, stated in `HigherDirectImageLocalClassVanishing.lean`; it captures the local continuity and sheafification part of the source proof.


## Second reading by J2

1. PASS: compared both Lean modules and both node records with the repository.
   The existing affine theorem signature is byte-for-byte identical. Its docstring
   and all public statement imports are unchanged. The other theorem and its node
   are new; no existing statement or definition changed and no change record is needed.
2. PASS: both files compile locally through lcompile.py in import order. The only
   new sorry is the named local theorem, whose proof is exactly `by sorry` and has
   its source, natural-language proof, and matching node. No axiom, unsafe, opaque,
   implemented_by, extern, hollow definition, or arbitrary witness definition occurs.
   Scratch #print axioms checks show only propext, Classical.choice, Quot.sound,
   and sorryAx. The affine reduction also uses the existing open transition-coherence
   theorem; it is not claimed axiom-free.
3. PASS: read the local theorem against Stacks 09Z1, 03Q8, 0EZM, and 03FD.
   Its conclusion is local eventual vanishing, strictly a part of the affine argument:
   it neither selects a common stage nor uses compactness or separatedness to conclude
   global vanishing. Checked empty V, q=0, q<0, zero coefficients/section, and a
   singleton index. Cofilteredness ensures nonempty indices even for an empty cover.
   Repeated leanfinder, loogle, and grep searches with different queries, plus rg in
   both library roots and the source checkout. Mathlib local sheafification lemmas
   supply ingredients but not higher-image continuity. Existing abelian local and
   affine section lemmas require a directed preorder, coefficient-system data, and
   nonnegative degree; reducing this theorem to them requires reindexing and a
   natural derived module/abelian comparison, not a few-minute application.
   The upstream module cohomology-presheaf comparison likewise does not supply
   eventual vanishing by itself. No duplicate theorem was found.
4. PASS: traced the finite-subcover, wideCospan, naturality, contravariant transition
   coherence, and module-hom separatedness arguments. Proof-only imports are plain
   imports; the public transition import supplies the signature. The local module's
   imports record the intended continuity ingredients. The unit sk-lem-failure-field
   retains its route; this item is below its level and bypasses none of its steps.
   Its realized statement/step lists are already empty in the repository: this
   pre-existing blueprint coverage defect is reported, not silently repaired here.
   Completed the old proof_deps pruning list and corrected the false implication
   that every removed module remains a dependency of the local theorem.
5. PASS: affine node proof/proof_deps/proof_origin match the checked assembly;
   the new local node records the source continuity argument, all required creation,
   blueprint, search, statement, and Lean fields. Existing statement fields are
   unchanged. The new node's Lean statement matches the new theorem.

Second reading changed the report only: explicit one-for-one decomposition accounting,
complete direct dependency pruning, and these review verdicts. The correct Lean
proofs and declarations were left unchanged.
