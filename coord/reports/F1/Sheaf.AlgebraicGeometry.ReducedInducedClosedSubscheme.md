## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`
without changing its signature. Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic`; both pass the import-cycle check.
Updated the existing node's proof and proof dependencies to match the Lean proof.
No new modules, declarations, nodes, or signature changes are delivered.

## Proved and sorry left

`AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`: all eight
conjuncts proved; no sorry remains or is added. The section condition follows by converting
zero on the reduced subscheme to an empty inverse-image basic open. Affine uniqueness uses
vanishingIdeal/zeroLocus and radical ideals. The structural facts reuse proved source and
Mathlib infrastructure. For uniqueness, `Scheme.Hom.ker_eq_vanishingIdeal` identifies the
kernel, and the closed-immersion lift is an isomorphism; monicity proves uniqueness.
Local compilation passes without warnings. The delivery dry run also checks declaration
axioms and compilation on the server.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.Coherent` (node `pqf-def-coherent`).
The proof no longer directly needs nodes `lem-weil-pbc-spec-tilde-free-module`,
`lem-weil-pbc-spec-module-tilde-sections`, `lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-affine-open-spec-points`, `def-weil-affine-spectrum`, `def-pc-scheme`,
and `def-weil-closed-immersion` as proof dependencies. Their definitions that occur in the
statement remain available through the unchanged public imports and statement dependencies.
The three tilde nodes are Mathlib declarations in `Mathlib.AlgebraicGeometry.Modules.Tilde`;
no new proof imports of that module are required. Affine scheme definitions are already
available; no unit statement or unit proof step is bypassed by this local simplification.

## Where the brief, the DAG or earlier work was wrong

The existing node correctly identifies proved source infrastructure for reducedness.
The source now also proves `Scheme.Hom.ker_eq_vanishingIdeal`, closing the ideal-equality
step directly. The original nine-step plan need not be reimplemented: IdealSheafData already
encodes affine localization, and the kernel-based extension to all opens combines with
basic-open vanishing on reduced schemes. The statement and the unit route are unchanged.

## Second reading by F1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports differ.
2. Compiled the module locally with `lcompile.py`; it succeeds with no warnings. The module has no remaining `sorry`, forbidden declarations, or hollow definitions; the proof uses only the permitted source axioms through its dependencies.
3. Checked the statement and proof route against the existing node and searched the repository/source infrastructure. No new statement was split off, and the existing theorem remains unchanged and appropriately strong.
4. Verified pruning: `Sheaf.AlgebraicGeometry.Coherent` is removed, while the two proof-only IdealSheaf imports are required by the proof. The unit route and all realized unit steps remain represented by the existing theorem and dependencies.
5. Checked the DAG node: its Lean declaration, proof description, proof dependencies, and origin remain consistent with the delivered proof; no node or statement changes are introduced.

Changed only the module proof/imports and this report; no mathematical statements or definitions were changed.
