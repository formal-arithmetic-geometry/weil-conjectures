## What changed

Replaced the sorry in `AlgebraicGeometry.affine_koszul_hom_complex_iso` by a complete
Lean combination of two complex isomorphisms. Its existing signature and public imports
are unchanged. Added proof imports of `AffineFiniteFreeDualComplexComparison` and
`Mathlib.LinearAlgebra.ExteriorPower.Basis`.

Added `Sheaf.Algebra.Homology.HomComplexToSingle`, which constructs the signed internal
sheaf dual and proves the generic comparison from internal Hom into a single target.
The proof constructs an inverse to the unique surviving product projection, proves both
inverse identities, and checks the signed differential using the actual Hom projections.
Added `Sheaf.Algebra.Homology.SignedModuleDualComplex`, a real construction with a proved
square-zero differential. Its Koszul specialization is definitionally the existing dual.
Added `Sheaf.AlgebraicGeometry.AffineFiniteFreeDualComplexComparison`, containing the
remaining affine finite free dualization step as a named public theorem.

The original module explicitly supplies freeness and finiteness of each Koszul term from
the exterior-power basis and composes the generic Hom-to-single comparison with the affine
comparison. This is a decomposition, not an axiom-free proof of the target closure. The
remaining theorem is strictly the finite free sheafification step: it has no product Hom
complex, no single target, and no Koszul sequence, and applies to arbitrary degreewise
finite free chain complexes.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.affine_koszul_hom_complex_iso`
(node `lem-sc-affine-koszul-hom-complex-iso`) by reduction.

Completely proved the new support theorems
`CategoryTheory.signedSheafDual_d_comp_d`,
`CategoryTheory.homComplex_to_single_iso`, and
`ModuleCat.signedDualBoundary_comp`. All definitions contain real constructed data and
refer only to proved square-zero identities.

Added exactly one hole:
`AlgebraicGeometry.affine_finite_free_dual_complex_comparison`
(node `lem-sc-affine-finite-free-dual-complex-comparison`).
No sorry remains in the original module or either algebra/homology module.
Thus one upper hole is closed and one strictly lower hole is added; the net hole count
is zero. The fully proved generic product-collapse calculation is the completed part.

Checked edge cases: the generic product collapse needs no boundedness or freeness and
works for all integer degrees and zero targets. The remaining affine statement admits
zero-rank terms, the zero ring, unbounded chain complexes, and empty affine charts; the
coordinate argument is degreewise and uses no infinite sum. For the Koszul specialization,
empty sequences and exterior powers above the rank have empty basis index types, so the
same finite/free proofs apply.

## No longer needed

None. No existing import is removed and no existing module or node is claimed pruned.
The old definition dependencies remain necessary through statements and constructions.
Regularity, augmentation, scalar Ext, or cohomology-transport modules are not used by this
proof and were not imported by the original module.

## Where the brief, the DAG or earlier work was wrong

The original node gives a valid calculation plan but its proof dependencies contain only
notion definitions; none supplies the finite free coordinate comparison as a theorem.
The explicit generic product-collapse proof implements its first step and the Hom-sign
part of its third step. The remaining comparison isolates its second step and the affine
boundary compatibility without restating the original product Hom conclusion.

The listed Stacks source files are absent from this read-only clone. Read the primary
sources online at Stacks Tags 0BQZ and 01HV. No repository literature file was changed.
No mathematical error, existing interface change, or forced adaptation was needed.

## New nodes

`def-sc-signed-sheaf-dual-complex` records the constructed integer complex with terms
internal Hom(L^(-k),N), differential -(-1)^k times precomposition, and its proved
square-zero identity, in `HomComplexToSingle.lean`.

`lem-sc-hom-complex-to-single` records the fully proved generic collapse of Hom into a
single target, in `HomComplexToSingle.lean`. Its source is the product Hom differential
of Stacks Section 0A8X. Product inverse identities and differential compatibility are
written in Lean, rather than left to a new hole.

`def-sc-signed-module-dual-complex` records the constructed signed dual of any natural
chain complex and its proved square-zero identity, in `SignedModuleDualComplex.lean`.

`lem-sc-affine-finite-free-dual-complex-comparison` records the one remaining comparison
for arbitrary degreewise finite free chain complexes, in
`AffineFiniteFreeDualComplexComparison.lean`. Its complete proof sketch specifies finite
basis evaluations, localization compatibility, precomposition by localized boundary
matrices, the sign, and the zero-degree extension cases.

All four nodes belong to the original chapter and unit. The unit's `realized` lists are
empty; no prescribed unit statement or step has been bypassed. The original node's
`proof`, `proof_deps`, and `proof_origin` now describe the actual Lean reduction.
No change record is needed because no existing signature or definition was changed.

## Second reading by S4

1. Compared the delivered affine Koszul module with the repository version. The target
signature is byte-for-byte unchanged; only proof imports and the proof body changed.
Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py`; the only remaining `sorry` is
the named affine finite-free comparison theorem. No forbidden declarations or hollow
definitions occur. Verdict: pass.
3. Read the three added statements and their DAG nodes. The two generic comparison
statements are strictly below the original target, sourced, and edge cases are covered;
the remaining affine comparison is explicitly split. Verdict: pass.
4. The proof follows the shortest available reduction through the generic Hom collapse,
the exterior-power basis, and the affine finite-free comparison. Imports are all used;
no pruning was found. Verdict: pass.
5. The original node and all new nodes record the declarations, dependencies, and proof
origins used by the Lean proof. The unit route is retained (its realized list is empty).
Verdict: pass.

Changed only this second-reading report section; no Lean statements or definitions were
altered.
