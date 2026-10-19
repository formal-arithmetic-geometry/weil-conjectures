## What changed

Proved six supporting theorems of `FiniteConstantCoefficientTransport` without changing any
existing signature or definition. Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` for preservation
of colimits by the underlying additive sheaf functor. Restriction of scalars preserves the
underlying additive sheaf exactly; preservation and reflection transfer its finite limits
and finite colimits. The counit of additive sheafification supplies the underlying comparison,
and the triangle identity and sheafification universal property prove its normalization and
uniqueness. Exactness of H follows by composition. The forward open comparison is invertible
as the inverse of an isomorphism. The direct-image comparison is the additive
comparison lifted to module morphisms: its linearity is checked on constant scalars and
extended by local surjectivity of the scalar unit. The defining adjunction identifies the
module direct-image scalar map on constants. Faithfulness and reflection of isomorphisms
then give the unique normalized natural isomorphism.

## Proved and sorry left

Closed six of the original nine holes, all in
`AlgebraicGeometry.ProEtale.StrictTower`:
`constantRingForget_preservesSheafification`, `finiteRestriction_exact`,
`cUnderlying_existsUnique`, `cDirect_existsUnique`, `hOpen_isIso`, and `h_exact`.

Three original holes remain, all attached to node
`def-cbc-finite-constant-coefficient-transport`:
`AlgebraicGeometry.ProEtale.StrictTower.hPullbackInv_isIso`,
`AlgebraicGeometry.ProEtale.StrictTower.hOpenInv_isIso`, and
`AlgebraicGeometry.ProEtale.StrictTower.hR_isIso`.
No holes added and no statements split off.

## No longer needed

Removed the unused proof-only import
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`. None of the six completed
proofs uses its ring-change comparisons or its node
`lem-weil-pbc-ring-sheaf-change-adjunction`. The item node has no `proof_deps` entry for that
module, so no dependency edge needs removing. No module is withdrawn; the unit route
is unchanged. The remaining public imports provide the unchanged statement and
definition interfaces.

Verification against the current published library: the complete module compiles
without this import in 12.2 seconds. All existing signatures and definitions are unchanged.

## Where the brief, the DAG or earlier work was wrong

The item's definition node has empty `proof` and `proof_deps` fields; the theorem docstrings
supply the mathematical arguments. The six proofs here use the existing component APIs
and the Mathlib sheafification universal property directly. No statement defect found.
The remaining pullback comparison needs a complete mate factorization through the normalized scalar comparison; the open comparison needs its
extension-by-zero unit calculation, and the derived direct-image comparison needs the
unit-normalized ring-change and etale-origin continuity factorization. An attempted
pullback proof was removed because its mate/gluing calculation was not fully checked.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
