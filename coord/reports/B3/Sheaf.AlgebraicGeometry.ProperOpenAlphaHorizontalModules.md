## What changed

Proved `AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_horizontal` with its
statement unchanged. Restriction detects maps to extension by zero by transporting
to sheaves of B-modules, composing with the existing monomorphism from extension by
zero to direct image, and using the restriction/direct-image adjunction.

Added `Sheaf.AlgebraicGeometry.ProperOpenAlphaRestriction` with the canonical inverse
open unit `moduleOpenUnitInv` and the proved one-square normalization
`singleAlpha_restriction`. The proof expands the actual beta/projector/compositor
construction, restricts its projector/open-compositor part and beta part separately,
and identifies the factored square by existing inverse-image compositor coherence.
Horizontal pasting then follows from naturality, inverse-unit composition, and square pasting.

All new imports used only in proofs are private. The original public import,
existing declaration signatures, and the tower/derived transport proofs stay intact.
The local irreducibility declarations were moved before the new proof to keep the
large inverse-image constructions abstract. The final inverse calculation uses
explicit left/right inverse equations rather than simplifying representations of
inverse natural-isomorphism components. No shared module or interface changed.
The restriction calculation is first stated for arbitrary factorization arrows,
then specialized to the pullback and its clopen lift. Alpha is kept as an abstract
map with its factorization equation during the calculation; the public theorem
supplies the actual definition and its proved factorization equation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_horizontal`
(`lem-cbc-proper-open-alpha-horizontal-modules`).

Also proved the new theorem
`AlgebraicGeometry.ProEtale.StrictTower.singleAlpha_restriction`
(`lem-cbc-single-alpha-restriction`). No holes added, no split-off unfinished
statements, and no `sorry` remains in either delivered module. The inverse open unit
is a concrete inverse of the specified, already proved invertible unit.

Validation: `lcompile.py --all` compiled both delivered files cleanly: restriction
in 24.1 seconds and the item in 30.8 seconds, each below the 60-second limit.
The original horizontal signature and the existing tower/derived proof tail were
also compared byte-for-byte with the shared source and are unchanged.

## No longer needed

No original import or existing module was removed. The experimental private import
of `EtaleClopenMateNormalization` was removed when the direct component restriction
calculation replaced its generic unit-word route. The planned direct dependency
`lem-weil-pbc-proetale-ringed-open-closed` is unnecessary for this horizontal proof:
restriction detection uses the proved monomorphism `j!` to `j*` and adjunction.
This does not withdraw that node or claim it is unused by its other consumers or by
underlying constructions.

The original normalization and projector dependencies are used in the new proved
single-square lemma. They are replaced by that lemma as direct proof dependencies
of the horizontal node. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The planned open/closed image argument has a shorter
route through the existing `mono_openImmersionLowerShriekToLowerStar_app` theorem.
The corresponding semilinear restriction theorem is already proved, but importing
its module here would create a cycle through the proper/open calculus. Its square
factorization proof informed the fixed-coefficient calculation, and its component
argument supplies the elementary categorical
strategy. The final proof uses private generic naturality and word-combination
helpers and imports none of the cyclic semilinear modules.
Empty opens, identity opens, and the zero ring require no extra assumptions: the
unit, projector, and naturality identities used in the proof cover them.

## New nodes

`lem-cbc-single-alpha-restriction` records the proved one-square restriction formula
in `Sheaf.AlgebraicGeometry.ProperOpenAlphaRestriction`. It realizes steps 2--3 of
the existing horizontal node, is strictly simpler than horizontal pasting, and
introduces no remaining obligation. A dependency-path audit found no route back
from the new restriction node to the horizontal parent. The existing horizontal
node has updated
`proof`, `proof_deps`, and `proof_origin` matching the actual proof. No change record
is needed because all existing statements and definitions are unchanged.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
