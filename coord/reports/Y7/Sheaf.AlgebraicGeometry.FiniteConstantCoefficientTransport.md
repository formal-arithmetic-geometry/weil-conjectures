## What changed

Filled `AlgebraicGeometry.ProEtale.StrictTower.hOpenInv_isIso` and
`AlgebraicGeometry.ProEtale.StrictTower.hR_isIso` in
`Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport`.

The proof constructs the equivalence from modules over the constant ring sheaf to
fixed-ring module sheaves by restriction along the sheafification unit. The existing
normalizations identify `C` and its direct-image square with ordinary scalar
restriction. The same equivalence now supplies the private proof of
`cPullback_isIso`, preserving the existing `hPullbackInv_isIso` theorem.

For open extension, the canonical localization comparison reduces the scalar mate to
`openExtensionScalarMap`. The site mate is identified by
`openComparison_unit_normalization`. The mate pasting laws combine these two
isomorphisms into the specified `hOpenInv`, including its original normalization.

For derived direct image, the source classical right-derived comparison theorems
transport acyclicity through the equivalence. The qcqs site-acyclicity theorem and
`rightDerivedLowerStarRestrictScalarsIso` show that `H` sends injectives to
module-direct-image acyclic objects. The acyclic-object criterion then proves
invertibility of the precise base-change transformation defining `hR`.

All added helper declarations are private and proved. The private `scalarUnit` has
its original defining term and an explicit type; it is now a definition whose
unfolding can be controlled. This elaboration change is recorded in
`coord/changes/Y7-finite-constant-scalar-unit.md`. The existing public statements,
definitions, visibility and public imports are unchanged. No source-library file or
target statement is changed. The node's proof, proof dependencies and proof origin
now record the implemented argument.

Validation: the complete item compiled successfully with zero local `sorry` bodies
and no warnings. The sandbox set check compiled the item in 52.9 seconds and its
unchanged private-helper consumer, `FiniteOpenBaseChangeNormalized`, in 8.1 seconds.
A source comparison found all 30 existing public signatures unchanged, with no
public declaration added or removed. The temporary consumer copy is not delivered.

## Proved and sorry left

Closed two of the two original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.hOpenInv_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.hR_isIso`.

Both belong to `def-cbc-finite-constant-coefficient-transport`.
Added holes: zero. Remaining holes in the item: zero. Split-off statements: zero.
The previously proved `hPullbackInv_isIso` remains proved. This is a proof delivery,
not a decomposition into new unfinished statements.

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce`. The old private
`fixedPullbackUnit_isIso` argument is replaced by transport through the explicit
constant-ring equivalence. No downstream declaration refers to that private helper.

The final proof also avoids importing
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage`: its short,
proved underived mate calculation is reproduced privately from the source
conjugation theorem and the scalar-adjunction triangle identity. Its derived
comparison and K-injective normalization are not needed for this argument.

No node or library module is withdrawn. These modules remain wherever other
consumers need them. The unit's statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The node previously had an empty proof and proof-dependency list, so it did not
supply the argument for either remaining invertibility assertion. The updated
proof uses the existing normalized source APIs and adds no mathematical hypothesis.

An invertible pullback square alone does not imply that its open-adjunction mate is
invertible. The open proof checks the unit normalization and scalar restriction
model explicitly. Likewise scalar restriction need not preserve injectives; the
derived proof transports acyclicity instead. The constant-ring equivalence works
for arbitrary `B`; no finiteness, flatness, connectedness or nonzero-ring condition
is imposed.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
