## What changed

Updated `lean/Sheaf/AlgebraicGeometry/ProEtaleRingSheafChangeAdjunction.lean`.
The parent derived direct-image comparison theorem now obtains its existence part from the
strictly simpler named theorem
`proEtaleRingRestrictionDerivedDirectImage_exists` and proves uniqueness by the existing
`derived_comp_ext` localization extensionality argument. The new theorem is recorded in the
new DAG node `lem-weil-pbc-ring-sheaf-change-adjunction-existence`.

## Proved and sorry left

Closed the sorry in
`AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_existsUnique` by combining
the existence split with a complete uniqueness proof. The new theorem
`AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_exists` remains as one
named sorry because its concrete ringed-topos composition instantiation still needs to be
written. No sorry remains in the final target theorem.

## No longer needed

None. No imports were removed and no existing proof dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original module's remaining hole bundled the concrete ringed-topos composition construction
and its derived uniqueness argument into one theorem. The uniqueness argument is independent and
strictly simpler, so it is split into the proved parent reduction while the construction is
recorded as a separate node. The generic composition theorem also exposes a universe mismatch
when applied directly to `u`-universe pro-etale sites carrying `u+1`-universe coefficient
sheaves; resolving that requires an explicit `ULift` site presentation. A direct mate candidate
likewise still needs the missing acyclicity assertion for restriction of K-injectives, which is
exactly the content of the existence node.

## New nodes

`lem-weil-pbc-ring-sheaf-change-adjunction-existence` records the existence-only derived
comparison theorem and its Stacks Tag 0D6E proof route. Its declaration is in the existing item
module, with the complete source and proof description in its docstring.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
