# Open-cover cohomology proof context

## Reason

Stage-3 preflight requires a change record for the added elaboration options and
reordered declaration in `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection`.
The module is held by K3. The delivery fills its ten existing theorem holes and
adds proved private helpers for slice extensionality, generic slice composition,
and exactness of module restriction. No existing public signature, definition,
instance body, declaration attribute, or public import changes.

## Old

The file began its public section with:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
```

`module_detection` occurred after `end Derived`, following `cohomology_detection`.
All ten theorem proofs were `by sorry`.

## New

The public section now begins with:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w v
open CategoryTheory CategoryTheory.Limits Opposite
```

These options control elaboration in this file and install no global instance,
simp rule, notation, or attribute for consumers. They support the concrete
site-equivalence and module-category proof terms. Every pre-existing definition
and instance retains its original body.

`module_detection`, with its original docstring and exact signature, is moved
before `section Derived`. Thus `cohomology_detection` can apply it to the homology
sheaf and transport zero objects along the canonical `chi` isomorphism. The
`include hFinite` context and all existing derived theorem signatures are retained.
All ten holes are filled; no public declaration is added and no hole is split off.

The private `sliceInverse` constructs its object and map directly from structure
maps and their compositions. It does not choose data from an existence theorem.
The private generic composition proof avoids expensive unfolding of concrete
site-equivalence records. The complete final module compiled in 20.6 seconds,
exit code 0, with no warnings.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection
--uses AlgebraicGeometry.OpenCoverCohomology.module_detection` reports zero current
Lean downstream modules and one textual user, the item module itself. Searches of
both library roots find no external import of the item. The DAG parent proofs
still require this node, so the item is retained with its Lean attachment and
all three declared proof-dependency modules.

No consumer adaptation is required because the public interface is identical.
No adopted source-library module or target statement is changed. The blueprint
unit route is retained, and no target statement review is reopened.

## Status

landed 20261023T231655-L-3632200 2026-10-23 (merge of deliver/K3/Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection)
