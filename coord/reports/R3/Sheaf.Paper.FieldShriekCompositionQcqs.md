## What changed

Proved `WeilConjectures.sfFieldShriekCompositionRational_existsUnique` in
`Sheaf.Paper.FieldShriekCompositionQcqs`, implementing step 6 of
`lem-zl-field-shriek-composition-qcqs` without changing its route.
A proved private helper `rationalCompositionIso` localizes a compositor of
integral linear functors. Its components are the localization functor's images
of the integral component isomorphisms. Tensor induction proves naturality:
the pure-tensor case is integral naturality, and the zero and addition cases
use bilinearity. Component extensionality proves uniqueness because the raw
rational category has the same objects as the integral category.

The finite compact-support action is definitionally the tensor transport, after
installing its already-proved additive and linear instances. Consequently the
component normalization is reflexive, including the wrapped integral objects.
No definitions, public signatures, public imports, or other modules change.

## Proved and sorry left

Closed one of the original three holes:
`WeilConjectures.sfFieldShriekCompositionRational_existsUnique`.
Added zero holes and split off zero statements.

Two original holes remain unchanged, both attached to
`lem-zl-field-shriek-composition-qcqs`:

- `WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique`: integral
  proper/open construction and common-refinement normalization, steps 1--5.
- `WeilConjectures.sfFieldShriekCompositionQbar_existsUnique`: coefficient
  compatibility and common-stage descent, steps 7--8.

The rational theorem uses the already-defined integral compositor; therefore
its transitive axioms still include the pre-existing integral obligation.
This is a partial delivery of the module, with a complete proof of its
rationalization hole and no replacement assumptions.

## No longer needed

None. No imports or nodes are withdrawn. The tensor-transport proof uses the
existing `Sheaf.Paper.PbcRationalTransport` import. The declarations for the
remaining integral and algebraically closed obligations retain their original
proof-dependency imports and their recorded DAG route. No unit route changes.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. Step 6 can be discharged by a generic
linear-category argument without requiring triangulated exactness in this
proof: the already-fixed integral functors and their natural isomorphism
suffice. No scalar-localization object needs to be replaced, no Karoubi
completion is taken, and no new lattice or arbitrary witness is chosen.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
