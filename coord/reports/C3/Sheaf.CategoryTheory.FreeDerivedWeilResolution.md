## What changed

Proved all four outstanding theorems in
`Sheaf.CategoryTheory.FreeDerivedWeilResolution`, preserving every public signature,
public import, and existing definition/instance body.

The heart properties use the existing proved IsoAlgebra construction. The derived
forgetful functor reflects isomorphisms by its homology comparison and preserves
coproducts by the proved general exact-derived coproduct theorem. The resolution is
constructed explicitly: the actual integer structure iterates identify its summands;
the shift is a free morphism; finite sums for positive and negative indices give an
underlying splitting. Reflection gives short exactness in the fixed-pair heart.
Fully faithful localization whiskering descends the difference and canonical connecting
maps. The counit normalization is proved for the specified localized adjunction.
Transport of the short-exact triangle supplies the triangle for every derived object.
The final localizing-closure conclusion follows by closure under distinguished cones.

Private proof helpers have complete proofs. No new public declarations, modules,
statements, or definition repairs were needed. Updated the existing node's proof route,
proof dependencies, proof origin, and obsolete tool approvals. The unit route is retained:
`sk-prop-sf-biduality-general` has no realized statement or steps to bypass.

Validation: remote single-file compilation succeeds. Axiom checks for all four theorems
show exactly `propext`, `Classical.choice`, and `Quot.sound`. The final delivery checks
also compile the packet and verify declaration preservation.

## Proved and sorry left

Closed four original holes:

- `CategoryTheory.Endofunctor.IsoAlgebra.freeWeil_heart_properties`.
- `CategoryTheory.Endofunctor.IsoAlgebra.freeWeil_derived_properties`.
- `CategoryTheory.Endofunctor.IsoAlgebra.exists_freeDerivedWeilResolution`.
- `CategoryTheory.Endofunctor.IsoAlgebra.freeWeil_mem_localizingClosure`.

All realize `lem-sf-free-derived-weil-resolution`. Holes added: zero. Holes left: zero.
This is a proof, with no split-off obligations.

## No longer needed

Removed the private imports
`Sheaf.CategoryTheory.FixedPairDerivedForgetComparison` and
`Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`.
Removed direct proof dependencies and obsolete tool approvals
`lem-sf-fixed-pair-derived-forget-comparison` and
`lem-kun-grothendieck-derived-coproducts`: the existing upstream heart facts and the
proved `lem-pur-exact-derived-coproducts` suffice. The latter uses a different already
proved coproduct implementation. No declarations or modules are withdrawn; this
packet makes no claim that these removed direct inputs have no other target consumers.
The remaining planned dependencies, including the short-exact-sequence triangle, stay.
Experimental redundant private `import all` statements for
`WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra`,
`WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`,
`Mathlib.CategoryTheory.Limits.HasLimits`, `Mathlib.CategoryTheory.NatIso`, and
`Mathlib.Algebra.Homology.DerivedCategory.ShortExact` were also removed.

## Where the brief, the DAG or earlier work was wrong

The planned invocation of the fixed-pair comparison is unnecessarily strong: its
available heart hypotheses identify the Grothendieck indexing universe with the hom
universe, whereas this module deliberately allows independent universes `w` and `v`.
The upstream IsoAlgebra Grothendieck theorem works directly in universe `w`. Shrinking
AB4 to the integer indexing universe supplies exact free induction. No public statement
needed changing.

The old theorem docstrings describe the original planned dependencies. The actual
proof and updated DAG instead use the direct heart construction, homology detection,
and the existing exact-derived coproduct theorem. All explicit summand formulas,
negative indices, canonical counit, and canonical connecting-map normalizations are
proved unchanged. There were no false statements, forced adaptations, or new nodes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
