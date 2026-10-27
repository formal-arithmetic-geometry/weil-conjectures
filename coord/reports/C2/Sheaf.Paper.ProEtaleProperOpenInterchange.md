## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.properOpenInterchange` using the
cartesian compactification theorem, the adjunction mate calculation, boundary
vanishing on constructible finite-Tor generators, and a triangulated vanishing
kernel to extend boundary vanishing to the localizing closure.

The three existing definitions, the theorem statement, and the public imports
are preserved. Private helpers transport finite discrete coefficients to a
small carrier and identify the arbitrary cartesian square with the chosen
pullback used by `proper_open_boundary_zero`.

## Proved and sorry left

Closed the module's sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.properOpenInterchange`.
No holes are added or split off; every private helper has a complete proof.
The item module has zero remaining `sorry` occurrences. The existing dependency
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_boundary_zero`
(node `lem-sfb-proper-open-boundary-zero`) is used as stated, with its existing
hole unchanged. This proves the item from its stated boundary dependency; it
does not claim that the transitive dependency is already sorry-free.

Validation: `lcompile.py` compiled the complete item module cleanly in 40.3 seconds
(exit code 0). The delivery preflight is the remaining gate. The original definitions and public theorem signature were compared
verbatim against the source and are unchanged. The selected imports introduce
no cycle.

## No longer needed

Removed direct proof imports:

- `Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedDetection`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Mathlib.CategoryTheory.Localization.Adjunction`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`
- `Sheaf.Paper.FiniteProperBaseChange`
- `Sheaf.Paper.IntegralProperBaseChange`
- `Sheaf.Paper.ProperBaseChangeRational`

The proof no longer directly uses `lem-sfb-derived-open-square-restriction`
(`Sheaf.Paper.DerivedOpenSquareRestriction`): the cartesian derived counit and
explicit conjugation calculation give the restriction mate for the actual square.
It no longer directly uses `det-sf-determination-localizing`
(`Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus`): the boundary functor's
vanishing kernel gives propagation without constructing a shift-compatible
natural transformation. The source-library derived joint-reflection and
disjoint-support lemmas replace the direct uses of
`det-sf-open-closed-sequence-ring-sheaf` and `lem-exc-open-closed-detection`.
The exact derived adjunctions replace direct uses of
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-termwise-adjunction-homotopy`, and
`sk-prop-sfb-cartesian-coefficients` at this node.
These six obsolete tool approvals are removed from the node's `tool_uses`,
retaining `det-sf-comp-coherence-single`. Underlying tools still used by
existing dependencies are not withdrawn.

No source-library declarations are withdrawn. No module is deleted: dependencies
still reached through other declarations remain in the library.

## Where the brief, the DAG or earlier work was wrong

The boundary theorem uses the chosen scheme pullback, whereas this item uses an
arbitrary dense compactification square. Its finite coefficient convention also
uses a small carrier. Both differences are handled by proved isomorphism
transports without changing either interface.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
