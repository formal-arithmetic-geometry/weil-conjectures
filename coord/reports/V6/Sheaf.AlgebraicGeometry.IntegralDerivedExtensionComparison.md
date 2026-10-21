## What changed

Filled all six theorem proofs in
`Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison`. The actual coefficient inclusion
is definitionally the continuous integral inclusion after equipping E with its induced norm;
the existing exactness theorem then applies. The actual derived functor and its specified
counit have the existing left derived universal property. Mathlib transports triangulatedness
and additivity along the existing canonical comparisons, and reflects additivity through the
faithful bounded-constructible inclusion. Shift compatibility uses the compatibility theorem
for the transported shift and its inverse. The final comparison transports distinguished
triangles along the specified compatibility isomorphism.

All existing declaration signatures, definitions, instances and public imports are unchanged.
The node proof now records direct derived uniqueness and reuse of the already proved integral
bounded-constructible triangulatedness instance. Its statement and the unit route are unchanged.
Single-file lcompile.py passed without warnings (19.7 seconds); delivery performs the axiom
probe and preflight checks.

## Proved and sorry left

Closed 6 original holes, all in namespace `AlgebraicGeometry.ProEtale` and attached to
`lem-sfb-integral-derived-extension-comparison`:

- `integralExtension_exact`.
- `integralExtensionDerived_isLeftDerived`.
- `integralExtension_triangulated`.
- `boundedConstructibleIntegralExtension_additive`.
- `boundedConstructibleIntegralExtensionCompatibility_commShift`.
- `integralDerivedExtension_comparison`.

Zero holes remain in the item; zero holes added and zero statements split off. Existing
imported theorems retain their own proof dependencies; this is a proof from the existing
library, not a claim that the entire imported closure is sorry-free.

## No longer needed

Removed three unused private proof imports:

- `Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact`:
  `def-sfb-left-derived-exact` is not needed as a separate theorem. The existing comparison
  already applies Mathlib leftDerivedUnique to the actual upstream derived functor and its
  own counit. Its universal property is proved directly from the recorded upstream instance.
- `Sheaf.Paper.IntegralConstructibleSerre`.
- `Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`.
  The latter two are not needed as direct proof imports or direct node dependencies because
  the retained `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` import already proves
  their coefficient-specific conclusion. Both remain indirect dependencies of that theorem;
  no claim of globally pruning either module is made. Their top-level tool_uses entries are
  removed from this node because this proof now uses the proved specialization.

No declarations or modules are withdrawn. All other planned dependencies are used, either
for the existing interfaces, exactness, termwise derived functor, or the triangulated source.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The recorded `def-sfb-left-derived-exact` declaration concerns
the separate total-tensor-derived interface, whereas this item already defines its canonical
comparison directly by the same Mathlib uniqueness construction for the specified upstream
left derived functor. Using the existing universal property directly avoids that unused
import. Step 4 was already proved by the coefficient-specific triangulatedness instance.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
