## What changed

Proved `WeilConjectures.PointDerivedHom.point_exact_extension_sections` in
`Sheaf.Paper.PointExactExtensionSections`, preserving its statement and the public
`ExactExtensionSections` definition. All added helpers are private and proved.

The integral case reuses the existing
`integral_point_coefficient_adjunction` declaration, including its exactness,
normalized adjunction and constant-value bijections. The finite case constructs
the constant-module adjunction by final-object evaluation and module
sheafification, then composes it with the proved tensor/restriction adjunction in
`SheafRingCoefficientOrdinaryAdjunction`. The latter module is privately imported
with `import all` to reuse its universe-independent proved implementation,
without changing any public definition or exposing private helpers to consumers.
Tensor along the identity is naturally isomorphic to the identity by uniqueness
of left adjoints, proving finite extension exactness. Exact point evaluation
followed by scalar restriction proves finite sections exactness.

An additive adjunction gives the equivalence of unbounded cochain maps via
`Adjunction.mapHomologicalComplex`. A private construction transports actual
homotopy witnesses componentwise in both directions; its commutation equations
follow from additivity and both naturality laws. The finite exponent n is
written m+1 using the existing hypothesis 1 ≤ n.

Updated the assigned DAG node's proof, proof dependencies and proof origin to
match this route. No statement or definition repair, consumer adaptation or new
node is needed. The assigned node realizes no fixed unit proof step, and the
new dependency routes were checked for cycles. Universe-related instance
selection adjustments are local to this module.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.PointDerivedHom.point_exact_extension_sections`
(node `lem-pod-point-exact-extension-sections`). No holes remain in the item.
Added 0 holes and split off 0 statements. Every new private helper is fully proved.
The existing imported integral coefficient and point-sections results remain
prerequisites; this delivery does not claim to close their holes.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.SecSmoothPurity.ProEtaleFiniteConstantSections`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Mathlib.Topology.Algebra.Valued.LocallyCompact`

The following old direct proof dependencies are replaced by the existing
integral-point coefficient adjunction and are no longer separately used here:

- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-completed-constant-sheaf-reduction`
- `def-weil-completed-integral-coefficients`
- `lem-weil-valued-dvr-finite-quotients`
- `lem-pur-proetale-finite-constant-sections`
- `lem-weil-pbc-continuous-coefficients-immersion-restriction`
- `def-weil-pbc-sheafification` (the proof uses the more specific module
  sheafification interface instead).

Removed obsolete top-level `tool_uses` entries for the DVR, completed reduction,
finite constant sections and continuous coefficient restriction nodes; retained
the exact point-sections entry. Some removed direct dependencies remain
transitive prerequisites of the reused integral coefficient theorem. No module
is withdrawn or claimed globally unreachable; there is no global module pruning.
Public imports and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan is mathematically applicable, but repeats integral coefficient
arguments already bundled in
`Sheaf.Paper.IntegralPointCoefficientAdjunction`. Reusing that declaration is
shorter and leaves the finite-level argument and actual homotopy equivalence
as substantive work here. No false statement or source-library defect was found.

## Second reading by K9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
