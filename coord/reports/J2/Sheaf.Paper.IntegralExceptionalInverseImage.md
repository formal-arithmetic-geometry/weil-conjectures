## What changed

`Sheaf.Paper.IntegralExceptionalInverseImage`: construct the quotient-ring sequence
isomorphism and restrict modules along it. Compose this with the existing ringed
sequence-site and coefficient-system equivalences. Compare the resulting functor
with the existing coordinate functor using identity maps on sections and the
specified horizontal-transition equation. Transfer equivalence and additivity.
The proved auxiliary lemmas `integralExceptionalSiteWeakSheafify`,
`integralExceptionalSiteAbSheafify`, and
`integralExceptionalSiteAbLocallyBijective` specialize existing site instances to
the fixed coefficient universe. They are attached to the item node. The new proof-only imports are `Sheaf.Paper.CoefficientEvaluationModels` and
`Sheaf.CategoryTheory.SystemRingedSequenceSite`.

The scalar-composition comparison is unchanged. Private helpers calculate its
sections using a componentwise congruence proved equal to equality transport.
Abstract section predicates and pointwise generic calculations on module maps avoid
expanding large concrete section types. These predicates use the underlying
additive-group carriers so scalar actions are forgotten before carrier comparison.
The scalar ring square is checked as an equation of component ring morphisms.
The new construction and proof sections respect local irreducibility settings.
The derived constructions also respect those settings and treat the coordinate
functors locally as irreducible. The Brown support proof explicitly installs its
proper-image additive instances under this setting. Successor bounds are typed as `n ≤ n + 1` in the private
transition statements and applications, avoiding repeated conversion through the
concrete quotient constructions. The principal-ideal transport proof uses explicit
ideal-map lemmas instead of broad simplification. No public definition,
declaration signature, target statement, or source-library declaration changes.


## Proved and sorry left

Closed: `WeilConjectures.integralExceptionalCoordinates_properties` (one of the
two holes in the current V6 source). No new holes or split statements.

Remaining: `WeilConjectures.integralExceptionalInverseImage_on_ctf`, on node
`def-pur-adic-exceptional-system-realization`, unchanged. The previously landed
`integralExceptionalSupport_exists` proof is preserved and is not counted here.

Axiom audit: `integralExceptionalCoordinates_properties` uses exactly `propext`,
`Classical.choice`, and `Quot.sound`. The complete module compiled in 59.5 seconds through `lcompile.py`.
Delivery checks follow.

## No longer needed

No existing imports, nodes, or modules are withdrawn. The coordinate proof
uses the stated sequence-site equivalence and the adjacent/all-transition bridge.
No new levelwise gluing obligations are introduced.

## Where the brief, the DAG or earlier work was wrong

The live source incorporates V6's support-existence proof and has two holes.
No mathematical defect was found in the original statements. The coordinate
proof needs explicit section formulas for the comparison isomorphisms; the
private helpers supply these through abstract predicates and module-map
calculations, avoiding the expanded concrete section statement types. The unit
route and the original finite-Tor comparison obligation are retained.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
