## What changed

Completed `AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`
in `Sheaf.SixFunctors.ProperImageLocalizingProper`, retaining its exact statement and all
existing public imports. The generic restriction theorem and both predicate definitions
are unchanged. Added proved private glue for scalar-equivalence transport, geometric
fibre bounds, rational/integral coefficient preservation, and the lifted finite discrete
coefficient model. The six coefficient cases now follow from the stated finite, rational
and integral dependencies. Updated the existing node proof to record the actual route.

Private `import all` uses existing proved helpers: `preservesCofanOnClass` from
IntegralProperDirectSums, `proper_integral_constructible` and `bounded_transport_iff` from
IntegralProperCohomologicalBounds, and `constantModelBoundedConstructible_eq_rational`
from ProperHeartConstructibleCohomology. These helpers themselves have complete proofs;
none is a new axiom or hole. The rational comparison is the finite-descent theorem's
predicate comparison, and integral constructibility is the integral proper theorem
transported through its existing normalized coefficient-ring comparison.

The geometric dimension bound uses the assigned finite-type fibre-bound theorem, then
pullback pasting and the existing field-extension dimension inequality. The scalar
transport preserves the actual coproduct universal property and reflects colimits along
the target equivalence. Finite coefficients are transported by explicit pointwise
ring-sheaf maps between A and ULift A. Empty sums, empty schemes and the zero finite ring
are covered; no nontriviality or regularity assumption is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.proper_image_localizing_proper_coefficients`
(node `det-proper-image-localizing-proper`). The item now has zero `sorry`; zero holes
added and zero split off. `proper_image_localizing_proper` was already proved and stays
proved. This is a proof from the project's existing named dependencies, some of which
still rest on their own recorded holes. No claim is made that the transitive closure is
axiom-free yet.

Validation: the complete item compiles without diagnostics through lcompile.py
(30.3 seconds). All Lean lines are at most 100 characters. Only the existing node
fields proof, proof_deps and proof_origin change.

## No longer needed

Removed redundant private imports:
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
`Sheaf.Paper.CondensedModuleDerivedPushpull`,
`Sheaf.Paper.IntegralProperBaseChange`,
`Sheaf.Paper.LocalizingAdmissibleCoefficients`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.
Their necessary declarations remain available through the dependencies actually used.
No mathematical dependency of the planned proof is pruned: in particular the integral
proper theorem remains used by its existing proved coefficient-transport helper. No
module is withdrawn and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient cases require two interface conversions that were implicit in
the prose: rational proper preservation uses the locally finitely presented predicate,
whereas the item uses finite constant models; the finite theorem fixes the discrete
coefficient model in the scheme universe. Existing finite-descent predicate comparisons
and explicit ULift coefficient maps supply these conversions. The stated dimension
bound concerns ordinary residue-field fibres; pullback pasting and the field-extension
dimension inequality supply the geometric bound needed by coproduct theorems.
The original module already compiles against the current server build despite its
historical rework/quarantine row. It is preserved and proved, not withdrawn.

Additional existing tools recorded in the node are
`lem-sfb-base-coefficient-condensed-identification`,
`lem-sfb-condensed-coefficient-iso-constructible`,
`def-sfb-derived-comap-lower-star-iso`,
`lem-sf-field-extension-dimension-upper-bound`,
`lem-integral-coefficient-ext-comparison`, and `sk-thm-sfb-qlbar-two-colimit`.
They implement coefficient presentations and geometry needed by this unit's original
route. No new nodes, definitions, statements or change records are required.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
