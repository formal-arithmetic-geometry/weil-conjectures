## What changed

Prove `AlgebraicGeometry.Etale.etaleClosedChartExceptionalPreservation` from the
recorded chart normalization, affine-space ambient adjunction, scalar flat model,
pullback/twist Tor window, arbitrary-field open-complement control, and closed-support
Tor-amplitude theorem. The main theorem signature is unchanged. Replace the expanded conjunction
`ClosedChartExceptionalAssertion` by the equivalent Prop structure with the identical
three clauses, to prevent kernel conversion from expanding large functor constructions.
Factor the same comparison equation into the generic definition
`counitNormalizedChartComparison`; the comparison field unfolds to the original assertion.
See `coord/changes/R4-closed-chart-exceptional-assertion-structure.md`.
A downstream search reports no external users; no adaptation is required.

Proved private categorical helpers give the counit-preserving uniqueness assertion
by transporting the left adjunction and applying Mathlib's right-adjoint uniqueness.
The comparison is on the entire derived categories and quantifies over every given
ambient and purity adjunction; it never assumes boundedness of the ambient right adjoint.

For preservation, enlarge the input Tor interval to an ordered interval, restrict to V,
choose the recorded flat constructible representative there, and apply the twist/shift
window along the affine projection. Transport both open-complement conditions from D+
to the unbounded derived functor, then apply closed-support Tor preservation. The output
interval is [a-2r,b-2r+2d+1], including r=0 and empty charts.

Update only the proof, proof dependencies and proof origin of the existing DAG node to
record this argument. Attach the generic comparison predicate to the existing node.
Add no public mathematical lemmas, modules, or nodes. No adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etaleClosedChartExceptionalPreservation`
(node `lem-pur-etale-closed-chart-exceptional-preservation`), the item's sole hole.
Added holes: none. Sorries remaining in the delivered Lean module: none.
Validation: the production item compiled successfully through `lcompile.py` in 33.5 seconds,
with zero warnings, zero local sorries, and default heartbeat and time limits.
The named prerequisite theorems are used as stated; their remaining proofs are separate
existing items. This is one hole closed, with zero split off.

## No longer needed

The direct vector-bundle-purity proof dependency is replaced by the existing, more
specialized `cor-amb-affine-space-adjunction`. The vector-bundle statement remains a
statement dependency and its public import is preserved. The quantified comparison
needs no separate choice of ambient adjoint from `thm-amb-etale-exceptional-adjoint`;
that theorem remains a statement dependency. No unit statement or step is bypassed.

Remove the following redundant direct proof imports:

- `Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `Sheaf.AlgebraicGeometry.EtaleDerivedTensorStalk`
- `Sheaf.AlgebraicGeometry.EtaleStalkTorTest`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.FlatConstructibleTensor`
- `Sheaf.AlgebraicGeometry.OpenSourceComposition`
- `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`
- `Sheaf.AlgebraicGeometry.Sites.TorsionAbelianDirectImageVanishing`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `WeilConjectures.AlgebraicGeometry.BaseChangeDimension`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`

Their lower-level arguments are supplied by the recorded normalization, Tor-window,
flat-model and complement-control dependencies. This prunes the direct proof route;
no claim is made that these modules are globally unreachable. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan uses vector-bundle purity directly, while the already stated affine-space
adjunction gives exactly the required functor. The Tor-window theorem needs an ordered
interval; the input permits an empty interval, so the proof first enlarges [a0,b0] to
[min a0 b0,max a0 b0]. Complement control is stated using the bounded-below derived
functor, while closed-support preservation uses the unbounded functor; the explicit
compatibility isomorphism transports vanishing and constructibility in the required
directions. The mathematical statement needs no correction. The expanded conjunction needed a
representation repair for kernel performance, recorded in the change record above.
Abstracting the identical counit equation over its functors was essential: raising recursion
depth or specifying functors explicitly did not fix kernel conversion. The diagnostic full
compile then passed in 32.4 seconds; no compiler time or heartbeat limit was increased.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
