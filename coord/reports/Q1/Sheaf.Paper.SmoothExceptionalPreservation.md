## What changed

Proved both holes of `Sheaf.Paper.SmoothExceptionalPreservation`, with unchanged public
signatures. `prime_isUnit_stalk` applies the existing fixed-setting local-unit theorem.
`smooth_exceptional_preservation` descends bounded intrinsic inputs to ordinary etale
complexes and explicitly cancels coefficient realization and the derived comparison unit
in `finiteExceptionalInverseImage`. Its three clauses reuse the source library's smooth
purity, bounded-constructibility and Tor-interval results. A private proof of the precise
cohomological interval uses tensoring with the flat rank-one dualizing line, so the first
clause imposes no finite-Tor hypothesis. All private helpers are proved; no public data or
signature changed. The node proof and dependencies now describe this route.

The smooth-purity step of the unit remains in use. The numerical statements do not need a
canonical Tate orientation: the existing source theorem `exists_dualizingComplex_iso_and_tensor`
has exactly the unoriented rank-one-line conclusion needed here. Its source proof and the
existing smooth preservation theorems replace the longer coverwise and residue-test glue.

## Proved and sorry left

Closed 2 of 2 existing holes:

- `WeilConjectures.PurityFiniteSetting.prime_isUnit_stalk`.
- `WeilConjectures.PurityFiniteSetting.smooth_exceptional_preservation`.

Added zero holes; split off zero statements. No `sorry` remains in this delivery.
The proof uses existing declared dependencies, including ordinary etale smooth duality
and comparison results that have their own proof obligations; it does not claim those
transitive obligations are closed.

## No longer needed

Removed direct proof imports (some remain transitively needed by the existing library):

- `Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint`.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`.
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.
- `WeilConjectures.Compactification.NagataCompactification`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.ProEtaleConstructibleOrigin`.
- `Sheaf.Paper.ComparisonPullbackExact`.
- `Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`.
- `WeilConjectures.SixFunctors.Etale.Derived.Triangulated`.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.
- `WeilConjectures.ConstructibleSheaf.Pullback`.
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`.
- `Sheaf.AlgebraicGeometry.DerivedCategories`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ConstructibleModuleUnderlyingSets`.
- `Sheaf.AlgebraicGeometry.EtaleLocalIsomorphismConstructible`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues`.
- `WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying`.

Removed this node's direct proof dependencies:

- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `thm-nagata-compactification`.
- `lem-weil-valued-dvr-finite-quotients`.
- `lem-sf-proetale-constructible-origin`.
- `lem-sf-comparison-pullback-exact`.
- `cor-sf-ambient-adjoint-discharge`.
- `lem-kun-inverse-image-monoidal`.
- `lem-weil-pbc-constructible-module-underlying-sets`.
- `prop-constructible-pullback`.
- `lem-pod-module-local-constancy-of-finite-underlying`.
- `lem-weil-pbc-finite-locally-constant-module-values`.
- `def-weil-pbc-etale-constructible-sheaf`.
- `def-weil-constructible-subset`.
- `lem-sf-etale-local-isomorphism-constructible`.
- `lem-exc-residue-tor-test`.
- `lem-kun-pullback-constant`.
- `def-weil-exceptional-adjoint-admissibility`.

The source smooth preservation theorems already prove constructibility and Tor bounds by
the flat rank-one dualizing line. Consequently this proof needs no separate residue test,
cover trivialization, local-isomorphism descent, module-underlying-set construction,
constant-residue pullback or scalar-extension admissibility datum. Finite coefficient
finiteness and compactifiability are supplied by their existing interfaces. The short
DVR calculation that ell^n belongs to the defining ideal is proved privately to supply
the invertible-exponent hypothesis without a cyclic import. Descent is reconstructed from the
fixed-module constructible origin and exact equivalence interfaces, avoiding the larger
alternative origin presentation. The ambient adjunction is not part of the theorem's
conclusion and is not needed to compute its already-defined exceptional functor.

Withdrawn obsolete entries from this node's `tool_uses`:

- `lem-weil-pbc-finite-type-over-noetherian`.
- `lem-weil-pbc-locally-noetherian-quasi-separated`.
- `thm-nagata-compactification`.
- `lem-weil-valued-dvr-finite-quotients`.
- `lem-sf-proetale-constructible-origin`.
- `lem-sf-comparison-pullback-exact`.
- `cor-sf-ambient-adjoint-discharge`.
- `lem-kun-inverse-image-monoidal`.
- `prop-constructible-pullback`.
- `lem-kun-pullback-constant`.
- `lem-exc-residue-tor-test`.
- `lem-weil-pbc-constructible-module-underlying-sets`.
- `lem-pod-module-local-constancy-of-finite-underlying`.
- `lem-weil-pbc-finite-locally-constant-module-values`.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The dry run detected a cycle through `PurityDncComparisons`;
that import was removed and its invertible-exponent fact is proved directly, using the
existing DVR theorem and the spectral norm. The planned residue test is unnecessary: the library already
proves the stronger smooth Tor-interval preservation theorem for arbitrary finite rings
with invertible exponent. The source-library rank-one duality theorem handles every etale
complex and the flat-tensor interval lemma handles bounded complexes without finite Tor
amplitude. This shortens the implementation while retaining smooth purity.

The two constructibility conventions have different definitions but agree over the finite
ring; the proof explicitly converts them with the existing comparison theorem. The Tor
predicates likewise require an explicit conversion between homology vanishing and the
canonical t-structure. Edge cases include the empty scheme, zero input, relative dimension
zero, and equal endpoints; no nonemptiness or strict interval hypothesis is introduced.

Validation: the final single-file compile passed cleanly in 21.9 seconds. The delivery
dry run passed compilation, its axiom probe and preflight (CODEX review class).

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
