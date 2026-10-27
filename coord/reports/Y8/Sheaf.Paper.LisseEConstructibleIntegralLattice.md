## What changed

`Sheaf.Paper.LisseEConstructibleIntegralLattice` now transports the given lisse sheaf
through the explicit continuous module equivalences, uses the existing stratified
lattice and integral gluing theorems, and transports the resulting lattice back.
The original theorem statement and all public imports are unchanged.

`Sheaf.Paper.IntegralContinuousEncodingConstructible` supplies the separate
constructibility comparison needed by this route. It compares the normalized
completed section encoding with the actual continuous coefficient encoding, then
uses the existing integral section and slice local-model comparisons. This theorem
has no rationalization or lattice-existence assertion.

The finite-extension target still obtains its lattice by Lemma 6.8.13. The
stratification and extension assembly are reused in their existing internal-module
realization. No unit statement or unit proof step is bypassed.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.exists_constructible_integral_lattice` is filled by a
complete Lean assembly of the existing stratified lattice and gluing theorems.
The new theorem
`AlgebraicGeometry.ProEtale.integralContinuousEncoding_constructible` has a
complete proof using the existing normalized section/slice comparisons.
There are no `sorry` tokens in either delivered source. Both complete files compiled
together with `lcompile.py --all`. The delivery tool runs its compile and required
preflight before pushing.

Existing imported theorems `integralSectionLocalModels` and
`continuousIntegralSliceModelComparison` retain their own named holes outside
this packet. They are stated dependencies with their existing sources and nodes;
no replacement holes are introduced by this delivery. Hole accounting: one original
hole closed, zero new holes, zero split off.
The compiler and preflight output from `deliver3.py` is the delivery validation record.

Local irreducibility attributes keep the existing coefficient encodings and inverse
images behind their interfaces. The normalized additive coefficient square uses
proved underlying-map equations and faithful forgetting, avoiding expansion of the
completed inverse limit. The ordinary internal lattice assembly is checked before
substitution of the spectral-norm coefficient structures. The compiler timeout was not increased.

## No longer needed

The item no longer directly imports the following proof modules:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`
- `Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `WeilConjectures.CategoryTheory.RingObjects.ContinuousMap`
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`
- `Mathlib.Algebra.Category.Ring.Limits`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.Algebra.Homology.HomComplex`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.AlgebraicGeometry.Cover.QuasiCompact`
- `Mathlib.Topology.NoetherianSpace`
- `Mathlib.AlgebraicGeometry.Properties`
- `Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit`
- `WeilConjectures.Algebra.Homology.DerivedInternalHomShiftRight`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.AlgebraicGeometry.ContinuousCoefficientImmersionRestriction`
- `Sheaf.CategoryTheory.DerivedCountableSumsExact`
- `Sheaf.CategoryTheory.SequenceRelativeHomTelescope`
- `Sheaf.Paper.AdicGlobalDerivedHom`
- `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent`
- `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`

The old item-level proof dependencies no longer used by this assembly are:

- `lem-weil-pbc-continuous-coefficients-immersion-restriction`
- `lem-weil-pbc-module-sheaves-colimits-forgetful`
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
- `lem-weil-pbc-integral-stratified-perfect-characterization`
- `lem-weil-pbc-integral-constructible-hom-sums`
- `lem-weil-pbc-scalar-localization-derived-hom`
- `def-pc-ext`
- `lem-weil-pbc-integral-models-extension-closed`
- `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
- `lem-weil-pbc-reduced-induced-closed-subscheme`
- `def-weil-pbc-continuous-constructible-module`
- `lem-weil-pbc-integral-model-open-closed-pieces`
- `def-weil-proetale-inverse-image`

These are removals from this item's route, not deletion requests. Existing proofs
in the imported gluing theorem still use their own extension, exactness and
devissage dependencies. The internal encoding route does not authorize removal
of any declaration or public import in the adopted source library.

The obsolete item-level `tool_uses` approvals removed from its node are:

- `lem-pc-pre-derived-adjoint-functors-general`
- `prop-pur-kinjective-resolutions-exist`
- `lem-kun-complex-colimit-hocolim`
- `lem-pur-derived-internal-hom-shift-right`
- `lem-pur-rhom-global-sections`
- `lem-kun-derived-countable-sums-exact`
- `lem-weil-pbc-scalar-localization-derived-hom`

## Where the brief, the DAG or earlier work was wrong

The planned direct open-closed induction was not necessary: the library already
contains the full stratified lattice construction and gluing argument for internal
continuous modules. The coefficient categories differ, so merely applying that
result is insufficient; the delivery includes the explicit constructibility
comparison and the scalar-extension/counit assembly. No mathematical statement
was weakened and no definition was repaired.

The source was checked in Bhatt--Scholze, Definitions 6.8.10 and Proposition
6.8.11(3), and the full proof of Lemma 6.8.13. Empty schemes, zero rank, torsion
integral models and nonreduced schemes are covered by the same existing
stratification/gluing and encoding comparisons.

## New nodes

`lem-weil-pbc-integral-continuous-encoding-constructible` states only invariance of
integral constructibility under the actual continuous section encoding and a
coefficient-sheaf isomorphism. Its proof uses normalized integral section local
models and integral slice-model comparison. It does not restate lattice existence,
and its conclusion contains neither a lattice witness nor a rational scalar
extension. There are no change records because no existing signature, definition,
visibility or public import changed.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
