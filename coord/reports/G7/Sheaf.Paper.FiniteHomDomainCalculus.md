## What changed

`Sheaf.Paper.FiniteHomDomainCalculus` now proves the finite scalar-extension flat-model
construction, the finite-Tor endpoint construction, and the reflexive quotient identity.
The proofs use `Etale.exists_etaleScalarFlatModel`, the bounded constructible derived-Hom
corollary, and the existing Noetherian and coefficient-extension results.  The module's
public declarations and target statements are unchanged.  Four upper-level statements
remain as named `sorry`s because their representative coherence calculations need the
larger monoidal comparison route.

The proof imports were reduced to the modules used by the three completed arguments.
No upstream definitions or declarations were changed.

## Proved and sorry left

Closed holes (3):

- `WeilConjectures.finiteHomDomain_flatModel`
- `WeilConjectures.finiteHomDomain_endpoints`
- `WeilConjectures.finiteHomDomain_quotient_id`

Sorries left (4), all existing declarations in this module:

- `WeilConjectures.finiteHomDomain_pullback`
- `WeilConjectures.finiteHomDomain_monoidal`
- `WeilConjectures.finiteHomDomain_scalarCoherence`
- `WeilConjectures.finiteHomDomain_transpose`

No split-off statements or new sorries were added.

## No longer needed

The completed route does not import the following private proof modules from the original
plan:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Paper.EtaleKFlatCriteria`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`
- `Sheaf.CategoryTheory.SystemScalarModel`
- `Sheaf.CategoryTheory.SystemScalarCoherence`
- `Sheaf.Algebra.Homology.ExactPullbackSignedComparison`
- `Sheaf.Paper.PullbackTensorCanonicalShiftUnit`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.CategoryTheory.DerivedCategory.ExactTensorFunctorBraiding`
- `Sheaf.CategoryTheory.ConstantScalarRestrictionTensor`
- `Sheaf.Paper.WitnessCompatibility`

Their corresponding planned nodes remain relevant to the four open declarations and are
not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The flat-model and endpoint steps can be discharged directly by the existing specialized
etale APIs; no ringed-topos pullback or abstract monoidal comparison is needed for them.
The identity quotient follows by reducing `Ideal.Quotient.factor` at a reflexive ideal
inclusion.  The planned pullback, monoidal, scalar-coherence, and transpose steps remain
open and retain their original statements.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
