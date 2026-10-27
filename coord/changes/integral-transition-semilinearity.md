# SheafOfModules.integralOperationsRestrictScalarsZero

## Reason

Complete the pullback transition existence-and-uniqueness proof while preserving every
existing public statement and operation definition. Restore finite semilinearity as
a proved helper. Name the zero-map and finite totalization existence proofs so no
private declaration appears in an existing public definition.

## Old

The pullback and tensor transition characterization theorems contained `sorry`.
There were no public declarations
`SheafOfModules.integralOperationsRestrictScalarsZero`,
`WeilConjectures.integralOperationsFiniteHasMap`, or
`WeilConjectures.unrestrictedIntegralTransition_smul`.

## New

```lean
theorem SheafOfModules.integralOperationsRestrictScalarsZero
    {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{r}} (q : R ⟶ S) :
    (SheafOfModules.restrictScalars.{r} q).PreservesZeroMorphisms

theorem integralOperationsFiniteHasMap
    (W : AlgebraicGeometry.Scheme.{t}) (n : ℕ)
    (P Q : CochainComplex (integralOperationsFiniteModules l E W n) ℤ) :
    HomologicalComplex.HasMapBifunctor P Q
      (MonoidalCategory.curriedTensor (integralOperationsFiniteModules l E W n)) (.up ℤ)
```

The first two declarations prove existing scalar-restriction zero-map and
countable-totalization instances. The restored semilinearity theorem identifies an
explicit linear finite-reduction map with the canonical selected transition by its
unique pure-tensor characterization. Their full signatures are in the two Lean
modules and attached to the corresponding DAG nodes. All three are proved.
Private adjunction mates construct the pullback transition and prove its generator
equation and uniqueness. The original tensor transition hole remains. Existing
library cone, exact-products and functorial-flat-resolution theorems replace
duplicated private proofs in the retained complete invariance and descent argument.

## Users

No existing public definition or statement signature changes. The main item uses
the two new instance proof interfaces and imports the restored semilinearity module.
No other module requires adaptation. The adopted WeilConjectures source tree is
unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralOperationsWellDefined | B4 | Uses the proved zero-map and totalization interfaces and the restored finite semilinearity theorem. |

## Status

landed 20261023T230424-L-3424882 2026-10-23 (merge of deliver/B4/Sheaf.Paper.IntegralOperationsWellDefined)
