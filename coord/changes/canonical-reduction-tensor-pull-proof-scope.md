# WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPull

## Reason

The proof opens `CanonicalTensorPullProof` and retains the local irreducibility of
`pullbackTensorCalculus`, keeping its large data folded during normalization. The static checker
flags these scope commands as a possible visible change. The theorem signature
and its public import are unchanged. The new namespace is introduced in new
Sheaf modules only. The attribute is explicitly local; it does not change a shared
definition or a public attribute. No consumer requires an adaptation.

## Old

```lean
theorem canonicalReductionTensorPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (K H : Integral l E V) :
    let μ (W : Scheme.{u}) :
        (d.tensor W).ordinary.tensor ⋙ (calculus l E W).reduction ⟶
          (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
            (calculus l E W).systemClosed.tensor :=
      Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
        (calculus l E W).reductionTensor.hom
    (m.reductionPull f).hom.app ((d.tensor V).ordinary.tensor.obj (K, H)) ≫
        (pull l E f).map ((μ V).app (K, H)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((calculus l E V).reduction.obj K, (calculus l E V).reduction.obj H) =
      (calculus l E U).reduction.map ((ringedTensorPull l E d f).hom.app (K, H)) ≫
        (μ U).app ((ringedPull l E f).obj K, (ringedPull l E f).obj H) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((m.reductionPull f).hom.app K) ((m.reductionPull f).hom.app H))
```

The old proof scope is:

```lean
open CategoryTheory AlgebraicGeometry
attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
```

## New

```lean
theorem canonicalReductionTensorPull
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (o : Operations l E) (m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (K H : Integral l E V) :
    let μ (W : Scheme.{u}) :
        (d.tensor W).ordinary.tensor ⋙ (calculus l E W).reduction ⟶
          (calculus l E W).reduction.prod (calculus l E W).reduction ⋙
            (calculus l E W).systemClosed.tensor :=
      Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
        (calculus l E W).reductionTensor.hom
    (m.reductionPull f).hom.app ((d.tensor V).ordinary.tensor.obj (K, H)) ≫
        (pull l E f).map ((μ V).app (K, H)) ≫
        (pullbackTensorSystemComparison l E f).hom.app
          ((calculus l E V).reduction.obj K, (calculus l E V).reduction.obj H) =
      (calculus l E U).reduction.map ((ringedTensorPull l E d f).hom.app (K, H)) ≫
        (μ U).app ((ringedPull l E f).obj K, (ringedPull l E f).obj H) ≫
        (calculus l E U).systemClosed.tensor.map
          (Prod.mkHom ((m.reductionPull f).hom.app K) ((m.reductionPull f).hom.app H))
```

The new proof scope uses:

```lean
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CanonicalTensorPullProof
attribute [local irreducible] pullbackTensorCalculus
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralOrdinaryCanonicalIsoSquare | unclaimed | Signature and public imports preserved; no adaptation |
| Sheaf.SixFunctors.CanonicalReductionPullTensor | unclaimed | Signature and public imports preserved; no adaptation |

The required related-module batch completed with 143 OK and 9 SLOW; its machine
readable evidence is recorded by the delivery tool for the independent review.

## Status

landed 20261027T210007-L-1642981 2026-10-27 (merge of deliver/G3/Sheaf.SixFunctors.CanonicalReductionTensorPull)
