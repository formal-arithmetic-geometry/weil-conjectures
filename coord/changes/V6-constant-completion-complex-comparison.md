# CategoryTheory.ConstantCompletion.reductionTowerComparisonComplex

## Reason

The assigned module exceeded the 60-second compile limit after adding proofs. Profiling
isolated about 14 seconds of kernel checking in the existing derived-tower comparison
statement. Its two applications converted the complex of a composite functor into a
composite of complex functors, unfolding the concrete reduction-tower construction.
Expose those composites in the comparison's type and assemble Mathlib's canonical
`Functor.mapHomologicalComplexCompIso` on each side in a local generic constructor,
then instantiate it. The assembly is checked with abstract functors, avoiding concrete
tower unfolding. Their degree maps are identities,
so this is the same termwise comparison, with the same objects, maps and normalization.
This comparison repair changes no target statement, coefficient ring or completeness predicate.

## Old

```lean
def reductionTowerComparisonComplex (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (res (coefficientMap J A I) ⋙ reductionTower J A I false).mapHomologicalComplex
        (ComplexShape.up ℤ) ≅
      (reductionTower J A I true ⋙ tres (coefficientMap J A I)).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  letI := reductionRestriction_preservesZero J A I
  NatIso.mapHomologicalComplex (reductionTowerComparison J A I) (ComplexShape.up ℤ)
```

## New

```lean
def reductionTowerComparisonComplex (J : GrothendieckTopology C) (A : Type u)
    [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    (res (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (reductionTower J A I false).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (reductionTower J A I true).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tres (coefficientMap J A I)).mapHomologicalComplex (ComplexShape.up ℤ) :=
  let liftIso {A₀ A₁ A₂ A₃ : Type (u + 1)}
      [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂] [Category.{u} A₃]
      [Preadditive A₀] [Preadditive A₁] [Preadditive A₂] [Preadditive A₃]
      (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₃) (H : A₀ ⥤ A₂) (K : A₂ ⥤ A₃)
      [F.Additive] [G.Additive] [H.Additive] [K.Additive] (e : F ⋙ G ≅ H ⋙ K) :
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          G.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          K.mapHomologicalComplex (ComplexShape.up ℤ) :=
    Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (H ⋙ K)) (ComplexShape.up ℤ)).symm
  letI := reductionTower_additive J A I false
  letI := reductionTower_additive J A I true
  liftIso (res (coefficientMap J A I)) (reductionTower J A I false)
    (reductionTower J A I true) (tres (coefficientMap J A I))
    (reductionTowerComparison J A I)
```

The subsequent proofs temporarily disable the three specialized composite-functor
instances and use Mathlib's generic instances instead. The original instance
attributes are restored at the end of the module; the declarations and their exported
attributes are retained. Only the locally selected proofs of propositional functor
properties differ.

## Users

`tools/downstream.py Sheaf.Paper.ConstantCompletionEquivalence --uses
reductionTowerComparisonComplex` lists the item itself as the only declaration user
(two occurrences). A full Lean-source search finds no use of this declaration outside the item. Its old and new types are
definitionally equal. No external module requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | V6 | Its existing derived comparison formula now matches the two nested complex functors directly. |

A standalone Lean check proved that degree q of the new hom component is exactly
`(reductionTowerComparison J A I).hom.app (P.X q)`, using only the identity and
composition laws. The full assigned module compiled without warnings in 39.3 seconds.

## Status

landed 20261020T230839-L-620015 2026-10-20 (merge of deliver/V6/Sheaf.Paper.ConstantCompletionEquivalence)
