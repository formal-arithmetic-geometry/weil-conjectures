/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GeometricFrobenius

/-!
# Pushforwards along a base change to `k̄` commute with the Frobenius pullbacks

Let `k` be a finite field, `φ : X₀ ⟶ Y₀` a morphism of `k`-schemes and `φ̄ = φ × 𝟙 : X ⟶ Y` its
base change to the geometric fibers, so that `φ̄ ≫ Fr_Y = Fr_X ≫ φ̄` for the geometric Galois
Frobenii. Since the Frobenii are isomorphisms, the square

```
          Fr_X
     X ────────▶ X
     │           │
   φ̄ │           │ φ̄
     ▼           ▼
     Y ────────▶ Y
          Fr_Y
```

is cartesian with horizontal universal homeomorphisms, so its base change maps are
isomorphisms. This gives the exchange isomorphisms which transport Frobenius structures along
`φ̄_*`, along `Rφ̄_*` and, for an open immersion `φ`, along the extension by zero `φ̄_!`.

## Main definitions

- `AlgebraicGeometry.Etale.lowerStarGeometricFiberMapCompFrobeniusIso`:
  `φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*`, the base change map of the square.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso`:
  `Rφ̄_* ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rφ̄_*` on the unbounded derived categories.
- `AlgebraicGeometry.Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`:
  `φ̄_! ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_!` for an open immersion `φ`, the inverse of the base change
  map for the extension by zero.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

open Etale

/-- The pullback along an isomorphism preserves K-injective complexes: it is an equivalence,
hence right adjoint to the exact inverse equivalence. -/
instance Etale.preservesKInjectiveComplexes_upperStar_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : ((f)^*[A]).PreservesKInjectiveComplexes :=
  have := Etale.isEquivalence_upperStar A f
  have : ((f)^*[A]).asEquivalence.functor.Additive := Etale.additive_upperStar A f
  have : ((f)^*[A]).asEquivalence.symm.functor.Additive := Equivalence.inverse_additive _
  ((f)^*[A]).asEquivalence.symm.toAdjunction.preservesKInjectiveComplexes

/-- The total right derived pushforward `Rf_*` on the unbounded derived categories of étale
sheaves is additive, being right adjoint to `D(f^*)`. -/
instance Etale.additive_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (R((f)_*[A])).Additive :=
  (Etale.mapDerivedUpperStarLowerStarAdjunction A f).right_adjoint_additive

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

/-- The square `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y` of the base change `φ̄` of a morphism of `k`-schemes and
the geometric Galois Frobenii. -/
lemma Scheme.Hom.commSq_geometricGaloisFrobenius :
    CommSq f.geometricGaloisFrobenius.hom (Scheme.Hom.geometricFiberMap φ h)
      (Scheme.Hom.geometricFiberMap φ h) g.geometricGaloisFrobenius.hom :=
  ⟨(Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm⟩

/-- The square `Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y` is cartesian, its horizontal maps being isomorphisms. -/
lemma Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap :
    IsPullback f.geometricGaloisFrobenius.hom (Scheme.Hom.geometricFiberMap φ h)
      (Scheme.Hom.geometricFiberMap φ h) g.geometricGaloisFrobenius.hom :=
  .of_horiz_isIso (Scheme.Hom.commSq_geometricGaloisFrobenius φ h)

/-- The pushforward along the base change `φ̄ = φ × 𝟙 : X ⟶ Y` of a morphism of `k`-schemes
commutes with the pullbacks along the geometric Galois Frobenii:
`φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*`. It is the base change map of the square
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`, an isomorphism since the Frobenii are isomorphisms, hence universal
homeomorphisms. -/
noncomputable def Etale.lowerStarGeometricFiberMapCompFrobeniusIso :
    (Scheme.Hom.geometricFiberMap φ h)_*[A] ⋙ (g.geometricGaloisFrobenius.hom)^*[A] ≅
      (f.geometricGaloisFrobenius.hom)^*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_*[A] :=
  asIso (Etale.baseChangeMap A (Scheme.Hom.commSq_geometricGaloisFrobenius φ h))

/-- The derived form of `Etale.lowerStarGeometricFiberMapCompFrobeniusIso`: the total right
derived pushforward along `φ̄` commutes with the pullbacks along the geometric Galois Frobenii,
`Rφ̄_* ⋙ D(Fr_Y^*) ≅ D(Fr_X^*) ⋙ Rφ̄_*`. The pullbacks along the Frobenii are exact, so their
derived functors are computed levelwise; they are equivalences, so they preserve K-injective
complexes, and both sides are the total right derived functors of the two sides of the
underived isomorphism. -/
noncomputable def Etale.rightDerivedLowerStarGeometricFiberMapCompFrobeniusIso :
    R((Scheme.Hom.geometricFiberMap φ h)_*[A]) ⋙ D((g.geometricGaloisFrobenius.hom)^*[A]) ≅
      D((f.geometricGaloisFrobenius.hom)^*[A]) ⋙
        R((Scheme.Hom.geometricFiberMap φ h)_*[A]) :=
  Functor.isoWhiskerLeft _ (Functor.rightDerivedFunctorIsoMapDerivedCategory _).symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (Etale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight (Functor.rightDerivedFunctorIsoMapDerivedCategory _) _

/-- The extension by zero along the base change `φ̄` of an open immersion `φ` of `k`-schemes
commutes with the pullbacks along the geometric Galois Frobenii:
`φ̄_! ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_!`. It is the inverse of the base change map for the extension
by zero (`Etale.openImmersionLowerShriekBaseChangeMap`) of the cartesian square
`Fr_X ≫ φ̄ = φ̄ ≫ Fr_Y`. -/
noncomputable def Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso
    [IsOpenImmersion φ] :
    (Scheme.Hom.geometricFiberMap φ h)_!open[A] ⋙ (g.geometricGaloisFrobenius.hom)^*[A] ≅
      (f.geometricGaloisFrobenius.hom)^*[A] ⋙ (Scheme.Hom.geometricFiberMap φ h)_!open[A] :=
  have := Etale.isIso_openImmersionLowerShriekBaseChangeMap A
    (Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap φ h)
  (asIso (Etale.openImmersionLowerShriekBaseChangeMap A
    (Scheme.Hom.commSq_geometricGaloisFrobenius φ h))).symm

/-- The comparison `φ̄_! ⟶ φ̄_*` commutes with the Frobenius exchange isomorphisms
`Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso` and
`Etale.lowerStarGeometricFiberMapCompFrobeniusIso`: for a sheaf `F` on `X`, the square

```
  Fr_Y^* φ̄_! F ────────────▶ Fr_Y^* φ̄_* F
       │                          │
       ▼                          ▼
  φ̄_! Fr_X^* F ────────────▶ φ̄_* Fr_X^* F
```

commutes. -/
lemma Etale.openImmersionLowerShriekToLowerStar_geometricFiberMap_comm [IsOpenImmersion φ]
    (F : Sheaf f.geometricFiber.smallEtaleTopology A) :
    ((g.geometricGaloisFrobenius.hom)^*[A]).map
        ((Etale.openImmersionLowerShriekToLowerStar A
          (Scheme.Hom.geometricFiberMap φ h)).app F) ≫
      (Etale.lowerStarGeometricFiberMapCompFrobeniusIso A φ h).hom.app F =
    (Etale.openImmersionLowerShriekGeometricFiberMapCompFrobeniusIso A φ h).hom.app F ≫
      (Etale.openImmersionLowerShriekToLowerStar A (Scheme.Hom.geometricFiberMap φ h)).app
        (((f.geometricGaloisFrobenius.hom)^*[A]).obj F) :=
  sorry

end AlgebraicGeometry
