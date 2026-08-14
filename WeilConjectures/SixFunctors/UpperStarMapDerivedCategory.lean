/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Derived
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# The derived pullback `Lg^*` and `mapDerivedCategory`

The pullback `g^* = Etale.upperStar` on étale sheaves is exact (the left exactness is
the assumed instance `Etale.preservesFiniteLimits_upperStar`; the right exactness holds
since `g^*` is a left adjoint), so it induces a functor
`(Etale.upperStar A g).mapDerivedCategory` on derived categories by applying `g^*`
levelwise. This file records the compatibility of the total left derived functor
`Lg^* = Etale.leftDerivedUpperStar` (defined via K-flat resolutions in
`WeilConjectures.SixFunctors.Derived`) with this levelwise functor, by
instantiating `WeilConjectures.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory`,
and derives the consequences needed by the base-change package:

- `AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory`: the canonical
  isomorphism `Lg^* ≅ (g^*).mapDerivedCategory`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`: the composition isomorphism
  `L(h₁ ≫ h₂)^* ≅ Lh₁^* ∘ Lh₂^*`, obtained from the underived composition isomorphism
  `Etale.upperStarComp` and the compatibility above.
- `AlgebraicGeometry.Etale.homologyLeftDerivedUpperStarIso`: the exactness comparison
  `g^* ∘ H^n ≅ H^n ∘ Lg^*`.
- `AlgebraicGeometry.Etale.singleCompLeftDerivedUpperStarIso`: the single-degree
  comparison `Lg^*(F[0]) ≅ (g^* F)[0]`.

The last three statements eliminate the corresponding sorried inputs of the base-change
morphism construction in the proper base change package
(`WeilConjectures.SixFunctors.ProperBaseChange.BaseChangeMorphism`).

-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

/- Sheafification, pointwise left Kan extensions and chosen localized derived categories
for the small étale sites of all schemes at once. -/
variable [∀ (T : Scheme.{u}), HasWeakSheafify T.smallEtaleTopology A]
  [∀ (T S : Scheme.{u}) (φ : T ⟶ S) (F : S.Etaleᵒᵖ ⥤ A),
    (MorphismProperty.Over.pullback @Etale ⊤ φ).op.HasLeftKanExtension F]
  [∀ (T : Scheme.{u}), HasDerivedCategory.{w} (Sheaf T.smallEtaleTopology A)]

/- The K-flat resolution package on the étale sheaf categories of all schemes at once,
as in the section `DerivedUpperStar` of
`WeilConjectures.SixFunctors.Derived`. -/
variable [∀ (T : Scheme.{u}), MonoidalCategory (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}), MonoidalPreadditive (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}))
    (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (T : Scheme.{u}) (X₁ X₂ X₃ : GradedObject ℤ (Sheaf T.smallEtaleTopology A)),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (T : Scheme.{u}), HasColimitsOfShape ℤ (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}), HasExactColimitsOfShape ℤ (Sheaf T.smallEtaleTopology A)]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology A),
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf T.smallEtaleTopology A)).obj F)]
  [∀ (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology A),
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf T.smallEtaleTopology A)).flip.obj F)]
  [∀ (T : Scheme.{u}), Abelian.HasFunctorialFlatResolution (Sheaf T.smallEtaleTopology A)]

/-- The compatibility of the derived pullback with the levelwise functor: the total left
derived functor `Lh^*`, computed via K-flat resolutions, is canonically isomorphic to
the functor induced by the exact functor `h^*` on the derived categories. -/
noncomputable def Etale.leftDerivedUpperStarIsoMapDerivedCategory {T S : Scheme.{u}}
    (h : T ⟶ S) :
    Etale.leftDerivedUpperStar A h ≅ (Etale.upperStar A h).mapDerivedCategory :=
  (Etale.upperStar A h).leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₁^* ∘ Lh₂^*` of derived pullbacks,
obtained from the underived composition isomorphism `Etale.upperStarComp` and the
compatibility of left derivation with `mapDerivedCategory` for exact functors. -/
noncomputable def Etale.leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    Etale.leftDerivedUpperStar A (h₁ ≫ h₂) ≅
      Etale.leftDerivedUpperStar A h₂ ⋙ Etale.leftDerivedUpperStar A h₁ :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarComp A h₁ h₂) ≪≫
    Functor.leftDerivedFunctorCompIso (Etale.upperStar A h₂) (Etale.upperStar A h₁)

/-- The exactness comparison `κ : h^* ∘ H^n ≅ H^n ∘ Lh^*`: since the underived pullback
`h^*` on étale sheaves is exact, applying it to the `n`-th homology sheaf of an object
of the derived category computes the `n`-th homology sheaf of the derived pullback. -/
noncomputable def Etale.homologyLeftDerivedUpperStarIso {T S : Scheme.{u}}
    (h : T ⟶ S) (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology A) n ⋙ Etale.upperStar A h ≅
      Etale.leftDerivedUpperStar A h ⋙
        DerivedCategory.homologyFunctor (Sheaf T.smallEtaleTopology A) n :=
  (Etale.upperStar A h).leftDerivedFunctorHomologyFunctorIso n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`h^*` on étale sheaves is exact, the derived pullback of a sheaf placed in degree `0` is
the pullback of the sheaf placed in degree `0`, `Lh^*(F[0]) ≅ (h^* F)[0]`. -/
noncomputable def Etale.singleCompLeftDerivedUpperStarIso {T S : Scheme.{u}} (h : T ⟶ S) :
    DerivedCategory.singleFunctor (Sheaf S.smallEtaleTopology A) 0 ⋙
        Etale.leftDerivedUpperStar A h ≅
      Etale.upperStar A h ⋙
        DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology A) 0 :=
  (Etale.upperStar A h).singleFunctorCompLeftDerivedFunctorIso

end AlgebraicGeometry
