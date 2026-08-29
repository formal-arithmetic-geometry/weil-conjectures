/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.SixFunctors.Derived.HasDerivedCategory

/-!

# Derived Upper Star and Lower Star

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  bounded below derived category.

- `AlgebraicGeometry.Etale.leftDerivedUpperStar` : total left derivation of upper star.

- `AlgebraicGeometry.Etale.homologyLeftDerivedUpperStarIso` : compatibility of
  `AlgebraicGeometry.Etale.leftDerivedUpperStar` and map derived category.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

@[inherit_doc Etale.rightDerivedLowerStar]
scoped notation "R(" g ")_*[" A "]" =>
  Etale.rightDerivedLowerStar A g

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerStar` this needs no K-injective hypothesis:
`Functor.rightDerivedFunctorPlus` needs only `EnoughInjectives` on the source, which
Mathlib provides for every Grothendieck abelian category. The only dependence on the
sorried `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` is
through the chosen `HasDerivedCategory.{u}` instance. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

@[inherit_doc Etale.rightDerivedLowerStarPlus]
scoped notation "R(" g ")_*[" A "]+" =>
  Etale.rightDerivedLowerStarPlus A g

end DerivedLowerStar

section DerivedUpperStar

/-!
## The derived pullback `Lg^*`

The pullback `g^* = Etale.upperStar` is left derived using the K-flat left
derivability structure of `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`.
This requires the source sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product interacts well with coproducts and
`ℤ`-indexed colimits, and to admit functorial flat resolutions. These inputs are stated
as hypotheses on the coefficient category `A` only; they are transported to the sheaf
categories by the instances of the folder
`WeilConjectures.CategoryTheory.GrothendieckAbelian`, with the monoidal structure and
its compatibilities provided by its `Monoidal` subfolder.

The additivity and right exactness of `g^*` are derived here from the adjunction
`g^* ⊣ g_*`; the left exactness comes from `Etale.preservesFiniteLimits_upperStar`, whose
hypotheses — sheafification on the small étale site of `Z` and left exactness of the left
Kan extension along the opposite of base change — are stated as variables of this section;
for an étale `g` both are automatic. Since `g^*` is exact, it preserves in
particular all K-flat quasi-isomorphisms, which is the input needed by the
derivability-structure machinery.
-/

open MonoidalCategory MonoidalClosed

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

instance : HasExactColimitsOfShape ℤ A := by
  have := AB5OfSize_of_univLE.{0, 0} A
  infer_instance

/- The preadditive monoidal structure on the coefficient category. It is assumed closed
and braided (as is the intended application `A = ModuleCat.{u + 1} Λ` for a commutative
ring `Λ`, which is even symmetric monoidal closed): that is what makes the class of
sheafification-inverting morphisms of presheaves monoidal, hence what lets the monoidal
structure descend to the étale sheaf categories, see
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]

/- Existence of the coproducts defining the tensor product of complexes (the indexing
fibers of the total degree map are in bijection with `ℤ`, see
`ComplexShape.hasColimitsOfShape_discrete_π_up_int`), and its compatibility with the
tensor product, on the coefficient category. -/
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/- Existence and exactness of `ℤ`-indexed colimits, and their preservation by the
tensor product in each variable, on the coefficient category. -/
variable [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]

instance : (Etale.upperStar A g).Additive :=
  (Etale.upperStarLowerStarAdjunction A g).left_adjoint_additive

local instance : (Etale.upperStar A g).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (F := Etale.upperStar A g)

instance : (Etale.upperStar A g).PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (Etale.upperStar A g) :=
    (Etale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  exact {}

/- Functorial flat resolutions on the coefficient category; they induce functorial flat
resolutions of étale sheaves via `Etale.sheafHasFunctorialFlatResolution`. -/
variable [Abelian.HasFunctorialFlatResolution A]

/-- The total left derived functor `Lg^* : D(Y_ét) ⥤ D(Z_ét)` of the pullback `g^*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of étale
sheaves, defined via the K-flat left derivability structure: `Lg^*` is computed by
applying `g^*` to a K-flat resolution.

Since `g^*` is exact, the counit `Lg^* ∘ Q ⟶ Q ∘ g^*` is in fact an isomorphism
everywhere; the construction via the derivability structure is uniform in the functor
and applies verbatim once `g^*` is replaced by a non-exact functor (e.g. the pullback
of sheaves of modules over a varying sheaf of rings). -/
noncomputable def Etale.leftDerivedUpperStar :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (Etale.upperStar A g).leftDerivedFunctor

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

end DerivedUpperStar

end AlgebraicGeometry
