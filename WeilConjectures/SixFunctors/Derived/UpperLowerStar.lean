/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived Upper Star and Lower Star

# Main Results

- `AlgebraicGeometry.Etale.rightDerivedLowerStar` : total right derived of lower star, with
  scoped notation `R(g)_*[A]`, prefixing the notation `(g)_*[A]` of the underived
  pushforward by `R`.

- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` : total right derived of lower star on
  bounded below derived category, with scoped notation `R(g)_*[A]+`.

- `AlgebraicGeometry.Etale.leftDerivedUpperStar` : total left derivation of upper star, with
  scoped notation `L(g)^*[A]`, prefixing the notation `(g)^*[A]` of the underived pullback
  by `L`.

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

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctor

@[inherit_doc rightDerivedLowerStar]
scoped notation "R(" g ")_*[" A "]" =>
  rightDerivedLowerStar A g

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves. -/
noncomputable def rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (g)_*[A].rightDerivedFunctorPlus

@[inherit_doc rightDerivedLowerStarPlus]
scoped notation "R(" g ")_*[" A "]+" =>
  rightDerivedLowerStarPlus A g

end Etale

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
its compatibilities provided by its `Monoidal` subfolder; its preadditivity is
`CategoryTheory.Sheaf.monoidalPreadditive`, which holds for any sheaf category.

The additivity and right exactness of `g^*` are derived here from the adjunction
`g^* ⊣ g_*`; the left exactness comes from `Etale.preservesFiniteLimits_upperStar`, whose
hypotheses — sheafification on the small étale site of `Z` and left exactness of the left
Kan extension along the opposite of base change — are stated as variables of this section;
for an étale `g` both are automatic. Since `g^*` is exact, it preserves in
particular all K-flat quasi-isomorphisms, which is the input needed by the
derivability-structure machinery.
-/

open MonoidalCategory MonoidalClosed Etale

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

instance : (g)^*[A].Additive :=
  (Etale.upperStarLowerStarAdjunction A g).left_adjoint_additive

instance : (g)^*[A].PreservesHomology := by
  have : PreservesColimitsOfSize.{0, 0} (g)^*[A] :=
    (Etale.upperStarLowerStarAdjunction A g).leftAdjoint_preservesColimits
  exact {}

/- Functorial flat resolutions on the coefficient category; they induce functorial flat
resolutions of étale sheaves via `Etale.sheafHasFunctorialFlatResolution`. -/
variable [Abelian.HasFunctorialFlatResolution A]

namespace Etale

/-- The total left derived functor `Lg^* : D(Y_ét) ⥤ D(Z_ét)` of the pullback `g^*`
along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of étale
sheaves, defined via the K-flat left derivability structure: `Lg^*` is computed by
applying `g^*` to a K-flat resolution.

Since `g^*` is exact, the counit `Lg^* ∘ Q ⟶ Q ∘ g^*` is in fact an isomorphism
everywhere; the construction via the derivability structure is uniform in the functor
and applies verbatim once `g^*` is replaced by a non-exact functor (e.g. the pullback
of sheaves of modules over a varying sheaf of rings). -/
noncomputable def leftDerivedUpperStar :
    DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Z.smallEtaleTopology A) :=
  (g)^*[A].leftDerivedFunctor

@[inherit_doc leftDerivedUpperStar]
scoped notation "L(" g ")^*[" A "]" =>
  leftDerivedUpperStar A g

end Etale

/-- The compatibility of the derived pullback with the levelwise functor: the total left
derived functor `Lh^*`, computed via K-flat resolutions, is canonically isomorphic to
the functor induced by the exact functor `h^*` on the derived categories. -/
noncomputable def Etale.leftDerivedUpperStarIsoMapDerivedCategory {T S : Scheme.{u}}
    (h : T ⟶ S) : L(h)^*[A] ≅ (h)^*[A].mapDerivedCategory :=
  (h)^*[A].leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(h₁ ≫ h₂)^* ≅ Lh₁^* ∘ Lh₂^*` of derived pullbacks,
obtained from the underived composition isomorphism `Etale.upperStarComp` and the
compatibility of left derivation with `mapDerivedCategory` for exact functors. -/
noncomputable def Etale.leftDerivedUpperStarComp {T S R : Scheme.{u}}
    (h₁ : T ⟶ S) (h₂ : S ⟶ R) :
    L(h₁ ≫ h₂)^*[A] ≅ L(h₂)^*[A] ⋙ L(h₁)^*[A] :=
  Functor.leftDerivedFunctorNatIso _ (Etale.upperStarComp A h₁ h₂) ≪≫
    Functor.leftDerivedFunctorCompIso (h₂)^*[A] (h₁)^*[A]

/-- The exactness comparison `κ : h^* ∘ H^n ≅ H^n ∘ Lh^*`: since the underived pullback
`h^*` on étale sheaves is exact, applying it to the `n`-th homology sheaf of an object
of the derived category computes the `n`-th homology sheaf of the derived pullback. -/
noncomputable def Etale.homologyLeftDerivedUpperStarIso {T S : Scheme.{u}}
    (h : T ⟶ S) (n : ℤ) :
    DerivedCategory.homologyFunctor (Sheaf S.smallEtaleTopology A) n ⋙ (h)^*[A] ≅
      L(h)^*[A] ⋙ DerivedCategory.homologyFunctor (Sheaf T.smallEtaleTopology A) n :=
  (h)^*[A].leftDerivedFunctorHomologyFunctorIso n

/-- The single-degree comparison for the derived pullback: since the underived pullback
`h^*` on étale sheaves is exact, the derived pullback of a sheaf placed in degree `0` is
the pullback of the sheaf placed in degree `0`, `Lh^*(F[0]) ≅ (h^* F)[0]`. -/
noncomputable def Etale.singleCompLeftDerivedUpperStarIso {T S : Scheme.{u}} (h : T ⟶ S) :
    DerivedCategory.singleFunctor (Sheaf S.smallEtaleTopology A) 0 ⋙ L(h)^*[A] ≅
      (h)^*[A] ⋙ DerivedCategory.singleFunctor (Sheaf T.smallEtaleTopology A) 0 :=
  (h)^*[A].singleFunctorCompLeftDerivedFunctorIso

end DerivedUpperStar

end AlgebraicGeometry
