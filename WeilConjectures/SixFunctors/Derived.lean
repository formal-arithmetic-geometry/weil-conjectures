/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.LowerShriek.Etale
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Derived pushforward and derived lower shriek on unbounded derived categories

For an abelian coefficient category `A` admitting sheafification on the small étale sites,
the categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D(Z_ét) ⥤ D(Y_ét)` and `Rf_! : D(X_ét) ⥤ D(Y_ét)` on the unbounded
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctor`.

The chosen localized categories `HasDerivedCategory` are inputs with a general universe.
The construction of the unbounded right derived functor requires the source abelian
category to have K-injective resolutions (`CategoryTheory.Abelian.HasKInjectiveResolutions`).
The sheaf categories are Grothendieck abelian
(`AlgebraicGeometry.Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`) whenever the
coefficient category `A` is a concrete Grothendieck abelian category (with hom types and
underlying types in the universe `u` of the base schemes, and the forgetful functor
preserving limits and filtered colimits and reflecting isomorphisms); this covers the
intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`. That Grothendieck abelian
categories have K-injective resolutions is a theorem of Alonso Tarrío–Jeremías
López–Souto Salorio and Serpé; it is recorded here as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.

-/

@[expose] public section

universe w w' v' u' u

open CategoryTheory Abelian Limits

namespace CategoryTheory.Abelian

/-- Every Grothendieck abelian category has K-injective resolutions: any cochain
complex admits a monomorphic quasi-isomorphism into a K-injective complex. This is a
theorem of Alonso Tarrío–Jeremías López–Souto Salorio and Serpé. -/
instance hasKInjectiveResolutions_of_isGrothendieckAbelian
    {C : Type u'} [Category.{v'} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasKInjectiveResolutions C :=
  sorry

end CategoryTheory.Abelian

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A]
  {FA : A → A → Type*} {CD : A → Type u}
  [∀ X Y, FunLike (FA X Y) (CD X) (CD Y)] [ConcreteCategory.{u} A FA]
  [PreservesLimits (CategoryTheory.forget A)]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget A)]
  [IsGrothendieckAbelian.{u} A]

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasDerivedCategory.{w} (Sheaf X.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Y.smallEtaleTopology A)]

/-- The total right derived functor `Rf_! : D(X_ét) ⥤ D(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the unbounded
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctor

end DerivedLowerShriek

section SheafInstances

/-!
## Structure on étale sheaf categories induced from the coefficient category

The K-flat left derivability structure used below to derive the pullback `g^*` requires
the sheaf category `Sheaf Y.smallEtaleTopology A` to carry a preadditive monoidal
structure whose tensor product interacts well with coproducts and `ℤ`-indexed colimits,
and to admit functorial flat resolutions. The instances of this section transport each
of these hypotheses from the coefficient category `A` to the categories of `A`-valued
étale sheaves, so that the derived pullback only takes hypotheses on `A`:

- the monoidal structure is mathematically provided by
  `CategoryTheory.Sheaf.monoidalCategory` (sheafification of the objectwise tensor
  product of presheaves), which is closed by Day's reflection theorem — whence the
  preadditivity and the colimit-preservation instances. Instantiating these for the
  small étale site requires transporting along the equivalence with the small affine
  étale site, since `Y.Etale` is only essentially small and the presheaf-level
  closed-monoidal infrastructure does not apply verbatim to a large site;
- the colimit existence and exactness instances hold since the sheaf category is
  Grothendieck abelian (`Scheme.isGrothendieckAbelian_sheaf_smallEtaleTopology`);
- the functorial flat resolutions are provided for module coefficients by the
  functorial local free covers `⊕ j_{U!} Λ_U` (Stacks Project, Tag 06YL).

These constructions are not yet formalized, so the instances are recorded with `sorry`.
-/

open MonoidalCategory

variable (Y : Scheme.{u})

/-- The monoidal structure on `A`-valued étale sheaves induced by a monoidal structure
on the coefficient category `A`: the sheafification of the objectwise tensor product of
presheaves. -/
noncomputable instance Etale.sheafMonoidalCategory [MonoidalCategory A] :
    MonoidalCategory (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- The monoidal structure on étale sheaves is preadditive when the one on the
coefficient category is. -/
instance Etale.sheafMonoidalPreadditive [MonoidalCategory A] [MonoidalPreadditive A] :
    MonoidalPreadditive (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Existence of the coproducts defining the tensor product of complexes of étale
sheaves, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasColimitsOfShapeDiscretePi [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A]
    (j : ℤ) :
    HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}))
      (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasTensor₄ObjExt [MonoidalCategory A]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensor₁₂Tensor [MonoidalCategory A]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensorTensor₂₃ [MonoidalCategory A]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  sorry

/-- Existence of `ℤ`-indexed colimits of étale sheaves, induced by the corresponding
condition on the coefficient category. -/
instance Etale.sheafHasColimitsOfShapeInt [HasColimitsOfShape ℤ A] :
    HasColimitsOfShape ℤ (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Exactness of `ℤ`-indexed colimits of étale sheaves, induced by the corresponding
condition on the coefficient category. -/
instance Etale.sheafHasExactColimitsOfShapeInt [HasColimitsOfShape ℤ A]
    [HasExactColimitsOfShape ℤ A] :
    HasExactColimitsOfShape ℤ (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in the
first variable, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorObj [MonoidalCategory A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf Y.smallEtaleTopology A)).obj X) :=
  sorry

/-- Preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in the
second variable, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorFlipObj [MonoidalCategory A]
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf Y.smallEtaleTopology A)).flip.obj X) :=
  sorry

/-- Functorial flat resolutions of étale sheaves: for module coefficients these are
given by the functorial local free covers `⊕ j_{U!} Λ_U` (Stacks Project, Tag 06YL). -/
instance Etale.sheafHasFunctorialFlatResolution [MonoidalCategory A]
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  sorry

end SheafInstances

section DerivedUpperStar

/-!
## The derived pullback `Lg^*`

The pullback `g^* = Etale.upperStar` is left derived using the K-flat left
derivability structure of `WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs`.
This requires the source sheaf category `Sheaf Y.smallEtaleTopology A` to carry a
preadditive monoidal structure whose tensor product interacts well with coproducts and
`ℤ`-indexed colimits, and to admit functorial flat resolutions. These inputs are stated
as hypotheses on the coefficient category `A` only; they are transported to the sheaf
categories by the instances of the section `SheafInstances` above.

The additivity and homology-preservation (exactness) of `g^*` are derived here from the
adjunction `g^* ⊣ g_*`; the left exactness of `g^*` is recorded as the sorried instance
`Etale.preservesFiniteLimits_upperStar`, mirroring the sorried
`Etale.preservesFiniteLimits_lowerStar`. Since `g^*` is exact, it preserves in
particular all K-flat quasi-isomorphisms, which is the input needed by the
derivability-structure machinery.
-/

open MonoidalCategory

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/- The sheafification needed by `g^*` is stated as a hypothesis (although it is
derivable from the concreteness assumptions on `A`) so that the instances declared in
this section do not depend on the concrete-category data of `A`; this keeps instance
resolution fast. -/
variable [HasWeakSheafify Z.smallEtaleTopology A]

variable [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Z.smallEtaleTopology A)]

/- The pointwise left Kan extensions defining `g^*` exist; for étale `g` this is
automatic (`Etale.hasPointwiseLeftKanExtension_op_overPullback`), and in general it
follows from the essential smallness of the étale sites and cocompleteness of `A`. -/
variable [∀ F : Y.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F]

/- The preadditive monoidal structure on the coefficient category. -/
variable [MonoidalCategory A] [MonoidalPreadditive A]

/- Existence of the coproducts defining the tensor product of complexes, and its
compatibility with the tensor product, on the coefficient category. -/
variable [∀ (j : ℤ), HasColimitsOfShape
    (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j})) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/- Existence and exactness of `ℤ`-indexed colimits, and their preservation by the
tensor product in each variable, on the coefficient category. -/
variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
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

end DerivedUpperStar

end AlgebraicGeometry
