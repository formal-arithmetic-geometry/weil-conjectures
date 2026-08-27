/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.ColimitInt
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.LowerShriek.Etale

/-!

# Derived pushforward and derived lower shriek on unbounded derived categories

The categories of `A`-valued étale sheaves are abelian, the pushforward
`g_* = Etale.lowerStar` along an arbitrary morphism `g` and the lower shriek
`f_! = Etale.lowerShriek` along a morphism `f` admitting a compactification are additive,
and this file records their total right derived functors
`Rg_* : D(Z_ét) ⥤ D(Y_ét)` and `Rf_! : D(X_ét) ⥤ D(Y_ét)` on the unbounded
derived categories, implemented via `CategoryTheory.Functor.rightDerivedFunctor`.

The sheaf categories are Grothendieck abelian (the sorried instance
`CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_smallGrothendieckTopology`
of `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`) whenever the
coefficient category `A` is a Grothendieck abelian category with `Hom`-types in the
universe `u + 1`, one above the universe `u` of the base schemes; this covers the
intended applications `A = Ab.{u + 1}` and `A = ModuleCat.{u + 1} Λ`. The chosen localized
categories are accordingly fixed once and for all by the instance
`AlgebraicGeometry.Scheme.hasDerivedCategory_sheaf_smallEtaleTopology` below, which
installs `HasDerivedCategory.{u + 1}` on every sheaf category via
`HasDerivedCategory.ofIsGrothendieckAbelian`; no auxiliary universe parameters appear.

The construction of the unbounded right derived functor requires the source abelian
category to have K-injective resolutions (`CategoryTheory.Abelian.HasKInjectiveResolutions`).
That Grothendieck abelian categories have K-injective resolutions is a theorem of Alonso
Tarrío–Jeremías López–Souto Salorio and Serpé; it is recorded as the sorried instance
`CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

On the *bounded below* derived categories the derived functor machinery needs no such
input: Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus` requires only
`EnoughInjectives` on the source, and a Grothendieck abelian category has enough injectives
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`). So `Etale.rightDerivedLowerStarPlus`
and `Etale.rightDerivedLowerShriekPlus` need no K-injective hypothesis. Note however that
the chosen `HasDerivedCategory.{u + 1}` instance is itself built from the sorried K-injective
statement (through the local `u + 1`-smallness of the derived category), so every derived
functor in this file — including the `Plus` variants — currently depends on `sorryAx`. Since
the `ℓ`-adic formalism only needs `Dᵇc`, the `Plus` variants are the versions to build on;
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility` identifies
the restriction of the unbounded functors to `DerivedCategory.Plus` with these.

The same asymmetry governs the composition isomorphism. The unbounded
`CategoryTheory.Functor.rightDerivedFunctorCompIso`
(`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`) takes
`HasKInjectiveResolutions` on both sheaf categories. Its bounded below counterpart
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso` in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp` asks only
that the first functor preserve injective objects, which for an étale `g` holds because
`g_*` is right
adjoint to the left exact `g^*`. That is what makes `Etale.rightDerivedLowerStarPlusComp`
below free of any K-injective hypothesis as well.

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerStar`: the total right derived functor
  `Rg_*` of the pushforward on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerShriek`: the total right derived functor
  `Rf_!` of the lower shriek on unbounded derived categories of étale sheaves.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` and
  `AlgebraicGeometry.Etale.rightDerivedLowerShriekPlus`: the same two functors on the
  bounded below derived categories, free of the K-injective hypothesis.
- `AlgebraicGeometry.Etale.preservesInjectiveObjects_lowerStar`: for étale `g`, the
  pushforward `g_*` preserves injective objects, being right adjoint to the left exact `g^*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarPlusComp`: the composition isomorphism
  `R⁺(h₁)_* ⋙ R⁺(h₂)_* ≅ R⁺(h₁ ≫ h₂)_*` for `h₁` étale, again free of the K-injective
  hypothesis.

-/

@[expose] public section

universe v'' u'' u' u

open CategoryTheory Abelian Limits

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The chosen localized category `D(X_ét)` of `A`-valued étale sheaves, with `Hom`-types in
`Type (u + 1)`, obtained from the Grothendieck abelian structure of the sheaf category via
`HasDerivedCategory.ofIsGrothendieckAbelian`. -/
noncomputable instance Scheme.hasDerivedCategory_sheaf_smallEtaleTopology (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (Sheaf X.smallEtaleTopology A) :=
  HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} _

section DerivedLowerStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The total right derived functor `Rg_* : D(Z_ét) ⥤ D(Y_ét)` of the pushforward
`g_*` along an arbitrary morphism `g : Z ⟶ Y` on the unbounded derived categories of
étale sheaves. -/
noncomputable def Etale.rightDerivedLowerStar :
    DerivedCategory (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctor

/-- The right derived functor `Rg_* : D⁺(Z_ét) ⥤ D⁺(Y_ét)` of the pushforward `g_*` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerStar` this needs no K-injective hypothesis:
`Functor.rightDerivedFunctorPlus` needs only `EnoughInjectives` on the source, which
Mathlib provides for every Grothendieck abelian category. The only dependence on the
sorried `CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian` is
through the chosen `HasDerivedCategory.{u + 1}` instance. -/
noncomputable def Etale.rightDerivedLowerStarPlus :
    DerivedCategory.Plus (Sheaf Z.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerStar A g).rightDerivedFunctorPlus

end DerivedLowerStar

section DerivedLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The total right derived functor `Rf_! : D(X_ét) ⥤ D(Y_ét)` of the lower shriek
`f_!` along a morphism `f : X ⟶ Y` admitting a compactification on the unbounded
derived categories of étale sheaves. -/
noncomputable def Etale.rightDerivedLowerShriek :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctor

/-- The right derived functor `Rf_! : D⁺(X_ét) ⥤ D⁺(Y_ét)` of the lower shriek `f_!` on the
*bounded below* derived categories of étale sheaves.

Unlike `Etale.rightDerivedLowerShriek` this needs no K-injective hypothesis;
see `Etale.rightDerivedLowerStarPlus`. -/
noncomputable def Etale.rightDerivedLowerShriekPlus :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology A) ⥤
      DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A) :=
  (Etale.lowerShriek A f).rightDerivedFunctorPlus

end DerivedLowerShriek


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

end DerivedUpperStar

section DerivedUpperLowerStarAdjunction

/-!
## The derived adjunction `Lg^* ⊣ Rg_*`

The adjunction `g^* ⊣ g_*` between the pullback and the pushforward of étale sheaves
induces an adjunction `Lg^* ⊣ Rg_*` between their total derived functors on the
unbounded derived categories, by
`CategoryTheory.Adjunction.derivedAdjunction`
(`WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`): the left adjoint is
derived via the K-flat left derivability structure on `D(Y_ét)` and the right adjoint
via the K-injective right derivability structure on `D(Z_ét)`, and the two
"absoluteness" hypotheses of mathlib's abstract theorem `Adjunction.derived` hold
because the derived-functor comparison maps are isomorphisms on K-flat, respectively
K-injective, complexes.

The hypotheses of this section are those of the section `DerivedUpperStar`: the
K-injective resolutions on the pushforward side are supplied by the sheaf category
being Grothendieck abelian.
-/

open MonoidalCategory MonoidalClosed

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
/- The closed braided preadditive monoidal structure on the coefficient category, as in
the section `DerivedUpperStar`; it is what the monoidal transport instances of
`WeilConjectures.CategoryTheory.GrothendieckAbelian` are stated under. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
variable [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `Lg^* ⊣ Rg_*` between the total derived functors of the
pullback and the pushforward along an arbitrary morphism `g : Z ⟶ Y` on the unbounded
derived categories of étale sheaves, induced by the adjunction `g^* ⊣ g_*`. -/
noncomputable def Etale.derivedUpperStarLowerStarAdjunction :
    Etale.leftDerivedUpperStar A g ⊣ Etale.rightDerivedLowerStar A g :=
  (Etale.upperStarLowerStarAdjunction A g).derivedAdjunction

/-- The bounded below version of `Etale.derivedUpperStarLowerStarAdjunction`: since the
pullback `g^*` on étale sheaves is exact, its derived functor on the bounded below
derived categories is the restriction `(g^*).mapDerivedCategoryPlus` of the functor
induced by `g^*`, and it is left adjoint to the right derived functor
`(g_*).rightDerivedFunctorPlus` of the pushforward on the bounded below derived
categories. The right adjoint is derived via injective resolutions, which exist since
the étale sheaf category is Grothendieck abelian. -/
noncomputable def Etale.derivedUpperStarLowerStarAdjunctionPlus :
    (Etale.upperStar A g).mapDerivedCategoryPlus ⊣
      (Etale.lowerStar A g).rightDerivedFunctorPlus :=
  (Etale.upperStarLowerStarAdjunction A g).derivedAdjunctionPlus

end DerivedUpperLowerStarAdjunction

section DerivedOpenImmersionLowerShriekUpperStarAdjunction

/-!
## The derived adjunction `j_! ⊣ j^*` along an open immersion

For an open immersion `j : U ⟶ X` both halves of the adjunction
`Etale.openImmersionLowerShriekUpperStarAdjunction` are *exact*: the extension by zero
`j_!` by `Etale.preservesFiniteLimits_openImmersionLowerShriek` together with its being a
left adjoint, and the pullback `j^*` by `Etale.preservesFiniteLimits_upperStar` together
with its being a left adjoint. So each of them induces a functor on derived categories by
applying it levelwise, and the two levelwise functors are again adjoint.

The adjunction is obtained where the derived formalism provides it, namely between the
*total* derived functors: `Adjunction.derivedAdjunction` gives
`(j_!).leftDerivedFunctor ⊣ (j^*).rightDerivedFunctor`, the left one computed by K-flat
resolutions and the right one by K-injective resolutions. Exactness then identifies each
with the corresponding levelwise functor
(`Functor.leftDerivedFunctorIsoMapDerivedCategory` and
`Functor.rightDerivedFunctorIsoMapDerivedCategory`), and the resulting adjunction on the
unbounded derived categories restricts along the fully faithful inclusions of the bounded
below ones. Both steps are the general
`Adjunction.mapDerivedCategoryAdjunction` and `Adjunction.mapDerivedCategoryPlusAdjunction`
of `WeilConjectures.CategoryTheory.DerivedCategory.Adjunction`.

In particular the K-flat and K-injective machinery, and with it the coefficient
hypotheses of the section `DerivedUpperStar`, are still needed even though the final
statement mentions only levelwise functors.
-/

open MonoidalCategory MonoidalClosed

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/- The K-flat resolution package on the coefficient category `A`, as in the sections
`DerivedUpperStar` and `DerivedUpperLowerStarAdjunction`; it is what makes the total left
derived functor of `j_!` available. -/
variable [MonoidalCategory A] [MonoidalPreadditive A] [BraidedCategory A] [MonoidalClosed A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
  [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived adjunction `j_! ⊣ j^*` along an open immersion `j : U ⟶ X` on the
unbounded derived categories of étale sheaves: since both `j_!` and `j^*` are exact, their
total derived functors are the levelwise functors, and the adjunction between the total
left derived functor of `j_!` and the total right derived functor of `j^*` becomes an
adjunction between the levelwise functors. -/
noncomputable def Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction :
    (Etale.openImmersionLowerShriek A j).mapDerivedCategory ⊣
      (Etale.upperStar A j).mapDerivedCategory :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryAdjunction

/-- The bounded below version of
`Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction`: the derived adjunction
`j_! ⊣ j^*` along an open immersion on the bounded below derived categories of étale
sheaves, obtained by restricting the unbounded one along the fully faithful inclusions,
which is legitimate since the exact functors `j_!` and `j^*` preserve bounded below
objects. -/
noncomputable def Etale.derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus :
    (Etale.openImmersionLowerShriek A j).mapDerivedCategoryPlus ⊣
      (Etale.upperStar A j).mapDerivedCategoryPlus :=
  (Etale.openImmersionLowerShriekUpperStarAdjunction A j).mapDerivedCategoryPlusAdjunction

end DerivedOpenImmersionLowerShriekUpperStarAdjunction

section Comp

/-- For an étale `g`, the pushforward `g_*` preserves injective objects, being right adjoint
to the pullback `g^*`, which is left exact and in particular preserves monomorphisms. This is
the hypothesis of `CategoryTheory.Functor.rightDerivedFunctorPlusCompIso`, and it is what
makes the composition isomorphism below available.

Only `g` étale is covered because that is the generality in which
`AlgebraicGeometry.Etale.preservesFiniteLimits_upperStar` fires by instance search; for a
general `g` the left exactness of `g^*` carries an extra hypothesis on the left Kan
extension along base change. -/
instance Etale.preservesInjectiveObjects_lowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) [Etale g] :
    (Etale.lowerStar A g).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Etale.upperStarLowerStarAdjunction A g)

variable {R S T : Scheme.{u}} (h₁ : T ⟶ S) (h₂ : S ⟶ R) [Etale h₁]

/-- The composition isomorphism `R⁺(h₁)_* ⋙ R⁺(h₂)_* ≅ R⁺(h₁ ≫ h₂)_*` for the bounded below
derived pushforwards, for `h₁` étale. It is the general
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIso'` applied to the underived
composition isomorphism `AlgebraicGeometry.Etale.lowerStarComp`.

There is no unbounded counterpart of this in the repository that avoids the K-injective
hypothesis: the unbounded composition theorem
`CategoryTheory.Functor.rightDerivedFunctorCompIso` needs `HasKInjectiveResolutions` on both
sheaf categories. -/
noncomputable def Etale.rightDerivedLowerStarPlusComp :
    Etale.rightDerivedLowerStarPlus A h₁ ⋙ Etale.rightDerivedLowerStarPlus A h₂ ≅
      Etale.rightDerivedLowerStarPlus A (h₁ ≫ h₂) :=
  Functor.rightDerivedFunctorPlusCompIso' (Etale.lowerStar A h₁) (Etale.lowerStar A h₂)
    (Etale.lowerStarComp A h₁ h₂)

end Comp

end AlgebraicGeometry
