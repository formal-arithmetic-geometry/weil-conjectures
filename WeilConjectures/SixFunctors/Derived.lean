/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW
public import WeilConjectures.DerivedCategory.Adjunction
public import WeilConjectures.DerivedCategory.HomotopyCategory.GrothendieckAbelian
public import WeilConjectures.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.SixFunctors.LowerShriek.Etale
public import WeilConjectures.SixFunctors.SheafCompose
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

universe w w' v' u' v'' u'' u

open CategoryTheory Abelian Limits

namespace ComplexShape

/-!
The coproducts appearing in the definition of the tensor product of cochain complexes
are indexed by the discrete categories on the fibers of the total degree map
`(p, q) ↦ p + q` on `ℤ × ℤ`. The fiber over `j` is the antidiagonal
`{(p, q) | p + q = j}`, which is in bijection with `ℤ` via `p ↦ (p, j - p)`, so the
hypotheses on these shapes reduce to a single condition of shape `Discrete ℤ`.
-/

/-- The fiber over `j` of the total degree map `(p, q) ↦ p + q` on `ℤ × ℤ` is in
bijection with `ℤ`, via `p ↦ (p, j - p)`. -/
def πUpIntFiberEquiv (j : ℤ) :
    ℤ ≃ ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}) where
  toFun p := ⟨(p, j - p), show p + (j - p) = j by omega⟩
  invFun x := x.1.1
  left_inv p := rfl
  right_inv := fun ⟨⟨p, q⟩, h⟩ => by
    have h' : p + q = j := h
    obtain rfl : q = j - p := by omega
    rfl

/-- A category with `ℤ`-indexed coproducts admits the coproducts indexed by the
fibers of the total degree map on `ℤ × ℤ` which define the tensor product of cochain
complexes. -/
instance hasColimitsOfShape_discrete_π_up_int {C : Type u''} [Category.{v''} C]
    [HasColimitsOfShape (Discrete ℤ) C] (j : ℤ) :
    HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}))
      C :=
  hasColimitsOfShape_of_equivalence (Discrete.equivalence (πUpIntFiberEquiv j))

end ComplexShape

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

The monoidal structure itself is obtained below from `CategoryTheory.Sheaf.monoidalCategory`:
its inputs are the sheafification (from the concreteness assumptions on `A`) and the
monoidality of the class `W` of sheafification-inverting morphisms of presheaves, which
is checked on the stalks at the geometric points of the small étale site and needs the
tensor product of `A` to commute with filtered colimits in each variable. The remaining
constructions are not yet formalized, so their instances are recorded with `sorry`.
-/

open MonoidalCategory

variable (Y : Scheme.{u})

omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- Postcomposition with a limit-preserving functor preserves sheaves on the small
étale site. This does not follow from `hasSheafCompose_of_preservesLimitsOfSize`
directly, since the covering sieves of the small étale site are indexed by a large
type; it is instead transported from the small affine étale site, which is
`1`-hypercover dense and essentially small. -/
lemma Etale.hasSheafCompose_smallEtaleTopology {B : Type u''} [Category.{v''} B]
    (F : A ⥤ B) [PreservesLimitsOfSize.{u, u} F] :
    Y.smallEtaleTopology.HasSheafCompose F :=
  GrothendieckTopology.hasSheafCompose_of_isOneHypercoverDense
    (Scheme.AffineEtale.Spec Y) (Scheme.AffineEtale.topology Y) _ F

/-- Postcomposition with the forgetful functor of the concrete coefficient category
preserves étale sheaves. This is the instance of
`Etale.hasSheafCompose_smallEtaleTopology` needed to check statements about étale
sheaves on their stalks; it is restricted to `forget A` so that instance search never
considers it for goals mentioning an unknown functor. -/
instance Etale.hasSheafCompose_forget_smallEtaleTopology :
    Y.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A) :=
  Etale.hasSheafCompose_smallEtaleTopology A Y _

section Monoidal

/- The monoidal structure on the coefficient category, whose tensor product commutes
with filtered colimits in each variable. The latter hypothesis makes the tensor product
of presheaves interact well with the stalks at the points of the small étale site; it
holds in the intended applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`, where the
tensor product commutes with all colimits. -/
variable [MonoidalCategory A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]

/-- The class `Y.smallEtaleTopology.W` of morphisms of `A`-valued étale presheaves
inverted by sheafification is monoidal: this is checked on the stalks at the geometric
points of `Y`, which form a conservative family of points of the small étale site. -/
instance Etale.isMonoidal_W_smallEtaleTopology :
    (Y.smallEtaleTopology.W (A := A)).IsMonoidal := by
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty.{u} Y.smallEtaleTopology
  exact hP.isMonoidal_W A

/-- The monoidal structure on `A`-valued étale sheaves induced by a monoidal structure
on the coefficient category `A`: the sheafification of the objectwise tensor product of
presheaves. -/
noncomputable instance Etale.sheafMonoidalCategory :
    MonoidalCategory (Sheaf Y.smallEtaleTopology A) :=
  Sheaf.monoidalCategory _ _

/-- The monoidal structure on étale sheaves is preadditive when the one on the
coefficient category is. -/
instance Etale.sheafMonoidalPreadditive [MonoidalPreadditive A] :
    MonoidalPreadditive (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Existence of `ℤ`-indexed coproducts of étale sheaves, induced by the corresponding
condition on the coefficient category. Via
`ComplexShape.hasColimitsOfShape_discrete_π_up_int`, this provides the coproducts
defining the tensor product of complexes of étale sheaves, whose indexing fibers
`(ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {j}` are in
bijection with `ℤ`. -/
instance Etale.sheafHasCoproductsOfShapeInt [HasColimitsOfShape (Discrete ℤ) A] :
    HasColimitsOfShape (Discrete ℤ) (Sheaf Y.smallEtaleTopology A) :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasTensor₄ObjExt
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensor₁₂Tensor
    [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    (X₁ X₂ X₃ : GradedObject ℤ (Sheaf Y.smallEtaleTopology A)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  sorry

/-- Compatibility of the tensor product of graded étale sheaves with coproducts,
induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafHasGoodTensorTensor₂₃
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
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorObj
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ ((curriedTensor (Sheaf Y.smallEtaleTopology A)).obj X) :=
  sorry

/-- Preservation of `ℤ`-indexed colimits by the tensor product of étale sheaves in the
second variable, induced by the corresponding condition on the coefficient category. -/
instance Etale.sheafPreservesColimitsOfShapeCurriedTensorFlipObj
    [∀ (X : A), PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X)]
    (X : Sheaf Y.smallEtaleTopology A) :
    PreservesColimitsOfShape ℤ
      ((curriedTensor (Sheaf Y.smallEtaleTopology A)).flip.obj X) :=
  sorry

/-- Functorial flat resolutions of étale sheaves: for module coefficients these are
given by the functorial local free covers `⊕ j_{U!} Λ_U` (Stacks Project, Tag 06YL). -/
instance Etale.sheafHasFunctorialFlatResolution
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  sorry

end Monoidal

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

/- The preadditive monoidal structure on the coefficient category, whose tensor
product commutes with filtered colimits in each variable (as it does in the intended
applications `A = Ab.{u}` and `A = ModuleCat.{u} Λ`); the latter hypothesis is what
allows the monoidal structure to descend to the étale sheaf categories via the stalk
functors, see the section `SheafInstances`. -/
variable [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]

/- Existence of the coproducts defining the tensor product of complexes (the indexing
fibers of the total degree map are in bijection with `ℤ`, see
`ComplexShape.hasColimitsOfShape_discrete_π_up_int`), and its compatibility with the
tensor product, on the coefficient category. -/
variable [HasColimitsOfShape (Discrete ℤ) A]
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

section DerivedUpperLowerStarAdjunction

/-!
## The derived adjunction `Lg^* ⊣ Rg_*`

The adjunction `g^* ⊣ g_*` between the pullback and the pushforward of étale sheaves
induces an adjunction `Lg^* ⊣ Rg_*` between their total derived functors on the
unbounded derived categories, by
`CategoryTheory.Adjunction.derivedAdjunction`
(`WeilConjectures.DerivedCategory.Adjunction`): the left adjoint is
derived via the K-flat left derivability structure on `D(Y_ét)` and the right adjoint
via the K-injective right derivability structure on `D(Z_ét)`, and the two
"absoluteness" hypotheses of mathlib's abstract theorem `Adjunction.derived` hold
because the derived-functor comparison maps are isomorphisms on K-flat, respectively
K-injective, complexes.

The hypotheses of this section are those of the section `DerivedUpperStar`: the
K-injective resolutions on the pushforward side are supplied by the sheaf category
being Grothendieck abelian.
-/

open MonoidalCategory

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
variable [HasWeakSheafify Z.smallEtaleTopology A]
variable [HasDerivedCategory.{w} (Sheaf Y.smallEtaleTopology A)]
variable [HasDerivedCategory.{w'} (Sheaf Z.smallEtaleTopology A)]
variable [∀ F : Y.Etaleᵒᵖ ⥤ A,
  (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension F]
variable [MonoidalCategory A] [MonoidalPreadditive A]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorLeft X)]
  [∀ (X : A), PreservesFilteredColimitsOfSize.{u, u} (tensorRight X)]
variable [HasColimitsOfShape (Discrete ℤ) A]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
variable [HasColimitsOfShape ℤ A] [HasExactColimitsOfShape ℤ A]
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

end AlgebraicGeometry
