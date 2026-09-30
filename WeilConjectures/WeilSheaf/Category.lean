/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.NumberTheory.Padics.Complex
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.Endofunctor.Shift
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-!
# Weil sheaves and Weil complexes

Let `k₀` be a finite field, `X` a scheme over `k₀`, `X̄ = X ×_{k₀} k̄` its geometric fiber
and `Fr_X = 𝟙 × σ : X̄ ≅ X̄` its geometric Galois Frobenius
(`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`). A *Weil sheaf* on `X` is a
constructible étale `ℚ̄_ℓ`-sheaf `F` on `X̄` together with an isomorphism
`φ : Fr_X^* F ≅ F`; a *Weil complex* is an object `K` of the derived category `D(X̄_ét)` with
bounded constructible homology together with an isomorphism `φ : Fr_X^* K ≅ K`. Both are
full subcategories of the categories `CategoryTheory.Endofunctor.IsoAlgebra` of the
pullback endofunctor `Fr_X^*` and of its derived functor.

Weil sheaves form an abelian category, Weil complexes an additive category with a shift. A
Weil sheaf is a Weil complex concentrated in degree zero (`WeilSheaf.toComplex`), the
cohomology sheaves `𝓗ᵃ` of a Weil complex are Weil sheaves (`WeilComplex.homologySheaf`),
and both notions pull back along morphisms of `k₀`-schemes (`WeilSheaf.upperStar`,
`WeilComplex.upperStar`), the base change `X̄ ⟶ Ȳ` commuting with the Frobenii.

## Main definitions

- `AlgebraicGeometry.WeilCoefficients`: the category of modules over `ℚ̄_ℓ`, lifted to the
  universe of the étale sites.
- `AlgebraicGeometry.WeilSheaf` and `AlgebraicGeometry.WeilComplex`: the category of
  constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme and the category of Weil complexes.
- `AlgebraicGeometry.WeilSheaf.toComplex` and `AlgebraicGeometry.WeilComplex.homologySheaf`.
- `AlgebraicGeometry.WeilSheaf.IsLisse`: the underlying sheaf is locally constant.
- `AlgebraicGeometry.WeilSheaf.upperStar` and `AlgebraicGeometry.WeilComplex.upperStar`.

## Implementation notes

The coefficient ring `ℚ̄_ℓ = PadicAlgCl l` lives in `Type`, while Mathlib's
`IsGrothendieckAbelian.{v} (ModuleCat.{v} R)` needs `R : Type v`; hence the `ULift` in
`AlgebraicGeometry.WeilCoefficients`. Constructible sheaves of abstract `ℚ̄_ℓ`-modules and
lisse as `Scheme.IsLocallyConstantSheaf` are the conventions of the six-functor layer.

Weil complexes live in the unbounded derived category `D(X̄_ét)`, whose functor
`Functor.mapDerivedCategory` is additive and commutes with the shifts. Their carriers are
bounded, so they are objects of the bounded below derived category on the nose.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open Etale

/-- The coefficients of Weil sheaves: modules over `ℚ̄_ℓ`, lifted to `Type (u + 1)`. -/
abbrev WeilCoefficients (l : ℕ) [Fact l.Prime] : Type (u + 2) :=
  ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l))

/-- The category of constructible Weil `ℚ̄_ℓ`-sheaves on a `k₀`-scheme `X`: constructible
étale sheaves `F` of `ℚ̄_ℓ`-modules on the geometric fiber `X̄` with an isomorphism
`Fr_X^* F ≅ F`, where `Fr_X` is the geometric Galois Frobenius of `X̄`. -/
def WeilSheaf (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type (u + 2) :=
  ((Etale.constructibleSheaf (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l])).FullSubcategory

/-- The category of Weil complexes on a `k₀`-scheme `X`: objects `K` of the derived category
of étale sheaves of `ℚ̄_ℓ`-modules on the geometric fiber `X̄` with bounded constructible
homology, with an isomorphism `Fr_X^* K ≅ K`, where `Fr_X` is the geometric Galois Frobenius
of `X̄`. -/
def WeilComplex (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    Type (u + 2) :=
  ((Etale.DerivedCategory.boundedConstructible (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l].mapDerivedCategory)).FullSubcategory

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

noncomputable instance : Category (WeilSheaf k₀ l X) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

/-- The closure of constructible sheaves under finite products, transported to Weil sheaves;
it is found on its own, but not within the search for `Abelian (WeilSheaf k₀ l X)`. -/
instance : ((Etale.constructibleSheaf (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l])).IsClosedUnderFiniteProducts :=
  inferInstance

noncomputable instance : Abelian (WeilSheaf k₀ l X) :=
  inferInstanceAs (Abelian ((Etale.constructibleSheaf (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l])).FullSubcategory)

-- Stated after the `Abelian` instance, so that it is the one found for `Preadditive`: it
-- unfolds to the preadditive structure of the full subcategory at instance transparency.
noncomputable instance : Preadditive (WeilSheaf k₀ l X) :=
  inferInstanceAs (Preadditive (ObjectProperty.FullSubcategory _))

noncomputable instance : Category (WeilComplex k₀ l X) :=
  inferInstanceAs (Category (ObjectProperty.FullSubcategory _))

noncomputable instance : Preadditive (WeilComplex k₀ l X) :=
  inferInstanceAs (Preadditive (ObjectProperty.FullSubcategory _))

noncomputable instance : HasShift (WeilComplex k₀ l X) ℤ :=
  inferInstanceAs (HasShift ((Etale.DerivedCategory.boundedConstructible (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).inverseImage (IsoAlgebra.forget
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l].mapDerivedCategory)).FullSubcategory ℤ)

namespace WeilSheaf

/-- A Weil sheaf, viewed as a Weil complex concentrated in degree zero. -/
noncomputable def toComplex : WeilSheaf k₀ l X ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l].mapDerivedCategorySingleFunctor 0))
    fun F ↦ by
      have := F.property
      change Etale.DerivedCategory.boundedConstructible _ _
        ((DerivedCategory.singleFunctor _ 0).obj F.obj.carrier)
      refine ⟨⟨⟨0, inferInstanceAs (DerivedCategory.IsGE _ 0)⟩,
        ⟨0, inferInstanceAs (DerivedCategory.IsLE _ 0)⟩⟩, fun n ↦ ?_⟩
      obtain hn | rfl | hn := lt_trichotomy n 0
      · exact Scheme.IsConstructibleSheaf.of_isZero
          ((DerivedCategory.isGE_iff _ 0).1 inferInstance n hn)
      · have : Scheme.IsConstructibleSheaf ((𝟭 _).obj F.obj.carrier) := F.property
        exact Scheme.IsConstructibleSheaf.of_iso
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F.obj.carrier).symm
      · exact Scheme.IsConstructibleSheaf.of_isZero
          ((DerivedCategory.isLE_iff _ 0).1 inferInstance n hn)

instance : (toComplex (k₀ := k₀) (l := l) (X := X)).Additive := by
  -- `WeilSheaf` and `WeilComplex` are not reducible, so these instances are not found by search
  unfold toComplex
  exact @Functor.instAdditiveFullSubcategoryLift _ _ _ _ _ _ _
    (@Functor.instAdditiveComp _ _ _ _ _ _ _ (Functor.fullSubcategoryInclusion_additive _) _ _ _
      _ (IsoAlgebra.additive_mapOfNatIso _)) _ _

/-- A Weil sheaf is *lisse* if its underlying étale sheaf is locally constant; it is then
finite locally constant, being constructible. -/
def IsLisse (F : WeilSheaf k₀ l X) : Prop :=
  Scheme.IsLocallyConstantSheaf F.obj.carrier

end WeilSheaf

namespace WeilComplex

/-- The `a`-th cohomology sheaf `𝓗ᵃK` of a Weil complex, in cohomological indexing, with the
Weil structure induced by that of `K`. -/
noncomputable def homologySheaf (a : ℤ) : WeilComplex k₀ l X ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ IsoAlgebra.mapOfNatIso
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
        l].mapDerivedCategoryHomologyFunctorIso a))
    fun K ↦ K.property.2 a

instance (a : ℤ) : (homologySheaf (k₀ := k₀) (l := l) (X := X) a).Additive := by
  -- `WeilSheaf` and `WeilComplex` are not reducible, so these instances are not found by search
  unfold homologySheaf
  exact @Functor.instAdditiveFullSubcategoryLift _ _ _ _ _ _ _
    (@Functor.instAdditiveComp _ _ _ _ _ _ _ (Functor.fullSubcategoryInclusion_additive _) _ _ _
      _ (IsoAlgebra.additive_mapOfNatIso _)) _ _

end WeilComplex

section UpperStar

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

/-- The pullback along the base change `φ̄ : X̄ ⟶ Ȳ` of a morphism `φ` of `k₀`-schemes commutes
with the pullbacks along the geometric Galois Frobenii: `φ̄^* ⋙ Fr_X^* ≅ Fr_Y^* ⋙ φ̄^*`, since
`φ̄ ≫ Fr_Y = Fr_X ≫ φ̄`. -/
noncomputable def WeilSheaf.upperStarFrobeniusIso :
    ((Scheme.Hom.geometricFiberMap φ (comp_over φ _)))^*[WeilCoefficients.{u} l] ⋙
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l] ≅
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l] ⋙
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _)))^*[WeilCoefficients.{u} l] :=
  (Etale.upperStarComp _ _ _ _
      (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ _))).symm ≪≫
    Etale.upperStarComp _ _ _

/-- The pullback `φ^*` of Weil sheaves along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`WeilSheaf.upperStarFrobeniusIso`. -/
noncomputable def WeilSheaf.upperStar : WeilSheaf k₀ l Y ⥤ WeilSheaf k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙
      IsoAlgebra.mapOfNatIso (WeilSheaf.upperStarFrobeniusIso φ))
    fun F ↦
      have : Scheme.IsConstructibleSheaf F.obj.carrier := F.property
      Scheme.IsConstructibleSheaf.upperStar (Scheme.Hom.geometricFiberMap φ (comp_over φ _))
        F.obj.carrier

instance : (WeilSheaf.upperStar (k₀ := k₀) (l := l) φ).Additive := by
  unfold WeilSheaf.upperStar
  exact @Functor.instAdditiveFullSubcategoryLift _ _ _ _ _ _ _
    (@Functor.instAdditiveComp _ _ _ _ _ _ _ (Functor.fullSubcategoryInclusion_additive _) _ _ _
      _ (IsoAlgebra.additive_mapOfNatIso _)) _ _

/-- The derived form of `WeilSheaf.upperStarFrobeniusIso`:
`D(φ̄^*) ⋙ D(Fr_X^*) ≅ D(Fr_Y^*) ⋙ D(φ̄^*)`. -/
noncomputable def WeilComplex.upperStarFrobeniusIso :
    ((Scheme.Hom.geometricFiberMap φ (comp_over φ _)))^*[WeilCoefficients.{u}
          l].mapDerivedCategory ⋙
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
          l].mapDerivedCategory ≅
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u}
          l].mapDerivedCategory ⋙
        ((Scheme.Hom.geometricFiberMap φ (comp_over φ _)))^*[WeilCoefficients.{u}
          l].mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (WeilSheaf.upperStarFrobeniusIso φ) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The pullback `φ^*` of Weil complexes along a morphism `φ : X ⟶ Y` of `k₀`-schemes: the
derived pullback along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure transported along
`WeilComplex.upperStarFrobeniusIso`. -/
noncomputable def WeilComplex.upperStar : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙
      IsoAlgebra.mapOfNatIso (WeilComplex.upperStarFrobeniusIso φ))
    fun K ↦ ⟨Functor.bounded_mapDerivedCategory_obj _ K.property.1, fun n ↦
      have : Scheme.IsConstructibleSheaf
          ((DerivedCategory.homologyFunctor _ n).obj K.obj.carrier) := K.property.2 n
      have : Scheme.IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ n ⋙
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ _)))^*[WeilCoefficients.{u} l]).obj
            K.obj.carrier) :=
        Scheme.IsConstructibleSheaf.upperStar _ _
      Scheme.IsConstructibleSheaf.of_iso
        ((Functor.mapDerivedCategoryHomologyFunctorIso _ n).app K.obj.carrier)⟩

instance : (WeilComplex.upperStar (k₀ := k₀) (l := l) φ).Additive := by
  unfold WeilComplex.upperStar
  exact @Functor.instAdditiveFullSubcategoryLift _ _ _ _ _ _ _
    (@Functor.instAdditiveComp _ _ _ _ _ _ _ (Functor.fullSubcategoryInclusion_additive _) _ _ _
      _ (IsoAlgebra.additive_mapOfNatIso _)) _ _

end UpperStar

end AlgebraicGeometry
