/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.AffineSpaceZeroSectionConstructions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula

/-! # Coordinate products and recursive exceptional adjuncts

Source: blueprint main-20261015, cor-pur-affine-space-zero-section-purity,
proof Steps 5 and 7 (blueprint: def-pur-coordinate-section-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

/-- The coordinate zero immersion is proper, so its existing proper compactification
is available. Source: coordinate geometry
(blueprint: def-pur-coordinate-section-projection). -/
instance zero_compactification (B : Scheme.{u}) (c : ℕ) :
    HasCompactification (zero B c) :=
  letI := zero_closed B c
  HasCompactification.of_isProper (zero B c)

/-- The last-coordinate zero section in the recorded affine tower.
Source: coordinate tower (blueprint: def-pur-coordinate-section-projection). -/
abbrev lastSection (B : Scheme.{u}) (r : ℕ) :
    iteratedAffineLine B r ⟶ iteratedAffineLine B (r + 1) :=
  zero (iteratedAffineLine B r) 1

/-- Reuse its proper compactification, with the same zero-section morphism.
Source: coordinate geometry (blueprint: def-pur-coordinate-section-projection). -/
instance lastSection_compactification (B : Scheme.{u}) (r : ℕ) :
    HasCompactification (lastSection B r) := zero_compactification (iteratedAffineLine B r) 1

/-- The coefficient unit identified by the constant-sheaf monoidal unit comparison.
Source: coefficient normalization
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def coefficientUnitIso (P : PurityFiniteSetting.{u}) (n : ℕ) (X : Scheme.{u}) :
    unit P n X ≅ 𝟙_ (D P n X) :=
  (cupSingle (setting P n) X).mapIso (cupConstantIso (setting P n) X) ≪≫
    (cupSingle (setting P n) X).mapIso
      (Functor.Monoidal.εIso
        (constantSheaf (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} (setting P n).Coefficient))).symm ≪≫
    DerivedCategory.singleFunctorObjUnitIso _

/-- Pullback along a zero section cancels its own affine projection canonically.
Source: the projection identification
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def sectionPullbackIso (A : Type (u + 1)) [CommRing A]
    (B : Scheme.{u}) (r : ℕ) :
    inverseImage A (lastProjection B r) ⋙ inverseImage A (lastSection B r) ≅ 𝟭 _ :=
  (inverseImageComp A (lastSection B r) (lastProjection B r)).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0)) ≪≫
    inverseImageId A _

/-- The recorded derived bifunctor has the object part of the canonical monoidal
structure. Source: derived tensor construction
(blueprint: def-pur-coordinate-section-projection).
Proof: unfold tensor and derivedTensor; both are curriedTensor for the canonical
K-flat derived monoidal structure. This equality only exposes that same object. -/
theorem tensorObject_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (M N : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((tensor A X).obj M).obj N = M ⊗ N := by
  rfl

/-- Left-unit normalization with the derived tensor's cached object expression.
Source: canonical unit identification
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def tensorUnitLeftIso (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ((tensor A X).obj (𝟙_ _)).obj K ≅ K :=
  eqToIso (tensorObject_eq A X (𝟙_ _) K) ≪≫ λ_ K

/-- Normalize the source of the proper projection at a section, before specializing
coefficients. Source: proper projection and unit identifications
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def sectionTensorRaw (A : Type (u + 1)) [CommRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) :
    ((tensor A Y).obj M).obj
      ((inverseImage A s).obj ((inverseImage A q).obj K)) ≅ K :=
  tensorIso A Y e
    (((inverseImageComp A s q).symm ≪≫
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) h ≪≫ inverseImageId A Y).app K) ≪≫
    tensorUnitLeftIso A Y K

/-- Compose a map with a supplied isomorphism, with category parameters cached.
Source: functoriality of the projection endpoint normalization
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def projectionPostcompose {C : Type v} [Category.{w} C] {X Y Z : C}
    (p : X ⟶ Y) (e : Y ≅ Z) : X ⟶ Z := p ≫ e.hom

/-- Postcomposition by an isomorphism preserves invertibility.
Source: functoriality of the projection endpoint normalization
(blueprint: def-pur-coordinate-section-projection).
Proof: the given map and the hom of the supplied isomorphism are invertible;
their composite is invertible. -/
theorem projectionPostcompose_isIso {C : Type v} [Category.{w} C] {X Y Z : C}
    (p : X ⟶ Y) (e : Y ≅ Z) (hp : IsIso p) :
    IsIso (projectionPostcompose p e) := by
  unfold projectionPostcompose
  exact IsIso.comp_isIso' hp e.isIso_hom

/-- The projection component before its section endpoint normalization.
Source: displayed proper projection (blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def sectionProjectionComponent (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s] (q : X ⟶ Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))) :=
  (((projectionMap (ModuleCat.{u + 1} A) s).app M).app ((inverseImage A q).obj K))

/-- The precise counit-defined proper projection with its canonical unit endpoint.
Source: displayed projection (blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def sectionProjectionRaw (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) :
    ((tensor A X).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj M)).obj
        ((inverseImage A q).obj K) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj K :=
  projectionPostcompose
    (sectionProjectionComponent A s q M K)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).mapIso
      (sectionTensorRaw A s q h M K e))

attribute [local irreducible] projectionMap

/-- The raw section projection is invertible when its projection component is.
Source: proper projection followed by canonical endpoint normalization
(blueprint: def-pur-coordinate-section-projection).
Proof: the endpoint normalization is the functorial image of an isomorphism.
Compose it with the supplied invertible projection component. -/
theorem sectionProjectionRaw_isIso (A : Type (u + 1)) [CommRing A]
    [IsNoetherianRing A] {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) (hp : IsIso (sectionProjectionComponent A s q M K)) :
    IsIso (sectionProjectionRaw A s q h M K e) := by
  unfold sectionProjectionRaw
  exact projectionPostcompose_isIso _ _ hp

/-- Finite-Tor applicability makes the raw section projection invertible.
Source: finite-coefficient projection formula and exact inverse image
(blueprint: def-pur-coordinate-section-projection).
Proof: inverse image preserves finite-Tor constructibility. Apply the finite-ring
projection formula to M and the pullback of K, then the canonical normalization. -/
theorem sectionProjectionRaw_isIso_of_constructibleFiniteTor
    (A : Type (u + 1)) [CommRing A] [Finite A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) (hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y M)
    (hK : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) Y K) :
    IsIso (sectionProjectionRaw A s q h M K e) := by
  have hL := constructibleFiniteTor_leftDerivedFunctor_upperStar_obj q hK
  have hp : IsIso (sectionProjectionComponent A s q M K) := by
    unfold sectionProjectionComponent
    exact hasProjectionFormula_of_constructibleFiniteTor A s hM hL
  exact sectionProjectionRaw_isIso A s q h M K e hp

/-- The actual projection component at the last zero section and W_r.
Source: displayed proper projection
(blueprint: def-pur-coordinate-section-projection). -/
@[irreducible]
def sectionProjection (P : PurityFiniteSetting.{u}) (n : ℕ) (B : Scheme.{u}) (r : ℕ) :=
  letI : IsNoetherianRing (setting P n).Coefficient :=
    isNoetherian_of_finite (setting P n).Coefficient (setting P n).Coefficient
  sectionProjectionRaw (setting P n).Coefficient (lastSection B r) (lastProjection B r)
    (Scheme.Hom.toIteratedAffineLine_comp_over (𝟙 _) (fun _ ↦ 0))
    (unit P n (iteratedAffineLine B r)) (target P n (iteratedAffineLine B r) r)
    (coefficientUnitIso P n _)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
