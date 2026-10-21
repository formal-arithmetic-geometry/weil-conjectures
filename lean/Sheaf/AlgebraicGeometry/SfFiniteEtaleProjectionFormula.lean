/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Sheaf.AlgebraicGeometry.SfEtaleExchanges
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage

/-!
# The finite-coefficient compact-support projection formula on the small etale site

Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sf-pf-finite/_section.md`, order 1706 (blueprint: sk-thm-sf-pf-finite).

The projection is the published natural transformation of etale bifunctors for the
chosen compactification. Its two endpoints belong to the full bounded-below subcategory;
therefore invertibility of its component is invertibility in D+. Naturality in both
arguments is retained from this bifunctor transformation. Only L has finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CommRing.toRing
attribute [local irreducible] HomologicalComplex₂.total
  projectionMapOfCompactification rightDerivedLowerStarProjectionMap
  derivedTensorRightDerivedLowerShriek rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
  derivedTensorRightDerivedLowerStar rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar

set_option backward.isDefEq.respectTransparency false in
private theorem finite_projection_iso
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ Y) :
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L) := by
  have := isIso_rightDerivedLowerStarProjectionMap_of_isProper Λ isAddTorsion_of_finite c.g
  exact hasProjectionFormulaOfCompactification_of_isIso (ModuleCat.{u + 1} Λ) c K L
    (NatIso.isIso_app_of_isIso
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) c.g).app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory.obj K)) L)

set_option backward.isDefEq.respectTransparency false in
private theorem compact_support_lower_bound
    (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule Λ X) (k : ℤ) [K.IsGE k] :
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K).IsGE k := by
  have : ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) c.i).mapDerivedCategory.obj K).IsGE k :=
    Functor.isGE_mapDerivedCategory_obj _ K k
  exact Functor.isGE_rightDerivedFunctor_obj (lowerStar (ModuleCat.{u + 1} Λ) c.g) _ k

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_right_bound
    {C : Type v} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {a b : ℤ} {L : _root_.DerivedCategory C}
    (hL : _root_.DerivedCategory.torAmplitudeIn C a b L)
    (M : _root_.DerivedCategory C) (d : ℤ) [M.IsGE d] :
    (M ⊗ L).IsGE (a + d) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory C
  have := _root_.DerivedCategory.isGE_tensor_of_torAmplitudeIn hL M d
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso (β_ L M) (a + d)

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_plus_coefficients
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (Y : Scheme.{u}) (M L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (d : ℤ) [M.IsGE d] (a b : ℤ)
    (ht : _root_.DerivedCategory.torAmplitudeIn (Sheaf Y.smallEtaleTopology A) a b L) :
    _root_.DerivedCategory.TStructure.t.plus (((derivedTensor A Y).obj M).obj L) := by
  exact ⟨a + d, tensor_right_bound ht M d⟩

set_option backward.isDefEq.respectTransparency false in
private theorem finite_projection_plus
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule Λ X) (L : DerivedCategoryModule Λ Y)
    (hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (hLt : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn Λ Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} Λ) c).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} Λ) c).obj K).obj L) ∧
    IsIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L) := by
  have hprojection := finite_projection_iso Λ c K L
  obtain ⟨k, _, _, hK⟩ := hKb
  have : K.IsGE k :=
    (_root_.DerivedCategory.isGE_iff K k).2 (fun i hi ↦ hK i (.inl hi))
  have : ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K).IsGE k :=
    compact_support_lower_bound Λ c K k
  obtain ⟨a, b, ht⟩ := hLt
  have ht' : _root_.DerivedCategory.torAmplitudeIn
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) a b L :=
    (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn
      (Λ := Λ) (X := Y) (a := a) (b := b) (K := L)).mp ht
  have hsource' := tensor_plus_coefficients (ModuleCat.{u + 1} Λ) Y
    ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) c).obj K) L k a b ht'
  have hsource : _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek (ModuleCat.{u + 1} Λ) c).obj K).obj L) := by
    simpa only [derivedTensorRightDerivedLowerShriek_obj_obj] using hsource'
  exact ⟨hsource, _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    (asIso (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app K).app L))
    hsource, hprojection⟩

set_option backward.isDefEq.respectTransparency false in
/-- The finite-coefficient projection transformation is an isomorphism in D+,
natural in both bounded constructible inputs, with finite Tor amplitude only for L.
The compactification is the chosen factorization used to define the projection.
Constructibility is exactly the recorded set-sheaf predicate on each cohomology sheaf.
Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-thm-sf-pf-finite/_section.md`, order 1706 (blueprint: sk-thm-sf-pf-finite).

Proof: the positive-level coefficient ring is finite, hence additively torsion.
The existing proper projection theorem applies to the proper factor c.g without
boundedness or constructibility assumptions. The component formula for the canonical
compact-support projection expresses it as this proper projection followed by the
images of the open-extension tensor and pullback-composition isomorphisms. Therefore
the specified projection component is invertible.

The lower cohomology bound of K is preserved by exact open extension and then by
the left t-exact right derived proper pushforward, so Rf!K belongs to D+.
The Tor-amplitude tensor estimate applied to L and Rf!K, followed by the derived
braiding, puts Rf!K tensor L in D+. Transport this property along the actual
projection isomorphism to put its target in D+ as well. Since D+ is full, this
is invertibility in D+. Naturality is inherited from sfEtaleProjection. -/
theorem sf_finite_etale_projection_formula
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) Y)
    (_hKc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj K)))
    (_hKb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj K))
    (_hLc : ∀ i : ℤ, Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose Y.smallEtaleTopology
        (CategoryTheory.forget (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))).obj
        ((_root_.DerivedCategory.homologyFunctor _ i).obj L)))
    (_hLb : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ i).obj L))
    (_hLt : ∃ a b : ℤ,
      DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing l E n) Y a b L) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensorRightDerivedLowerShriek
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    _root_.DerivedCategory.TStructure.t.plus
      (((rightDerivedLowerShriekDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) c).obj K).obj L) ∧
    IsIso (((sfEtaleProjection (Padic.coefficientExtensionRing l E n) c).app K).app L) := by
  have := Padic.finite_coefficientExtensionRing l E n _hn
  simpa only [sfEtaleProjection] using
    (finite_projection_plus (Padic.coefficientExtensionRing l E n) c K L _hKb _hLt)

end AlgebraicGeometry.Etale
