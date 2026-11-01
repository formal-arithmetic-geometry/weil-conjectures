/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModuleOpenPasting.ModuleDirectImageOpenPasting
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.ClopenLocalization.ProEtaleClopenUnboundedDerivedLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.CompositionAdjunctionNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperMateLaws
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperOpenLaws

/-! # Open exchange and proper/open pasting for condensed modules

Source: latest blueprint, sk-thm-sf-comp-composition.proof.md, canonicity,
associativity and base change; Stacks Tags 09AH and 0F7B--0F7F
(blueprint: lem-zl-condensed-open-proper-pasting).

The package below records exactly the canonical normalized comparisons and their laws
on full unbounded derived categories. Component equations include all compositors;
functor associators have identity components. No proper exchange is inverted.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The full unbounded internal-module derived category, in the fixed site universes.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
abbrev D (X : Scheme.{u}) :=
  DerivedCategory (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj Λ X))

/-- The exact model D(f*) of the recorded total derived pullback.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) := (upperStar Λ f).mapDerivedCategory

/-- The recorded total derived direct image of the full module pushforward.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
abbrev R {X Y : Scheme.{u}} (f : X ⟶ Y) := moduleObjectDerivedPushforward Λ f

/-- Exact derived open extension with its existing linear module action.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
abbrev J {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :=
  (openImmersionLowerShriek Λ j).mapDerivedCategory

/-- Canonical derived restriction composition, from the existing ordinary comparison.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    P Λ (f ≫ g) ≅ P Λ g ⋙ P Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The specified identity restriction comparison.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def pId (X : Scheme.{u}) : P Λ (𝟙 X) ≅ 𝟭 (D Λ X) :=
  Functor.mapDerivedCategoryNatIso (upperStarId Λ X) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The specified direct-image compositor, conjugate to canonical restriction composition.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def rComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R Λ f ⋙ R Λ g ≅ R Λ (f ≫ g) :=
  (conjugateIsoEquiv
    (upperStarLowerStarAdjunction Λ (f ≫ g)).mapDerivedCategoryRightDerivedAdjunction
    ((upperStarLowerStarAdjunction Λ g).mapDerivedCategoryRightDerivedAdjunction.comp
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction)
    (pComp Λ f g).symm).symm

/-- The corresponding identity direct-image comparison.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def rId (X : Scheme.{u}) : R Λ (𝟙 X) ≅ 𝟭 (D Λ X) :=
  conjugateIsoEquiv
    (upperStarLowerStarAdjunction Λ (𝟙 X)).mapDerivedCategoryRightDerivedAdjunction
    Adjunction.id (pId Λ X).symm

/-- Open composition is the conjugate of the restriction compositor under the open adjunctions.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def jComp {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] : J Λ j ⋙ J Λ i ≅ J Λ (j ≫ i) :=
  ((conjugateIsoEquiv
    ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).comp
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i))
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i))).symm
      (pComp Λ j i).symm).symm

/-- The identity open comparison, fixed by its restriction normalization.
Source: latest blueprint composition proof (blueprint: lem-zl-condensed-open-proper-pasting). -/
def jId (X : Scheme.{u}) : J Λ (𝟙 X) ≅ 𝟭 (D Λ X) :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
    (pId Λ X)).leftAdjointUniq Adjunction.id

/-- The normalized inverse mate: insert the open unit, transport around the square,
then contract the other open counit. Its square comparison is the existing exact comparison.
Source: latest blueprint base-change paragraph (blueprint: lem-zl-condensed-open-proper-pasting). -/
def openMap {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : CommSq a j' j b) : P Λ a ⋙ J Λ j' ⟶ J Λ j ⋙ P Λ b :=
  ((mateEquiv (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j')).symm
    (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).inv)).natTrans

/-- A total inverse operation: it is the unique inverse on invertible comparisons and zero
otherwise. Only its invertible branch is used on the squares whose restriction is asserted
invertible. Totality allows outer mixed pastes without adding a Cartesian/proper hypothesis.
Source: latest blueprint canonicity paragraph (blueprint: lem-zl-condensed-open-proper-pasting). -/
def comparisonInverse {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
    {A B : C} (f : A ⟶ B) : B ⟶ A := by
  classical
  exact if h : IsIso f then @inv _ _ _ _ f h else 0

/-- The two classes of squares in part (b): Cartesian, or with both verticals proper.
Source: latest blueprint composition paragraph; Stacks 0F7B
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def IsAdmissibleSquare {U W Y Z : Scheme.{u}}
    (j : U ⟶ W) (p : U ⟶ Y) (r : W ⟶ Z) (i : Y ⟶ Z) : Prop :=
  IsPullback j p r i ∨ (IsProper p ∧ IsProper r)

/-- The invertible specified open units, with their precise adjunction normalization.
Source: latest blueprint composition paragraph (blueprint: lem-zl-condensed-open-proper-pasting). -/
structure OpenUnits where
  /-- The specified open unit is an isomorphism on the full unbounded category. -/
  unitIso : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j],
    𝟭 (D Λ U) ≅ J Λ j ⋙ P Λ j
  /-- Its forward map is exactly the published derived open-adjunction unit. -/
  normalized : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j],
    (unitIso j).hom = (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).unit

/-- Lambda: ambient open restriction of direct image followed by inverse open unit.
Source: latest blueprint composition paragraph; Stacks 0F7B
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def restriction (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] (sq : CommSq j p r i) :
    (J Λ j ⋙ R Λ r) ⋙ P Λ i ⟶ R Λ p :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j) (derivedDirectImageOpenRestriction Λ sq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (units.unitIso j).inv (R Λ p) ≫ (Functor.leftUnitor _).hom

/-- Gamma: the open-adjunction transpose of inverse Lambda. The total inverse merely
extends the expression to outer mixed pastes; invertibility on every input square of (b)
is asserted separately. Naturality is part of the natural-transformation type.
Source: latest blueprint composition paragraph (blueprint: lem-zl-condensed-open-proper-pasting). -/
def gamma (units : OpenUnits Λ)
    {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] (sq : CommSq j p r i) :
    R Λ p ⋙ J Λ i ⟶ J Λ j ⋙ R Λ r :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (comparisonInverse (restriction Λ units sq)) (J Λ i) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (J Λ j ⋙ R Λ r)
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).counit ≫
    (Functor.rightUnitor _).hom

/-- Equality transport for open extension, retaining the canonical scheme identifications.
Source: latest blueprint associativity paragraph
(blueprint: lem-zl-condensed-open-proper-pasting). -/
def jCongr {X Y : Scheme.{u}} {j i : X ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion i]
    (h : j = i) : J Λ j ≅ J Λ i := by
  subst i
  exact Iso.refl _

/-- The normalized maps and every identity, associativity, pasting and cube law of (a)--(c).
All maps live on the full unbounded categories; no field of definition is present.
Source: latest blueprint composition proof; Stacks 09AH and 0F7B--0F7F
(blueprint: lem-zl-condensed-open-proper-pasting). -/
structure Pasting where
  /-- The specified invertible open units. -/
  units : OpenUnits Λ
  /-- Normalized open exchange on every Cartesian open square, without quasi-compactness. -/
  B : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j'],
    IsPullback a j' j b → (J Λ j ⋙ P Λ b ≅ P Λ a ⋙ J Λ j')
  /-- B is the inverse of exactly the specified unit--square--counit transformation. -/
  B_normalized : ∀ {U' U W' W : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ W'}
    {j : U ⟶ W} {b : W' ⟶ W} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback a j' j b), (B sq).inv = openMap Λ sq.toCommSq
  /-- Identity vertical maps give the canonical identity exchange. -/
  B_id : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j]
    (sq : IsPullback (𝟙 U) j j (𝟙 W)) (K : D Λ U),
    (B sq).hom.app K = (pId Λ W).hom.app ((J Λ j).obj K) ≫
      (J Λ j).map ((pId Λ U).inv.app K)
  /-- Identity opens give the canonical identity exchange. -/
  B_open_id : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sq : IsPullback f (𝟙 X) (𝟙 Y) f) (K : D Λ Y),
    (B sq).hom.app K = (P Λ f).map ((jId Λ Y).hom.app K) ≫
      (jId Λ X).inv.app ((P Λ f).obj K)
  /-- Cartesian pasting along successive arbitrary base maps. -/
  B_vertical : ∀ {U₀ U₁ U₂ W₀ W₁ W₂ : Scheme.{u}}
    {a₁ : U₁ ⟶ U₀} {a₂ : U₂ ⟶ U₁} {b₁ : W₁ ⟶ W₀} {b₂ : W₂ ⟶ W₁}
    {j₀ : U₀ ⟶ W₀} {j₁ : U₁ ⟶ W₁} {j₂ : U₂ ⟶ W₂}
    [IsOpenImmersion j₀] [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (q₁ : IsPullback a₁ j₁ j₀ b₁) (q₂ : IsPullback a₂ j₂ j₁ b₂)
    (q : IsPullback (a₂ ≫ a₁) j₂ j₀ (b₂ ≫ b₁)) (K : D Λ U₀),
    (B q).hom.app K =
      (pComp Λ b₂ b₁).hom.app ((J Λ j₀).obj K) ≫
      (P Λ b₂).map ((B q₁).hom.app K) ≫
      (B q₂).hom.app ((P Λ a₁).obj K) ≫
      (J Λ j₂).map ((pComp Λ a₂ a₁).inv.app K)
  /-- Cartesian pasting along successive opens. -/
  B_horizontal : ∀ {U U' V V' W W' : Scheme.{u}}
    {a : U' ⟶ U} {b : V' ⟶ V} {c : W' ⟶ W}
    {j : U ⟶ V} {j' : U' ⟶ V'} {i : V ⟶ W} {i' : V' ⟶ W'}
    [IsOpenImmersion j] [IsOpenImmersion j'] [IsOpenImmersion i] [IsOpenImmersion i']
    (q₁ : IsPullback a j' j b) (q₂ : IsPullback b i' i c)
    (q : IsPullback a (j' ≫ i') (j ≫ i) c) (K : D Λ U),
    (B q).hom.app K =
      (P Λ c).map ((jComp Λ j i).inv.app K) ≫
      (B q₂).hom.app ((J Λ j).obj K) ≫
      (J Λ i').map ((B q₁).hom.app K) ≫
      (jComp Λ j' i').hom.app ((P Λ a).obj K)
  /-- Associativity of the specified open compositors. -/
  j_assoc : ∀ {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (j : X₀ ⟶ X₁) (i : X₁ ⟶ X₂) (k : X₂ ⟶ X₃)
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k] (K : D Λ X₀),
    (J Λ k).map ((jComp Λ j i).hom.app K) ≫
      (jComp Λ (j ≫ i) k).hom.app K ≫ (jCongr Λ (Category.assoc j i k)).hom.app K =
      (jComp Λ i k).hom.app ((J Λ j).obj K) ≫ (jComp Λ j (i ≫ k)).hom.app K
  /-- Both open-compositor unit equations. -/
  j_unit : ∀ {U W : Scheme.{u}} (j : U ⟶ W) [IsOpenImmersion j] (K : D Λ U),
    ((jComp Λ (𝟙 U) j).hom.app K ≫ (jCongr Λ (Category.id_comp j)).hom.app K =
      (J Λ j).map ((jId Λ U).hom.app K)) ∧
    ((jComp Λ j (𝟙 W)).hom.app K ≫ (jCongr Λ (Category.comp_id j)).hom.app K =
      (jId Λ W).hom.app ((J Λ j).obj K))
  /-- The exact-model ambient mate equals the recorded total-left-derived ambient mate. -/
  exchange_normalized : ∀ {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    (sq : ChosenCartesianSquare j p r i) (K : D Λ W),
    (condensedAmbientExchange Λ sq).app K ≫
        (R Λ p).map ((leftDerivedUpperStarIsoMapDerivedCategory Λ j).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ i).hom.app ((R Λ r).obj K) ≫
        (derivedDirectImageOpenRestriction Λ sq.toCommSq).app K
  /-- Lambda is invertible in precisely the two geometric situations of (b). -/
  restriction_isIso : ∀ {U W Y Z : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [QuasiCompact j] [QuasiCompact i]
    (sq : CommSq j p r i), IsAdmissibleSquare j p r i → IsIso (restriction Λ units sq)
  /-- Vertical mixed pasting, with canonical direct-image compositors at both ends. -/
  gamma_vertical : ∀ {U W Y Z V T : Scheme.{u}}
    {j : U ⟶ W} {i : Y ⟶ Z} {k : V ⟶ T}
    {p₁ : U ⟶ Y} {p₂ : Y ⟶ V} {r₁ : W ⟶ Z} {r₂ : Z ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion k]
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact k]
    (q₁ : CommSq j p₁ r₁ i) (q₂ : CommSq i p₂ r₂ k)
    (q : CommSq j (p₁ ≫ p₂) (r₁ ≫ r₂) k)
    (_h₁ : IsAdmissibleSquare j p₁ r₁ i) (_h₂ : IsAdmissibleSquare i p₂ r₂ k)
    (K : D Λ U),
    (gamma Λ units q).app K =
      (J Λ k).map ((rComp Λ p₁ p₂).inv.app K) ≫
      (gamma Λ units q₂).app ((R Λ p₁).obj K) ≫
      (R Λ r₂).map ((gamma Λ units q₁).app K) ≫
      (rComp Λ r₁ r₂).hom.app ((J Λ j).obj K)
  /-- Horizontal mixed pasting, with canonical open compositors at both ends. -/
  gamma_horizontal : ∀ {U W V Y Z T : Scheme.{u}}
    {j₁ : U ⟶ W} {j₂ : W ⟶ V} {i₁ : Y ⟶ Z} {i₂ : Z ⟶ T}
    {p : U ⟶ Y} {r : W ⟶ Z} {s : V ⟶ T}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact j₁] [QuasiCompact j₂] [QuasiCompact i₁] [QuasiCompact i₂]
    (q₁ : CommSq j₁ p r i₁) (q₂ : CommSq j₂ r s i₂)
    (q : CommSq (j₁ ≫ j₂) p s (i₁ ≫ i₂))
    (_h₁ : IsAdmissibleSquare j₁ p r i₁) (_h₂ : IsAdmissibleSquare j₂ r s i₂)
    (K : D Λ U),
    (gamma Λ units q).app K =
      (jComp Λ i₁ i₂).inv.app ((R Λ p).obj K) ≫
      (J Λ i₂).map ((gamma Λ units q₁).app K) ≫
      (gamma Λ units q₂).app ((J Λ j₁).obj K) ≫
      (R Λ s).map ((jComp Λ j₁ j₂).hom.app K)
  /-- Identity vertical morphisms give identity comparisons. -/
  gamma_vertical_id : ∀ {U W : Scheme.{u}} (j : U ⟶ W)
    [IsOpenImmersion j] [QuasiCompact j] (sq : CommSq j (𝟙 U) (𝟙 W) j)
    (K : D Λ U),
    (gamma Λ units sq).app K =
      (J Λ j).map ((rId Λ U).hom.app K) ≫ (rId Λ W).inv.app ((J Λ j).obj K)
  /-- Identity horizontal opens give identity comparisons. -/
  gamma_horizontal_id : ∀ {U Y : Scheme.{u}} (p : U ⟶ Y)
    (sq : CommSq (𝟙 U) p p (𝟙 Y)) (K : D Λ U),
    (gamma Λ units sq).app K =
      (jId Λ Y).hom.app ((R Λ p).obj K) ≫ (R Λ p).map ((jId Λ U).inv.app K)
  /-- Arbitrary-base-change cube (c), on all unbounded objects and without inverting Ex. -/
  cube : ∀ {U W Y Z U' W' Y' Z' : Scheme.{u}}
    {j : U ⟶ W} {p : U ⟶ Y} {r : W ⟶ Z} {i : Y ⟶ Z}
    {j' : U' ⟶ W'} {p' : U' ⟶ Y'} {r' : W' ⟶ Z'} {i' : Y' ⟶ Z'}
    {aU : U' ⟶ U} {aW : W' ⟶ W} {aY : Y' ⟶ Y} {b : Z' ⟶ Z}
    [IsOpenImmersion j] [IsOpenImmersion i] [IsOpenImmersion j'] [IsOpenImmersion i']
    [QuasiCompact j] [QuasiCompact i] [QuasiCompact j'] [QuasiCompact i']
    (q : CommSq j p r i) (q' : CommSq j' p' r' i')
    (_hQ : IsAdmissibleSquare j p r i)
    (qj : IsPullback aU j' j aW) (qi : IsPullback aY i' i b)
    (qr : IsPullback aW r' r b) (qp : IsPullback aU p' p aY) (K : D Λ U),
    (P Λ b).map ((gamma Λ units q).app K) ≫
      (derivedDirectImageOpenRestriction Λ qr.toCommSq).app ((J Λ j).obj K) ≫
      (R Λ r').map ((B qj).hom.app K) =
    (B qi).hom.app ((R Λ p).obj K) ≫
      (J Λ i').map ((derivedDirectImageOpenRestriction Λ qp.toCommSq).app K) ≫
      (gamma Λ units q').app ((P Λ aU).obj K)

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

/-- Open exchange, mixed proper/open pasting and arbitrary-base-change cube coherence.
Source: latest blueprint sk-thm-sf-comp-composition.proof.md, Canonicity and associativity
and Base change; Stacks Tags 09AH, 0F7B--0F7F
(blueprint: lem-zl-condensed-open-proper-pasting).

Proof: `condensedOpenProperOpenLaws` gives the open package (units, normalized open exchange
`B`, the open compositor laws and the ambient exchange normalization: blueprint steps 1-3,
new-zl-condensed-open-proper-open-laws). For that package `condensedOpenProperMateLaws`
gives restriction invertibility, the mixed `gamma` pasting and identity laws and the
base-change cube (blueprint steps 4-10, new-zl-condensed-open-proper-mate-laws). The
fields of the two packages are exactly the fields of `Pasting`.
-/
theorem condensedOpenProperPasting (_hΛ : IsAdmissibleCoefficient Λ) :
    Nonempty (Pasting Λ) := by
  let openData : OpenLaws Λ := Classical.choice (condensedOpenProperOpenLaws Λ _hΛ)
  let mateData : MateLaws Λ openData :=
    Classical.choice (condensedOpenProperMateLaws Λ _hΛ openData)
  refine ⟨{ units := openData.units
            B := openData.B
            B_normalized := openData.B_normalized
            B_id := openData.B_id
            B_open_id := openData.B_open_id
            B_vertical := openData.B_vertical
            B_horizontal := openData.B_horizontal
            j_assoc := openData.j_assoc
            j_unit := openData.j_unit
            exchange_normalized := openData.exchange_normalized
            restriction_isIso := mateData.restriction_isIso
            gamma_vertical := mateData.gamma_vertical
            gamma_horizontal := mateData.gamma_horizontal
            gamma_vertical_id := mateData.gamma_vertical_id
            gamma_horizontal_id := mateData.gamma_horizontal_id
            cube := mateData.cube }⟩

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
