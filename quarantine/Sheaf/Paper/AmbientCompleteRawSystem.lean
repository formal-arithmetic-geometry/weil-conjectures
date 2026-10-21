/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.FiniteStagePairCategory

/-! # Canonical raw ambient scalar system

Source: literature/blueprint/slopmaster2/src/version/sketch/32_smooth_base_change.tex,
lines 1191--1228 and 1291--1338
(blueprint: def-sbc-ambient-complete-raw-scalar-system).

## Main definitions

* `pbcAmbientCompleteStage`: the raw rational ambient complete category.
* `pbcAmbientCompleteRawTransition`: the normalized localized tensor.
* `pbcAmbientCompleteRawSystem`: these tensors and their balanced associators.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u v
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Use the existing division-ring torsion-free instance directly for coefficient fields.
This specializes Mathlib's instance, avoiding its slower flatness search path.
Source: sketch32, coefficient fields throughout lines 1191--1438;
Mathlib `DivisionSemiring.to_moduleIsTorsionFree`
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
instance (priority := 3000) pbcCompleteCoefficientTorsionFree
    (l : ℕ) [Fact l.Prime] (L : Type v) [Field L] [Algebra (Padic l) L] :
    Module.IsTorsionFree (Padic l) L := DivisionSemiring.to_moduleIsTorsionFree

/-- The ambient complete coefficient stage before idempotent completion.
Source: sketch32, lines 1192--1207 (blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
abbrev pbcAmbientCompleteStage (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (W : Scheme.{u}) (E : Padic.FiniteCoefficientFields l Ω) : Type (u + 2) :=
  WeilConjectures.PbcRationalComplete l (pbcFiniteField.{u} l Ω E) W

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [IsNoetherian W]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

variable {E F G : Padic.FiniteCoefficientFields l Ω}

/-- Finite coefficient tensor preserves intrinsic completeness without constructible bounds.
Source: sketch32, finite-stage pair categories, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: finite freeness makes tensor commute with the Koszul completion limit.
The source and target uniformizer powers are cofinal. Thus tensor carries the
invertible source completion unit to the target completion unit. -/
theorem pbcAmbientCompleteTensor_preserves (h : E ≤ F)
    (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
    WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω F) W
      ((pbcAmbientScalarExtension l Ω W h).obj K.obj) := by
  sorry

/-- Restrict the actual finite-projection-normalized tensor to complete objects.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralTransition (h : E ≤ F) :
    WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W ⥤
      WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω F) W :=
  ObjectProperty.lift (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω F) W)
    (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W) ⋙
      pbcAmbientScalarExtension l Ω W h)
    (pbcAmbientCompleteTensor_preserves l Ω W h)

/-- Localization of the complete integral stage; no idempotents are adjoined.
Source: sketch32, lines 1192--1207
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
abbrev pbcAmbientCompleteLocalization (E : Padic.FiniteCoefficientFields l Ω) :=
  ScalarLocalization.localization (PbcIntegralRing l (pbcFiniteField.{u} l Ω E))
    (WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W)
    (pbcStageUniformizer.{u} l Ω E)

/-- The rational tensor functor is uniquely determined on integral objects and arrows.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: the coefficient inclusion sends a source uniformizer to a unit times a
positive power of the target uniformizer. Send a fraction to the tensor image
with its denominator mapped by that inclusion. Bilinearity gives the tensor-Hom
formula, functoriality descends, and fractions generate every Hom, proving uniqueness. -/
theorem pbcAmbientCompleteRaw_exists (h : E ≤ F) :
    ∃! T : pbcAmbientCompleteStage l Ω W E ⥤ pbcAmbientCompleteStage l Ω W F,
      pbcAmbientCompleteLocalization l Ω W E ⋙ T =
        pbcAmbientCompleteIntegralTransition l Ω W h ⋙
          pbcAmbientCompleteLocalization l Ω W F := by
  sorry

/-- Canonical rational tensor, normalized to the literal identity at equal fields.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteRawTransition (h : E ≤ F) :
    pbcAmbientCompleteStage l Ω W E ⥤ pbcAmbientCompleteStage l Ω W F := by
  classical
  exact if e : E = F then e ▸ 𝟭 _ else
    (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose

/-- The complete integral tensor unit is the restriction of the canonical derived unit.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: the ambient unit is normalized on tensor sections. Completeness is a full
subcategory, so lift its components and inverses. Faithfulness proves uniqueness. -/
theorem pbcAmbientCompleteIntegralUnit_exists (E : Padic.FiniteCoefficientFields l Ω) :
    ∃! e : pbcAmbientCompleteIntegralTransition l Ω W (le_refl E) ≅ 𝟭 _,
      HEq (Functor.whiskerRight e.hom
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W)))
        (Functor.whiskerLeft
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W))
          (pbcAmbientScalarUnit l Ω W E).hom) := by
  sorry

/-- The section-normalized complete tensor unit.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralUnit (E : Padic.FiniteCoefficientFields l Ω) :=
  (pbcAmbientCompleteIntegralUnit_exists l Ω W E).exists.choose

/-- Integral normalization of raw rational extension, including the equal-field branch.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: at equal fields use the inverse tensor unit. At distinct fields use the
unique localization factorization. These formulas fix every component. -/
theorem pbcAmbientCompleteIntegralComparison_exists (h : E ≤ F) :
    ∃! c : pbcAmbientCompleteLocalization l Ω W E ⋙
        pbcAmbientCompleteRawTransition l Ω W h ≅
      pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteLocalization l Ω W F,
      (E = F → HEq c
        ((Functor.rightUnitor (pbcAmbientCompleteLocalization l Ω W E)) ≪≫
          (Functor.leftUnitor (pbcAmbientCompleteLocalization l Ω W E)).symm ≪≫
          Functor.isoWhiskerRight (pbcAmbientCompleteIntegralUnit l Ω W E).symm
            (pbcAmbientCompleteLocalization l Ω W E))) ∧
      (E ≠ F → HEq c
        (eqToIso (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec)) := by
  sorry

/-- The uniquely normalized integral/rational tensor comparison.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralComparison (h : E ≤ F) :=
  (pbcAmbientCompleteIntegralComparison_exists l Ω W h).exists.choose

/-- Restriction of the specified balanced ambient associator to complete objects.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: both complete subcategories are full. Lift the balanced tensor comparison
and its inverse. Faithfulness proves the naturality, inverse equations and uniqueness. -/
theorem pbcAmbientCompleteIntegralAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! a : pbcAmbientCompleteIntegralTransition l Ω W h ⋙
        pbcAmbientCompleteIntegralTransition l Ω W k ≅
      pbcAmbientCompleteIntegralTransition l Ω W (h.trans k),
      HEq (Functor.whiskerRight a.hom
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω G) W)))
        (Functor.whiskerLeft
          (ObjectProperty.ι (WeilConjectures.IsPbcComplete l (pbcFiniteField.{u} l Ω E) W))
          (pbcAmbientScalarAssociator l Ω W h k).hom) := by
  sorry

/-- Complete integral tensor balancing, with its ambient normalization.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralAssociator (h : E ≤ F) (k : F ≤ G) :=
  (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose

/-- Rational associators are fixed by the integral balanced components.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: localize the integral associator and conjugate by the integral/rational
comparisons. Naturality holds on integral arrows and hence on their fractions.
Every raw object is integral, so the formula also gives uniqueness. -/
theorem pbcAmbientCompleteRawAssociator_exists (h : E ≤ F) (k : F ≤ G) :
    ∃! a : pbcAmbientCompleteRawTransition l Ω W h ⋙
        pbcAmbientCompleteRawTransition l Ω W k ≅
      pbcAmbientCompleteRawTransition l Ω W (h.trans k),
      ∀ K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W,
        a.hom.app ((pbcAmbientCompleteLocalization l Ω W E).obj K) =
          (pbcAmbientCompleteRawTransition l Ω W k).map
              ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K) ≫
            (pbcAmbientCompleteIntegralComparison l Ω W k).hom.app
              ((pbcAmbientCompleteIntegralTransition l Ω W h).obj K) ≫
            (pbcAmbientCompleteLocalization l Ω W G).map
              ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) ≫
            (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).inv.app K := by
  sorry

/-- The canonical rational tensor associator.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteRawAssociator (h : E ≤ F) (k : F ≤ G) :=
  (pbcAmbientCompleteRawAssociator_exists l Ω W h k).exists.choose

/-- The canonical raw system has additive transitions, normalized units and tensor pentagon.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system).
Proof: finite tensor and localization preserve addition. The equal-field branch
is identity. The section-normalized tensor unit satisfies the unit equations
with balancing. The two tensor-balancing composites agree on pure tensors.
Their derived, full-subcategory and localized images give the displayed pentagon. -/
theorem pbcAmbientCompleteRaw_laws (h : E ≤ F) (k : F ≤ G)
    {H : Padic.FiniteCoefficientFields l Ω} (j : G ≤ H) :
    (pbcAmbientCompleteRawTransition l Ω W h).Additive ∧
    pbcAmbientCompleteRawTransition l Ω W (le_refl E) = 𝟭 _ ∧
    HEq (pbcAmbientCompleteRawAssociator l Ω W (le_refl E) h)
      (Functor.leftUnitor (pbcAmbientCompleteRawTransition l Ω W h)) ∧
    HEq (pbcAmbientCompleteRawAssociator l Ω W h (le_refl F))
      (Functor.rightUnitor (pbcAmbientCompleteRawTransition l Ω W h)) ∧
    (∀ K : pbcAmbientCompleteStage l Ω W E,
      (pbcAmbientCompleteRawTransition l Ω W j).map
          ((pbcAmbientCompleteRawAssociator l Ω W h k).hom.app K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W (h.trans k) j).hom.app K =
      (pbcAmbientCompleteRawAssociator l Ω W k j).hom.app
          ((pbcAmbientCompleteRawTransition l Ω W h).obj K) ≫
        (pbcAmbientCompleteRawAssociator l Ω W h (k.trans j)).hom.app K) := by
  sorry

/-- The actual ambient raw scalar-extension system, rather than an arbitrary diagram.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
def pbcAmbientCompleteRawSystem :
    StageSystem (fun E : Padic.FiniteCoefficientFields l Ω ↦ pbcAmbientCompleteStage l Ω W E)
    where
  T h := pbcAmbientCompleteRawTransition l Ω W h
  assoc h k := pbcAmbientCompleteRawAssociator l Ω W h k
  cocycle h k j K := (pbcAmbientCompleteRaw_laws l Ω W h k j).2.2.2.2 K

/-- Additivity of the uniquely localized ambient tensor.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
instance pbcAmbientCompleteRaw_additive (h : E ≤ F) :
    (pbcAmbientCompleteRawTransition l Ω W h).Additive :=
  (pbcAmbientCompleteRaw_laws l Ω W h (le_refl F) (le_refl F)).1


end AlgebraicGeometry.Scheme
