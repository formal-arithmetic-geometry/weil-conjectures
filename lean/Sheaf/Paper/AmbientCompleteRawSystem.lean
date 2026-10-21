/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.FiniteStagePairCategory
import Sheaf.Paper.PbcScalarExtension
import Mathlib.RingTheory.Localization.BaseChange

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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Integral naturality extends to all localized arrows by clearing one denominator.
Source: Mathlib `IsLocalizedModule.surj` and `IsLocalization.map_units`
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
private lemma extend_naturality
    {R : Type*} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (p : R) {D : Type*} [Category D]
    (F G : ScalarLocalization R C p ⥤ D)
    (e : ScalarLocalization.localization R C p ⋙ F ⟶ ScalarLocalization.localization R C p ⋙ G)
    {X Y : ScalarLocalization R C p} (f : X ⟶ Y) :
    F.map f ≫ e.app Y.obj = e.app X.obj ≫ G.map f := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  let Q := ScalarLocalization.localization R C p
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (X ⟶ Y) 1) f
  let d : X ⟶ X := (s : R) • 𝟙 X
  have hd : Q.map d ≫ f = Q.map g := by
    change (s : R) • f = (1 : Localization.Away p) ⊗ₜ[R] g at hs
    change ScalarLocalization.composition R C p X X Y f (1 ⊗ₜ[R] d) = 1 ⊗ₜ[R] g
    rw [← hs]
    clear hs
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a f => simp [d, ScalarLocalization.composition_tmul, TensorProduct.tmul_smul]
    | add f g hf hg => simp [hf, hg]
  have hi : IsIso (Q.map d) := by
    have hh : Q.map d = (algebraMap R (Localization.Away p) s) • 𝟙 (Q.obj X) := by
      change (1 : Localization.Away p) ⊗ₜ[R] ((s : R) • 𝟙 X) = _
      rw [← TensorProduct.smul_tmul]
      change ((s : R) • (1 : Localization.Away p)) ⊗ₜ[R] 𝟙 X =
        (algebraMap R (Localization.Away p) s) • ((1 : Localization.Away p) ⊗ₜ[R] 𝟙 X)
      simp [Algebra.smul_def, TensorProduct.smul_tmul']
    rw [hh]
    obtain ⟨z, hz⟩ := IsLocalization.map_units (Localization.Away p) s
    rw [← hz]
    exact ⟨⟨(↑(z⁻¹) : Localization.Away p) • 𝟙 (Q.obj X), by
      simp [Linear.comp_smul, smul_smul], by
      simp [Linear.comp_smul, smul_smul]⟩⟩
  apply (cancel_epi (F.map (Q.map d))).1
  calc
    F.map (Q.map d) ≫ (F.map f ≫ e.app Y) =
        F.map (Q.map g) ≫ e.app Y := by
      rw [← Category.assoc, ← F.map_comp, hd]
    _ = e.app X ≫ G.map (Q.map g) := e.naturality g
    _ = e.app X ≫ (G.map (Q.map d) ≫ G.map f) := by
      rw [← G.map_comp, hd]
    _ = F.map (Q.map d) ≫ (e.app X ≫ G.map f) := by
      have he := e.naturality d
      change F.map (Q.map d) ≫ e.app X = e.app X ≫ G.map (Q.map d) at he
      rw [← Category.assoc, ← he, Category.assoc]

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

set_option linter.unusedSectionVars false in
/-- The specified finite comparison is the constants-to-functions comparison.
Source: `pbcLevelConstantComparison_exists`, blueprint order 1250
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
private lemma completeLevelComparison_hom (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    (pbcLevelConstantComparison W d n).hom =
      AdicCoefficients.constantComparison W (A ⧸ d.ideal ^ (n + 1)) := by
  let := d.quotientFinite
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((pbcAdicRings W d).obj (Opposite.op n)).property
  change toSheafify _ _ ≫ (pbcLevelConstantComparison W d n).hom.hom =
    toSheafify _ _ ≫ sheafifyMap _ _
  rw [← toSheafify_naturality]
  ext U b
  exact (pbcLevelConstantComparison_exists W d n).exists.choose_spec U b

set_option linter.unusedSectionVars false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two completed scalar maps agree on every finite quotient projection.
Source: blueprint order 1307, the normalized finite coefficient inclusions
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
private lemma completeScalarMap_eq
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
    {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCompletedScalarMap l Ω W h =
      pbcScalarCoefficientMap l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) W := by
  apply (pbcCompletedScalarMap_exists l Ω W h).unique
  · exact (pbcCompletedScalarMap_exists l Ω W h).exists.choose_spec
  · intro n
    dsimp only [pbcScalarCoefficientMap, pbcStageDatum]
    rw [(pbcScalarCoefficientMap_exists l (pbcFiniteField.{u} l Ω E)
      (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω h) W).exists.choose_spec]
    congr 1
    dsimp only [pbcFiniteScalarMap]
    apply (cancel_epi (pbcLevelConstantComparison W (pbcStageDatum l Ω E) n).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [completeLevelComparison_hom W, completeLevelComparison_hom W]
    change (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _ =
      (presheafToSheaf _ CommRingCat).map _ ≫
        (presheafToSheaf _ CommRingCat).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

variable (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (W : Scheme.{u})
  [IsNoetherian W]
  [hDim : Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
  [hInv : Fact (∀ x : W, IsUnit (l : W.presheaf.stalk x))]

variable {E F G : Padic.FiniteCoefficientFields l Ω}

set_option linter.unusedSectionVars false in
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
  change PbcIsIntrinsicallyComplete W (pbcStageDatum l Ω F)
    ((pbcDerivedExtend (pbcCompletedScalarMap l Ω W h)).obj K.obj)
  rw [completeScalarMap_eq l Ω W h]
  exact pbcScalarPreservesComplete l (pbcFiniteField l Ω E) (pbcFiniteField l Ω F)
    (pbcFiniteFieldInclusion l Ω h) W K

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
  let e : pbcAmbientCompleteIntegralTransition l Ω W (le_refl E) ≅ 𝟭 _ := by
    unfold pbcAmbientCompleteIntegralTransition
    exact NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _ ((pbcAmbientScalarUnit l Ω W E).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarUnit l Ω W E).hom.naturality f.hom)
  unfold pbcAmbientCompleteIntegralTransition at *
  refine ⟨e, ?_, ?_⟩
  · rfl
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply ObjectProperty.hom_ext _
    exact congrArg (fun η ↦ η.app K) (eq_of_heq he')

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
  classical
  by_cases hEF : E = F
  · subst F
    have hs : pbcAmbientCompleteRawTransition l Ω W h = 𝟭 _ := by
      simp [pbcAmbientCompleteRawTransition]
    rw [hs]
    let e := (Functor.rightUnitor (pbcAmbientCompleteLocalization l Ω W E)) ≪≫
      (Functor.leftUnitor (pbcAmbientCompleteLocalization l Ω W E)).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralUnit l Ω W E).symm
        (pbcAmbientCompleteLocalization l Ω W E)
    refine ⟨e, ⟨fun _ ↦ HEq.rfl, fun hne ↦ (hne rfl).elim⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.1 rfl)
  · have hs : pbcAmbientCompleteRawTransition l Ω W h =
        (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose := by
      simp [pbcAmbientCompleteRawTransition, hEF]
    rw [hs]
    refine ⟨eqToIso (pbcAmbientCompleteRaw_exists l Ω W h).exists.choose_spec,
      ⟨fun heq ↦ (hEF heq).elim, fun _ ↦ HEq.rfl⟩, ?_⟩
    intro e' he'
    exact eq_of_heq (he'.2 hEF)

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
  let a : pbcAmbientCompleteIntegralTransition l Ω W h ⋙
      pbcAmbientCompleteIntegralTransition l Ω W k ≅
      pbcAmbientCompleteIntegralTransition l Ω W (h.trans k) := by
    unfold pbcAmbientCompleteIntegralTransition
    exact NatIso.ofComponents
      (fun K ↦ ObjectProperty.isoMk _
        ((pbcAmbientScalarAssociator l Ω W h k).app K.obj))
      (fun f ↦ by
        apply ObjectProperty.hom_ext
        exact (pbcAmbientScalarAssociator l Ω W h k).hom.naturality f.hom)
  unfold pbcAmbientCompleteIntegralTransition at *
  refine ⟨a, ?_, ?_⟩
  · rfl
  · intro a' ha'
    apply Iso.ext
    apply NatTrans.ext
    funext K
    apply ObjectProperty.hom_ext _
    exact congrArg (fun η ↦ η.app K) (eq_of_heq ha')

/-- Complete integral tensor balancing, with its ambient normalization.
Source: sketch32, lines 1291--1311
(blueprint: def-sbc-ambient-complete-raw-scalar-system). -/
@[irreducible] def pbcAmbientCompleteIntegralAssociator (h : E ≤ F) (k : F ≤ G) :=
  (pbcAmbientCompleteIntegralAssociator_exists l Ω W h k).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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
  let Q := pbcAmbientCompleteLocalization l Ω W E
  let R := pbcAmbientCompleteLocalization l Ω W F
  let S := pbcAmbientCompleteLocalization l Ω W G
  let A := pbcAmbientCompleteRawTransition l Ω W h
  let B := pbcAmbientCompleteRawTransition l Ω W k
  let C := pbcAmbientCompleteRawTransition l Ω W (h.trans k)
  let I := pbcAmbientCompleteIntegralTransition l Ω W h
  let J := pbcAmbientCompleteIntegralTransition l Ω W k
  let e : Q ⋙ (A ⋙ B) ≅ Q ⋙ C :=
    (Functor.associator Q A B).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralComparison l Ω W h) B ≪≫
      Functor.associator I R B ≪≫
      Functor.isoWhiskerLeft I (pbcAmbientCompleteIntegralComparison l Ω W k) ≪≫
      (Functor.associator I J S).symm ≪≫
      Functor.isoWhiskerRight (pbcAmbientCompleteIntegralAssociator l Ω W h k) S ≪≫
      (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).symm
  let a : A ⋙ B ≅ C := NatIso.ofComponents (fun K ↦ e.app K.obj)
    (fun f ↦ extend_naturality
      (pbcStageUniformizer l Ω E) (A ⋙ B) C e.hom f)
  have ha (K : WeilConjectures.PbcComplete l (pbcFiniteField.{u} l Ω E) W) :
      a.hom.app (Q.obj K) =
        B.map ((pbcAmbientCompleteIntegralComparison l Ω W h).hom.app K) ≫
          (pbcAmbientCompleteIntegralComparison l Ω W k).hom.app (I.obj K) ≫
          S.map ((pbcAmbientCompleteIntegralAssociator l Ω W h k).hom.app K) ≫
          (pbcAmbientCompleteIntegralComparison l Ω W (h.trans k)).inv.app K := by
    dsimp [a, e, Q, R, S, I, J, pbcAmbientCompleteLocalization,
      ScalarLocalization.localization]
    simp only [Category.id_comp]
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  exact (ha' K.obj).trans (ha K.obj).symm

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
