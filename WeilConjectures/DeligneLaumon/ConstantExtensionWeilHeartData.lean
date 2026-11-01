/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.AdicHeartIntrinsicFibres
public import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Data for constant extension and the constructible Weil hearts

Source: Deligne, Weil II, (1.1.7)--(1.1.10), pp. 150--152; blueprint
main-20261015, thm-zl-real-mixed-by-curves, proof paragraphs 1 and 5
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)

/-- The fixed subfield k_m has q^m elements and the same algebraic closure k.
Source: Deligne, Weil II, p. 152, change of finite base field
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the unique-subfield theorem gives cardinality q^m, which is nonzero,
so the subfield is finite. The closure k is algebraically closed and algebraic
also over this intermediate finite field, hence is its algebraic closure. -/
theorem constantExtensionField_properties :
    Finite (D.extensionSubfield m hm) ∧
      Nat.card (D.extensionSubfield m hm) = D.q ^ m ∧
      IsAlgClosure (D.extensionSubfield m hm) D.k := by
  have hc : Nat.card (D.extensionSubfield m hm) = D.q ^ m :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.1
  have hf : Finite (D.extensionSubfield m hm) := Nat.finite_of_card_ne_zero
    (hc ▸ pow_ne_zero m (D.cardinality_eq ▸ pow_ne_zero D.a D.prime.ne_zero))
  let := (D.extensionEmbedding m hm).toAlgebra
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  let : IsScalarTower D.k₀ (D.extensionSubfield m hm) D.k :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  exact ⟨hf, hc, ⟨IsAlgClosure.isAlgClosed D.k₀,
    Algebra.IsAlgebraic.tower_top (K := D.k₀) (D.extensionSubfield m hm)⟩⟩

/-- The new finite base remains the actual subfield of the fixed closure.
Source: Deligne, Weil II, p. 152
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionDatum : FiniteFieldDatum.{u} where
  p := D.p
  a := D.a * m
  q := D.q ^ m
  prime := D.prime
  exponent_pos := le_trans hm (Nat.le_mul_of_pos_left m D.exponent_pos)
  cardinality_eq := D.cardinality_eq ▸ (pow_mul D.p D.a m).symm
  k₀ := D.extensionSubfield m hm
  finite_base := (constantExtensionField_properties D m hm).1
  card_base := (constantExtensionField_properties D m hm).2.1
  k := D.k
  isAlgClosure := (constantExtensionField_properties D m hm).2.2

variable (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

/-- X_(0,m) as a k_m-scheme, the actual finite constant base change.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionModel : Over (Spec (.of (D.extensionSubfield m hm))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀

/-- The same scheme regarded over k_0, before finite pushforward.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionOriginalModel : Over (Spec (.of D.k₀)) :=
  Over.mk ((constantExtensionModel D m hm X₀).hom ≫
    Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))

set_option linter.unusedSectionVars false in
/-- The actual projection g_m, as a morphism over the original base field.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionProjection : constantExtensionOriginalModel D m hm X₀ ⟶ X₀ :=
  Over.homMk (pullback.fst X₀.hom
    (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))) pullback.condition

/-- Compatibility needed for the canonical sheet inclusion into the k_0-geometric fibre.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the inclusion k_m into k composed with extensionEmbedding is algebraMap.
Apply Spec and the defining pullback projection equation. -/
theorem constantExtensionSheet_compatible :
    pullback.fst (constantExtensionModel D m hm X₀).hom
        (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
        (constantExtensionOriginalModel D m hm X₀).hom =
      ((constantExtensionDatum D m hm).geometricFiber
        (constantExtensionModel D m hm X₀)).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  change pullback.fst _ _ ≫
      ((constantExtensionModel D m hm X₀).hom ≫
        Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) =
    pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))
  rw [← Category.assoc, pullback.condition, Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]

/-- The distinguished sheet for the given inclusion k_m into k, constructed by a lift.
Source: blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionSheet :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ⟶
        (D.geometricFiber (constantExtensionOriginalModel D m hm X₀)).left :=
  pullback.lift
    (pullback.fst (constantExtensionModel D m hm X₀).hom
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)))
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).hom
    (constantExtensionSheet_compatible D m hm X₀)

/-- The distinguished sheet maps isomorphically onto the original geometric fibre.
Source: blueprint parts (a)--(b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: associativity of base change identifies the composite with
(X_0 times_{k_0} k_m) times_{k_m} k to X_0 times_{k_0} k.
Its two projections are the canonical ones; the pullback universal property
constructs its inverse and proves both inverse identities. -/
theorem constantExtensionFiberMap_isIso :
    IsIso (constantExtensionSheet D m hm X₀ ≫
      zlFiberMap D (constantExtensionProjection D m hm X₀)) := by
  have hcomp : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
      algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have hs : Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype) ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)) =
        Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let e := pullbackLeftPullbackSndIso X₀.hom
      (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))
      (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≪≫
    pullback.congrHom rfl hs
  have he : constantExtensionSheet D m hm X₀ ≫
      zlFiberMap D (constantExtensionProjection D m hm X₀) = e.hom := by
    apply pullback.hom_ext
    · simp [e, constantExtensionSheet, zlFiberMap, constantExtensionProjection,
        Over.pullback, pullback.congrHom]
      rfl
    · simp [e, constantExtensionSheet, zlFiberMap, Over.pullback, pullback.congrHom]
      rfl
  rw [he]
  infer_instance

/-- The canonical associativity identification; no geometric scheme is replaced silently.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionFiberIso :
    ((constantExtensionDatum D m hm).geometricFiber
      (constantExtensionModel D m hm X₀)).left ≅ (D.geometricFiber X₀).left :=
  letI := constantExtensionFiberMap_isIso D m hm X₀
  asIso (constantExtensionSheet D m hm X₀ ≫
    zlFiberMap D (constantExtensionProjection D m hm X₀))

private theorem frobeniusPower_projections
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (n : ℕ) :
    let := Fintype.ofFinite D.k₀
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.fst Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ∧
    localPositivePower (D.geometricFrobenius Y₀).hom n ≫
        pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
      pullback.snd Y₀.hom (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) ≫
        Spec.map (CommRingCat.ofHom
          (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ (n + 1)).toRingHom)
        := by
  let := Fintype.ofFinite D.k₀
  have h := D.galoisMap_projections Y₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k)
  change (D.geometricFrobenius Y₀).hom ≫ _ = _ ∧
    (D.geometricFrobenius Y₀).hom ≫ _ = _ ≫
      Spec.map (CommRingCat.ofHom
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingHom) at h
  induction n with
  | zero => simpa only [localPositivePower, Nat.zero_add, pow_one] using h
  | succ n ih =>
    constructor
    · rw [localPositivePower, Category.assoc, h.1]
      exact ih.1
    · rw [localPositivePower, Category.assoc, h.2, ← Category.assoc, ih.2,
        Category.assoc, ← Spec.map_comp]
      congr 2

private theorem extensionFrobenius_power :
    let := Fintype.ofFinite D.k₀
    let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
      (constantExtensionDatum D m hm).algebra_closure
    let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
      (constantExtensionDatum D m hm).isAlgClosure
    let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k).toRingHom =
      (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ m).toRingHom := by
  let := Fintype.ofFinite D.k₀
  let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).algebra_closure
  let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).isAlgClosure
  let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
  have hc : Fintype.card (constantExtensionDatum D m hm).k₀ =
      Fintype.card D.k₀ ^ m := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, D.card_base]
    exact (constantExtensionField_properties D m hm).2.1
  ext x
  rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
    FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, inv_pow]
  change (FiniteField.frobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k).symm x =
    (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ m).symm x
  apply (FiniteField.frobeniusAlgEquivOfAlgebraic
    (constantExtensionDatum D m hm).k₀ D.k).injective
  rw [AlgEquiv.apply_symm_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply, hc]
  have h := (FiniteField.frobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ m).apply_symm_apply x
  simpa only [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] using h.symm

/-- The q^m-Frobenius returns to the distinguished sheet.
Source: Deligne, Weil II (1.1.7)--(1.1.10), blueprint part (b)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the geometric q^m automorphism is gamma^m on the same closure.
The latter fixes k_m. Comparing both projections of the defining fibre products
proves the sheet-return identity. -/
theorem constantExtensionSheet_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫ constantExtensionSheet D m hm X₀ =
      constantExtensionSheet D m hm X₀ ≫
        localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom (m - 1) := by
  let := Fintype.ofFinite D.k₀
  let : Algebra (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).algebra_closure
  let : IsAlgClosure (constantExtensionDatum D m hm).k₀ D.k :=
    (constantExtensionDatum D m hm).isAlgClosure
  let := Fintype.ofFinite (constantExtensionDatum D m hm).k₀
  have hn := (constantExtensionDatum D m hm).galoisMap_projections
    (constantExtensionModel D m hm X₀).hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic
      (constantExtensionDatum D m hm).k₀ D.k)
  have ho := frobeniusPower_projections D
    (constantExtensionOriginalModel D m hm X₀) (m - 1)
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have he := extensionFrobenius_power D m hm
  change ((constantExtensionDatum D m hm).geometricFrobenius
      (constantExtensionModel D m hm X₀)).hom ≫ _ = _
  have hn' :
      ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
          pullback.fst (constantExtensionModel D m hm X₀).hom
            (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) =
        pullback.fst (constantExtensionModel D m hm X₀).hom
          (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) := by
    exact hn.1
  have hn'' :
      ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
          ((constantExtensionDatum D m hm).geometricFiber
            (constantExtensionModel D m hm X₀)).hom =
        ((constantExtensionDatum D m hm).geometricFiber
          (constantExtensionModel D m hm X₀)).hom ≫
          Spec.map (CommRingCat.ofHom
            (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k ^ m).toRingHom) := by
    rw [← he]
    exact hn.2
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [ho.1]
    simp only [constantExtensionSheet, pullback.lift_fst]
    exact hn'
  · simp only [Category.assoc]
    rw [ho.2, hm']
    simp only [constantExtensionSheet, pullback.lift_snd, pullback.lift_snd_assoc]
    exact hn''


variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The residue degree uses the actual field map induced by g_m, not its total degree.
Source: blueprint part (a), f=[kappa(z):kappa(x)]
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionResidueDegree
    (z : (constantExtensionModel D m hm X₀).left) : ℕ :=
  letI : Algebra
      (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
      ((constantExtensionModel D m hm X₀).left.residueField z) :=
    ((constantExtensionProjection D m hm X₀).left.residueFieldMap z).hom.toAlgebra
  Module.finrank (X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z))
    ((constantExtensionModel D m hm X₀).left.residueField z)

set_option linter.unusedSectionVars false in
/-- A closed point has closed image under the finite projection.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: g_m is finite, hence closed. The image of the one-point closed subset is closed. -/
theorem constantExtensionClosedImage_mem
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    (constantExtensionProjection D m hm X₀).left z.val ∈ closedPoints X₀.left := by
  let := (D.extensionEmbedding m hm).toAlgebra
  have := (constantExtensionField_properties D m hm).1
  have : IsFinite (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) :=
    (IsFinite.SpecMap_iff _).mpr (show Module.Finite D.k₀ (D.extensionSubfield m hm) from
      inferInstance)
  have : IsFinite (constantExtensionProjection D m hm X₀).left :=
    show IsFinite (pullback.fst X₀.hom _) from inferInstance
  have hc := (constantExtensionProjection D m hm X₀).left.isClosedMap _ z.property
  change IsClosed {(constantExtensionProjection D m hm X₀).left z.val}
  simpa only [Set.image_singleton] using hc

/-- The closed image point with its inherited closedness proof.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence). -/
def constantExtensionClosedImage
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    {x : X₀.left // x ∈ closedPoints X₀.left} :=
  ⟨(constantExtensionProjection D m hm X₀).left z.val,
    constantExtensionClosedImage_mem D m hm X₀ z⟩

/-- The canonical fibre isomorphism intertwines the new Frobenius with the mth power.
Source: blueprint part (a)
(blueprint: lem-zl-constant-extension-weil-heart-equivalence).
Proof: the fibre isomorphism is the associativity map of base change, and geometric
Frobenius acts only on the closure factor. Over k_m its coefficient action is gamma^m.
Comparing the two projections gives the equality, also when the model is empty. -/
theorem constantExtensionFiber_return :
    ((constantExtensionDatum D m hm).geometricFrobenius
        (constantExtensionModel D m hm X₀)).hom ≫
        (constantExtensionFiberIso D m hm X₀).hom =
      (constantExtensionFiberIso D m hm X₀).hom ≫
        localPositivePower (D.geometricFrobenius X₀).hom (m - 1) := by
  have hn (n : ℕ) :
      localPositivePower
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom n ≫
          zlFiberMap D (constantExtensionProjection D m hm X₀) =
        zlFiberMap D (constantExtensionProjection D m hm X₀) ≫
          localPositivePower (D.geometricFrobenius X₀).hom n := by
    induction n with
    | zero => exact zlFrobenius_naturality D (constantExtensionProjection D m hm X₀)
    | succ n ih =>
      rw [localPositivePower, Category.assoc, zlFrobenius_naturality,
        ← Category.assoc, ih, Category.assoc]
      rfl
  change _ ≫ (constantExtensionSheet D m hm X₀ ≫
      zlFiberMap D (constantExtensionProjection D m hm X₀)) =
    (constantExtensionSheet D m hm X₀ ≫
      zlFiberMap D (constantExtensionProjection D m hm X₀)) ≫ _
  rw [← Category.assoc, constantExtensionSheet_return, Category.assoc, hn,
    Category.assoc]

end WeilConjectures
