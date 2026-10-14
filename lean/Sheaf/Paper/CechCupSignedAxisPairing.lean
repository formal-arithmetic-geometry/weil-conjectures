/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProductCore
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Sheaf.Paper.CupCechTotalCochainPairing

/-! # Signed total Cech pairing and its two axes

Source: Stacks Project, Tags 07MB and 0FKV.
(blueprint: lem-sc-cech-cup-signed-axis-pairing).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private def cycleClassLinear {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) :
    (K.sc n).moduleCatLeftHomologyData.K →ₗ[R] K.homology n :=
  ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cycleClassLinear_eq_zero {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    cycleClassLinear K n a = 0 ↔
      a ∈ LinearMap.range (K.sc n).moduleCatToCycles := by
  have h := (K.sc n).moduleCatCyclesIso_inv_π
  have ha := congrArg (fun f ↦ f a) h
  change cycleClassLinear K n a = _ at ha
  rw [ha]
  change (K.sc n).moduleCatHomologyIso.inv (Submodule.Quotient.mk a) = 0 ↔ _
  rw [← (K.sc n).moduleCatHomologyIso.inv.hom.map_zero]
  exact ((ModuleCat.mono_iff_injective (K.sc n).moduleCatHomologyIso.inv).mp
    inferInstance).eq_iff.trans (Submodule.Quotient.mk_eq_zero _)

private lemma bilinear_homology_desc {R : Type v} [CommRing R]
    (A B C : CochainComplex (ModuleCat.{v} R) ℕ) (p q n : ℕ)
    (f : (A.sc p).moduleCatLeftHomologyData.K →ₗ[R]
      (B.sc q).moduleCatLeftHomologyData.K →ₗ[R] (C.sc n).moduleCatLeftHomologyData.K)
    (hl : ∀ a b, f ((A.sc p).moduleCatToCycles a) b ∈
      LinearMap.range (C.sc n).moduleCatToCycles)
    (hr : ∀ a b, f a ((B.sc q).moduleCatToCycles b) ∈
      LinearMap.range (C.sc n).moduleCatToCycles) :
    ∃ cup : A.homology p →ₗ[R] B.homology q →ₗ[R] C.homology n,
      ∀ a b, cup (cupCycleClass A p a) (cupCycleClass B q b) =
        cupCycleClass C n (f a b) := by
  let g := f.compr₂ (cycleClassLinear C n)
  have hgl : LinearMap.range (A.sc p).moduleCatToCycles ≤ g.ker := by
    rintro _ ⟨a, rfl⟩
    ext b
    exact (cycleClassLinear_eq_zero C n _).mpr (hl a b)
  have hgr : LinearMap.range (B.sc q).moduleCatToCycles ≤ g.flip.ker := by
    rintro _ ⟨b, rfl⟩
    ext a
    exact (cycleClassLinear_eq_zero C n _).mpr (hr a b)
  let cup := (g.liftQ₂ _ _ hgl hgr).compl₁₂
    (A.sc p).moduleCatHomologyIso.hom.hom (B.sc q).moduleCatHomologyIso.hom.hom
  refine ⟨cup, ?_⟩
  intro a b
  have hc (K : CochainComplex (ModuleCat.{v} R) ℕ) (i : ℕ)
      (z : (K.sc i).moduleCatLeftHomologyData.K) :
      (K.sc i).moduleCatHomologyIso.hom (cupCycleClass K i z) =
        (K.sc i).moduleCatLeftHomologyData.π z := by
    simp only [cupCycleClass, ← ConcreteCategory.comp_apply]
    rw [Category.assoc, ShortComplex.π_moduleCatCyclesIso_hom,
      Iso.inv_hom_id_assoc]
  dsimp only [cup, LinearMap.compl₁₂_apply, ModuleCat.Hom.hom]
  exact (congrArg₂ (fun x y ↦ g.liftQ₂ _ _ hgl hgr x y)
    (hc A p a) (hc B q b)).trans (by rfl)

private lemma cycle_d_zero {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) : K.d n (n + 1) a.val = 0 := by
  have h := a.property
  change K.d n ((ComplexShape.up ℕ).next n) a.val = 0 at h
  rw [(ComplexShape.up ℕ).next_eq' (show n + 1 = n + 1 from rfl)] at h
  exact h

private lemma toCycles_zero {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (a : (K.sc 0).X₁) :
    (K.sc 0).moduleCatToCycles a = 0 := by
  apply Subtype.ext
  change K.d ((ComplexShape.up ℕ).prev 0) 0 a = 0
  rw [K.shape _ _ (by intro h; change _ + 1 = 0 at h; omega)]
  rfl

private lemma cycle_mem_range_of_d {R : Type v} [Ring R]
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (m n : ℕ) (hn : m + 1 = n)
    (c : (K.sc n).moduleCatLeftHomologyData.K) (x : K.X m)
    (hc : K.d m n x = c.val) : c ∈ LinearMap.range (K.sc n).moduleCatToCycles := by
  have hi : (ComplexShape.up ℕ).prev n = m := (ComplexShape.up ℕ).prev_eq' hn
  refine ⟨(K.XIsoOfEq hi).inv x, Subtype.ext ?_⟩
  change K.d ((ComplexShape.up ℕ).prev n) n ((K.XIsoOfEq hi).inv x) = c.val
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_inv_comp_d]
  exact hc

private abbrev tensorTotal {R : Type v} [CommRing R]
    (A B : CochainComplex (ModuleCat.{v} R) ℕ) :=
  HomologicalComplex.mapBifunctor A B (curriedTensor (ModuleCat.{v} R))
    (ComplexShape.up ℕ)

private def tensorInsert {R : Type v} [CommRing R]
    (A B : CochainComplex (ModuleCat.{v} R) ℕ) (p q : ℕ) :
    A.X p →ₗ[R] B.X q →ₗ[R] (tensorTotal A B).X (p + q) :=
  (TensorProduct.mk R (A.X p) (B.X q)).compr₂
    (HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{v} R))
      (ComplexShape.up ℕ) p q (p + q) rfl).hom

open scoped TensorProduct in
private lemma tensorInsert_cast {R : Type v} [CommRing R]
    (A B : CochainComplex (ModuleCat.{v} R) ℕ) (p q n : ℕ) (hn : p + q = n)
    (a : A.X p) (b : B.X q) :
    (eqToHom (congrArg (fun i ↦ (tensorTotal A B).X i) hn))
        (tensorInsert A B p q a b) =
      HomologicalComplex.ιMapBifunctor A B (curriedTensor (ModuleCat.{v} R))
        (ComplexShape.up ℕ) p q n hn (a ⊗ₜ[R] b) := by
  subst n
  rfl

open scoped TensorProduct in
private lemma tensorInsert_d {R : Type v} [CommRing R]
    (A B : CochainComplex (ModuleCat.{v} R) ℕ) (p q : ℕ)
    (a : A.X p) (b : B.X q) :
    (tensorTotal A B).d (p + q) (p + q + 1) (tensorInsert A B p q a b) =
      (eqToHom (congrArg (fun n ↦ (tensorTotal A B).X n)
        (by omega : p + 1 + q = p + q + 1)))
        (tensorInsert A B (p + 1) q (A.d p (p + 1) a) b) +
      (-1 : ℤ) ^ p •
        (eqToHom (congrArg (fun n ↦ (tensorTotal A B).X n)
          (by omega : p + (q + 1) = p + q + 1)))
          (tensorInsert A B p (q + 1) a (B.d q (q + 1) b)) := by
  let T := curriedTensor (ModuleCat.{v} R)
  have h := congrArg (fun f ↦ f.hom (a ⊗ₜ[R] b))
    (show HomologicalComplex.ιMapBifunctor A B T (ComplexShape.up ℕ)
        p q (p + q) rfl ≫ (tensorTotal A B).d (p + q) (p + q + 1) = _ from
      by rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁,
        HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq A B T (ComplexShape.up ℕ)
          (by rfl) q (p + q + 1) (by dsimp; omega),
        HomologicalComplex.mapBifunctor.d₂_eq A B T (ComplexShape.up ℕ)
          p (by rfl) (p + q + 1) (by rfl)])
  simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε,
    one_smul, ModuleCat.hom_comp, ModuleCat.hom_add, ModuleCat.hom_smul,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply] at h
  change (tensorTotal A B).d (p + q) (p + q + 1)
      (HomologicalComplex.ιMapBifunctor A B T (ComplexShape.up ℕ)
        p q (p + q) rfl (a ⊗ₜ[R] b)) =
    ((A.d p (p + 1) ▷ B.X q) ≫
      HomologicalComplex.ιMapBifunctor A B T (ComplexShape.up ℕ)
        (p + 1) q (p + q + 1) (by dsimp; omega)) (a ⊗ₜ[R] b) +
    (-1 : ℤˣ) ^ p •
      ((A.X p ◁ B.d q (q + 1)) ≫
        HomologicalComplex.ιMapBifunctor A B T (ComplexShape.up ℕ)
          p (q + 1) (p + q + 1) (by rfl)) (a ⊗ₜ[R] b) at h
  simp only [ConcreteCategory.comp_apply] at h
  have hl : (A.d p (p + 1) ▷ B.X q) (a ⊗ₜ[R] b) =
      A.d p (p + 1) a ⊗ₜ[R] b :=
    TensorProduct.map_tmul (A.d p (p + 1)).hom LinearMap.id a b
  have hr : (A.X p ◁ B.d q (q + 1)) (a ⊗ₜ[R] b) =
      a ⊗ₜ[R] B.d q (q + 1) b :=
    TensorProduct.map_tmul LinearMap.id (B.d q (q + 1)).hom a b
  rw [hl, hr] at h
  rw [tensorInsert_cast _ _ _ _ _ (by omega),
    tensorInsert_cast _ _ _ _ _ (by omega)]
  simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one] at h
  convert h using 1 <;> rfl

private def tensorCochainPair {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ) :
    A.X p →ₗ[R] B.X q →ₗ[R] C.X (p + q) :=
  (tensorInsert A B p q).compr₂ (h.f (p + q)).hom

private lemma tensorCochainPair_leibniz {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ) (a : A.X p) (b : B.X q) :
    C.d (p + q) (p + q + 1) (tensorCochainPair h p q a b) =
      (eqToHom (congrArg (fun n ↦ C.X n)
        (by omega : p + 1 + q = p + q + 1)))
        (tensorCochainPair h (p + 1) q (A.d p (p + 1) a) b) +
      (-1 : ℤ) ^ p •
        (eqToHom (congrArg (fun n ↦ C.X n)
          (by omega : p + (q + 1) = p + q + 1)))
          (tensorCochainPair h p (q + 1) a (B.d q (q + 1) b)) := by
  have hc := congrArg (fun f ↦ f (tensorInsert A B p q a b))
    (h.comm (p + q) (p + q + 1))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, tensorInsert_d,
    map_add, map_zsmul] at hc
  have he (m n : ℕ) (hmn : m = n) (z : (tensorTotal A B).X m) :
      h.f n (eqToHom (congrArg (fun i ↦ (tensorTotal A B).X i) hmn) z) =
        eqToHom (congrArg (fun i ↦ C.X i) hmn) (h.f m z) := by
    subst n
    rfl
  rw [he _ _ (by omega), he _ _ (by omega)] at hc
  exact hc

private lemma tensorCochainPair_cycle {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ)
    (a : (A.sc p).moduleCatLeftHomologyData.K)
    (b : (B.sc q).moduleCatLeftHomologyData.K) :
    C.d (p + q) (p + q + 1) (tensorCochainPair h p q a.val b.val) = 0 := by
  rw [tensorCochainPair_leibniz, cycle_d_zero, cycle_d_zero]
  simp

private def tensorCyclePair {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ) :
    (A.sc p).moduleCatLeftHomologyData.K →ₗ[R]
      (B.sc q).moduleCatLeftHomologyData.K →ₗ[R]
        (C.sc (p + q)).moduleCatLeftHomologyData.K :=
  LinearMap.mk₂ _ (fun a b ↦ ⟨tensorCochainPair h p q a.val b.val, by
    change C.d (p + q) ((ComplexShape.up ℕ).next (p + q)) _ = 0
    rw [(ComplexShape.up ℕ).next_eq' (show p + q + 1 = p + q + 1 from rfl)]
    exact tensorCochainPair_cycle h p q a b⟩)
    (fun a a' b ↦ Subtype.ext (by
      change tensorCochainPair h p q (a.val + a'.val) b.val = _
      exact congrArg (fun f ↦ f b.val) ((tensorCochainPair h p q).map_add a.val a'.val)))
    (fun r a b ↦ Subtype.ext (by
      change tensorCochainPair h p q (r • a.val) b.val = _
      exact congrArg (fun f ↦ f b.val) ((tensorCochainPair h p q).map_smul r a.val)))
    (fun a b b' ↦ Subtype.ext (by
      change tensorCochainPair h p q a.val (b.val + b'.val) = _
      exact (tensorCochainPair h p q a.val).map_add b.val b'.val))
    (fun r a b ↦ Subtype.ext (by
      change tensorCochainPair h p q a.val (r • b.val) = _
      exact (tensorCochainPair h p q a.val).map_smul r b.val))

private lemma tensorCyclePair_boundary_left {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ)
    (a : (A.sc p).X₁)
    (b : (B.sc q).moduleCatLeftHomologyData.K) :
    tensorCyclePair h p q
        ((A.sc p).moduleCatToCycles a) b
      ∈ LinearMap.range
        (C.sc (p + q)).moduleCatToCycles := by
  cases p with
  | zero =>
    rw [toCycles_zero, LinearMap.map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  | succ p =>
    have hi : (ComplexShape.up ℕ).prev (p + 1) = p :=
      (ComplexShape.up ℕ).prev_eq' rfl
    let a' := (A.XIsoOfEq hi).hom a
    have ha : (((A.sc (p + 1)).moduleCatToCycles) a).val =
        A.d p (p + 1) a' := by
      dsimp only [a']
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_d]
      rfl
    have hdif := tensorCochainPair_leibniz h p q a' b.val
    rw [cycle_d_zero B q b] at hdif
    have hz : tensorCochainPair h p (q + 1) a' 0 = 0 :=
      (tensorCochainPair h p (q + 1) a').map_zero
    rw [hz, map_zero, smul_zero, add_zero] at hdif
    apply cycle_mem_range_of_d C (p + q) ((p + 1) + q) (by omega) _
      (tensorCochainPair h p q a' b.val)
    have hd := congrArg (fun f ↦ f (tensorCochainPair h p q a' b.val))
      (C.d_comp_XIsoOfEq_hom (Nat.add_right_comm p 1 q).symm (p + q))
    rw [ConcreteCategory.comp_apply, hdif] at hd
    simp only [HomologicalComplex.XIsoOfEq, eqToIso] at hd
    rw [← ConcreteCategory.comp_apply, eqToHom_trans, eqToHom_refl,
      CategoryTheory.id_apply] at hd
    change C.d (p + q) (p + 1 + q) _ = tensorCochainPair h (p + 1) q _ b.val
    rw [ha]
    exact hd.symm

set_option maxHeartbeats 1600000 in
-- Degree transports require extra unification work in the Leibniz calculation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma tensorCyclePair_boundary_right {R : Type v} [CommRing R]
    {A B C : CochainComplex (ModuleCat.{v} R) ℕ}
    (h : tensorTotal A B ⟶ C) (p q : ℕ)
    (a : (A.sc p).moduleCatLeftHomologyData.K)
    (b : (B.sc q).X₁) :
    tensorCyclePair h p q a
        ((B.sc q).moduleCatToCycles b)
      ∈ LinearMap.range
        (C.sc (p + q)).moduleCatToCycles := by
  cases q with
  | zero =>
    rw [toCycles_zero, LinearMap.map_zero]
    exact Submodule.zero_mem _
  | succ q =>
    have hi : (ComplexShape.up ℕ).prev (q + 1) = q :=
      (ComplexShape.up ℕ).prev_eq' rfl
    let b' := (B.XIsoOfEq hi).hom b
    have hb : (((B.sc (q + 1)).moduleCatToCycles) b).val =
        B.d q (q + 1) b' := by
      dsimp only [b']
      rw [← ConcreteCategory.comp_apply, HomologicalComplex.XIsoOfEq_hom_comp_d]
      rfl
    have hdif := tensorCochainPair_leibniz h p q a.val b'
    rw [cycle_d_zero A p a] at hdif
    have hz : tensorCochainPair h (p + 1) q 0 b' = 0 := by
      exact congrArg (fun f ↦ f b') (tensorCochainPair h (p + 1) q).map_zero
    rw [hz, map_zero, zero_add] at hdif
    have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
      rw [← mul_pow]
      simp
    have h' := congrArg (fun z ↦ (-1 : ℤ) ^ p • z) hdif
    rw [smul_smul, hs, one_smul] at h'
    apply cycle_mem_range_of_d C (p + q) (p + (q + 1)) (by omega) _
      ((-1 : ℤ) ^ p • tensorCochainPair h p q a.val b')
    have hd := congrArg
      (fun f ↦ f ((-1 : ℤ) ^ p • tensorCochainPair h p q a.val b'))
      (C.d_comp_XIsoOfEq_hom (Nat.add_assoc p q 1) (p + q))
    rw [ConcreteCategory.comp_apply, map_zsmul, h'] at hd
    simp only [HomologicalComplex.XIsoOfEq, eqToIso, eqToHom_refl] at hd
    change C.d (p + q) (p + (q + 1)) _ = tensorCochainPair h p (q + 1) a.val _
    rw [hb]
    exact hd.symm

private def axisCycleMap {R : Type v} [Ring R]
    {A B : CochainComplex (ModuleCat.{v} R) ℕ} (φ : A ⟶ B) (n : ℕ) :
    (A.sc n).moduleCatLeftHomologyData.K →ₗ[R] (B.sc n).moduleCatLeftHomologyData.K :=
  ((A.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
    (B.sc n).moduleCatCyclesIso.hom).hom

private lemma axisCycleMap_val {R : Type v} [Ring R]
    {A B : CochainComplex (ModuleCat.{v} R) ℕ} (φ : A ⟶ B) (n : ℕ)
    (z : (A.sc n).moduleCatLeftHomologyData.K) :
    (axisCycleMap φ n z).val = φ.f n z.val := by
  have he : ((A.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
      (B.sc n).moduleCatCyclesIso.hom) ≫ (B.sc n).moduleCatLeftHomologyData.i =
      (A.sc n).moduleCatLeftHomologyData.i ≫ φ.f n := by
    simp only [Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i]
    change (A.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
      B.iCycles n = _
    rw [HomologicalComplex.cyclesMap_i, ← Category.assoc]
    exact congrArg (fun f ↦ f ≫ φ.f n) (A.sc n).moduleCatCyclesIso_inv_iCycles
  exact congrArg (fun f ↦ f z) he

private lemma axisCycleMap_class {R : Type v} [Ring R]
    {A B : CochainComplex (ModuleCat.{v} R) ℕ} (φ : A ⟶ B) (n : ℕ)
    (z : (A.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyMap φ n (cupCycleClass A n z) =
      cupCycleClass B n (axisCycleMap φ n z) := by
  have he : ((A.sc n).moduleCatCyclesIso.inv ≫ (A.sc n).homologyπ) ≫
      HomologicalComplex.homologyMap φ n =
      ((A.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (B.sc n).moduleCatCyclesIso.hom) ≫
          ((B.sc n).moduleCatCyclesIso.inv ≫ (B.sc n).homologyπ) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact (A.sc n).moduleCatCyclesIso.inv ≫= HomologicalComplex.homologyπ_naturality φ n
  exact congrArg (fun f ↦ f z) he

set_option maxHeartbeats 1600000 in
-- Six axis identifications and the total-complex types require extra unification work.
/-- The signed Alexander--Whitney pairing descends to total homology and
computes both axis products. Only the chain maps and their component formulas
are required; no comparison isomorphism or sheaf cohomology cup is used.
Source: Stacks Project, Tags 07MB and 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-signed-axis-pairing)

Proof: for summands of bidegrees (r,i) and (s,j), restrict the front and back
Cech sections to the common intersection, apply D.pair r s, and multiply by
(-1)^(i*s). Extend bilinearly over the finite sums in each total degree.
D.restriction identifies restrictions of products with products of restrictions.
The adjacent shared-face terms in the alternating Cech differential cancel;
the remaining faces give the two Cech Leibniz terms. D.leibniz gives the
resolution differential terms, and the sign (-1)^(i*s) matches the total
Leibniz sign (-1)^(r+i). Thus products of cycles are cycles and a product
with a boundary is a boundary, so the pairing descends through both homology
quotients. On alpha images the Cech degrees are zero and the summands are the
global resolution product. On beta images both resolution degrees are zero;
D.augmentation_pair identifies the product with the coefficient Cech product.
The six component equations therefore give the two displayed class formulas.

The Lean proof reuses exists_cupCech_total_cochain_pairing for the cochain
morphism and its axis formulas. It proves the tensor Leibniz identity,
cycle and boundary preservation, and naturality of cycle classes explicitly,
then reuses bilinear_homology_desc to pass to the two homology quotients.
Empty families, zero complexes and zero inputs cause no exception: the finite
sum and quotient constructions still apply, with the corresponding maps zero. -/
theorem cupCech_signed_axis_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (lalpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (lbeta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (hlalpha : ∀ n : ℕ, lalpha.f n = moduleCechZero U (D.left.K.X n) ≫
      (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hlbeta : ∀ n : ℕ, lbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.left.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (ralpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (rbeta : (cechComplexFunctor U).obj G.presheafModuleCat ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (hralpha : ∀ n : ℕ, ralpha.f n = moduleCechZero U (D.right.K.X n) ≫
      (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hrbeta : ∀ n : ℕ, rbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.right.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (talpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (tbeta : (cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (htalpha : ∀ n : ℕ, talpha.f n = moduleCechZero U (D.target.K.X n) ≫
      (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (htbeta : ∀ n : ℕ, tbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.target.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap lalpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap ralpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap talpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = n2CechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap lbeta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap rbeta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap tbeta (p + q) (cupCycleClass _ (p + q) c)) := by
  have elalpha : lalpha = cupCechAlpha U D.left := by
    ext n : 1
    exact hlalpha n
  have eralpha : ralpha = cupCechAlpha U D.right := by
    ext n : 1
    exact hralpha n
  have etalpha : talpha = cupCechAlpha U D.target := by
    ext n : 1
    exact htalpha n
  have elbeta : lbeta = cupCechBeta U D.left := by
    ext n : 1
    exact hlbeta n
  have erbeta : rbeta = cupCechBeta U D.right := by
    ext n : 1
    exact hrbeta n
  have etbeta : tbeta = cupCechBeta U D.target := by
    ext n : 1
    exact htbeta n
  obtain ⟨h, halpha, hbeta⟩ := exists_cupCech_total_cochain_pairing U D
  obtain ⟨t, ht⟩ := bilinear_homology_desc _ _ _ p q (p + q) (tensorCyclePair h p q)
    (tensorCyclePair_boundary_left h p q) (tensorCyclePair_boundary_right h p q)
  refine ⟨t, ?_, ?_⟩
  · intro a b c hc
    rw [axisCycleMap_class, axisCycleMap_class, axisCycleMap_class, ht]
    congr 1
    apply Subtype.ext
    change tensorCochainPair h p q (axisCycleMap lalpha p a).val
      (axisCycleMap ralpha q b).val = (axisCycleMap talpha (p + q) c).val
    rw [axisCycleMap_val, axisCycleMap_val, axisCycleMap_val,
      elalpha, eralpha, etalpha, hc]
    exact halpha p q a.val b.val
  · intro a b c hc
    rw [axisCycleMap_class, axisCycleMap_class, axisCycleMap_class, ht]
    congr 1
    apply Subtype.ext
    change tensorCochainPair h p q (axisCycleMap lbeta p a).val
      (axisCycleMap rbeta q b).val = (axisCycleMap tbeta (p + q) c).val
    rw [axisCycleMap_val, axisCycleMap_val, axisCycleMap_val,
      elbeta, erbeta, etbeta, hc]
    exact hbeta p q a.val b.val

end
end AlgebraicGeometry.Scheme.Modules
