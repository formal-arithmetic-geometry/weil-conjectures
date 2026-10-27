/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Sheaf.Algebra.Homology.LocalRHomCohomologicalBound
import Sheaf.CategoryTheory.PostnikovAdditiveExactCouple

/-! # Finite-diagonal internal hyper-Ext

Source: Stacks Project, derived.tex, Tag 015W (filtered-derived method),
sites-cohomology.tex, Tags 0A94 and 0A95, and homology.tex, Tags 011R, 011T and 012U.
This is the Postnikov/internal-Hom variant, rather than a left-exact functor on the heart.
It supplies the truncation passage in ILO XVII 10.1.1, proof p. 325.
(blueprint: lem-per-bounded-above-rhom-hyperext).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def hyperExtPageExtend
    (β : {s : ℤ // 2 ≤ s} → Sort v)
    (f : ∀ i : ℕ, β ⟨(i : ℤ) + 2, by omega⟩)
    (s : ℤ) (hs : 2 ≤ s) : β ⟨s, hs⟩ :=
  Eq.mpr (congrArg β (show (⟨s, hs⟩ : {s : ℤ // 2 ≤ s}) =
    ⟨((s - 2).toNat : ℤ) + 2, by omega⟩ by
    apply Subtype.ext
    dsimp
    omega)) (f (s - 2).toNat)

private theorem hyperExtPageExtend_nat
    (β : {s : ℤ // 2 ≤ s} → Sort v)
    (f : ∀ i : ℕ, β ⟨(i : ℤ) + 2, by omega⟩) (i : ℕ) (hs : 2 ≤ (i : ℤ) + 2) :
    hyperExtPageExtend β f ((i : ℤ) + 2) hs = f i := by
  apply eq_of_heq
  dsimp only [hyperExtPageExtend]
  simp only [eq_mpr_eq_cast, cast_heq_iff_heq]
  exact congr_arg_heq f (show ((i : ℤ) + 2 - 2).toNat = i by omega)

private abbrev hyperExtEmbedding (ρ s : ℤ) :
    (ComplexShape.up' (s, 1 - s)).Embedding (ComplexShape.up' (s, 1 - s)) :=
  ComplexShape.Embedding.mk' _ _ (fun pq ↦ (pq.1 + ρ, pq.2))
    (by intro a b h; ext <;> have := congrArg _root_.Prod.fst h <;>
      have := congrArg _root_.Prod.snd h <;> dsimp at * <;> omega)
    (by intro a b; change a + (s, 1 - s) = b ↔
          (a.1 + ρ, a.2) + (s, 1 - s) = (b.1 + ρ, b.2)
        simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add]
        omega)

private instance (ρ s : ℤ) : (hyperExtEmbedding ρ s).IsRelIff :=
  inferInstanceAs (ComplexShape.Embedding.mk' _ _ _ _ _).IsRelIff

private theorem hyperExt_prev (s : ℤ) (pq : ℤ × ℤ) :
    (ComplexShape.up' (s, 1 - s)).prev pq = (pq.1 - s, pq.2 - (1 - s)) :=
  ComplexShape.prev_eq' _ (by change (_, _) + (s, 1 - s) = pq; ext <;> dsimp <;> omega)

private theorem hyperExt_next (s : ℤ) (pq : ℤ × ℤ) :
    (ComplexShape.up' (s, 1 - s)).next pq = (pq.1 + s, pq.2 + (1 - s)) :=
  ComplexShape.next_eq' _ rfl

private noncomputable def hyperExtCyclesIso {B : Type*} [Category* B] [Abelian B]
    (ρ s : ℤ) (K : HomologicalComplex B (ComplexShape.up' (s, 1 - s))) (pq : ℤ × ℤ) :
    (K.restriction (hyperExtEmbedding ρ s)).cycles pq ≅ K.cycles (pq.1 + ρ, pq.2) :=
  K.restrictionCyclesIso (hyperExtEmbedding ρ s) pq _ (hyperExt_next s pq) rfl rfl
    (by rw [hyperExt_next]; congr 1; dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)

private noncomputable def hyperExtHomologyIso {B : Type*} [Category* B] [Abelian B]
    (ρ s : ℤ) (K : HomologicalComplex B (ComplexShape.up' (s, 1 - s))) (pq : ℤ × ℤ) :
    (K.restriction (hyperExtEmbedding ρ s)).homology pq ≅ K.homology (pq.1 + ρ, pq.2) :=
  K.restrictionHomologyIso (hyperExtEmbedding ρ s) _ pq _
    (hyperExt_prev s pq) (hyperExt_next s pq) rfl rfl rfl
    (by rw [hyperExt_prev]; congr 1; dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)
    (by rw [hyperExt_next]; congr 1; dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)

@[reassoc]
private theorem hyperExtCyclesIso_i {B : Type*} [Category* B] [Abelian B]
    (ρ s : ℤ) (K : HomologicalComplex B (ComplexShape.up' (s, 1 - s))) (pq : ℤ × ℤ) :
    (hyperExtCyclesIso ρ s K pq).hom ≫ K.iCycles (pq.1 + ρ, pq.2) =
      (K.restriction (hyperExtEmbedding ρ s)).iCycles pq := by
  simpa only [hyperExtCyclesIso, HomologicalComplex.restrictionXIso, eqToIso_refl, Iso.refl_hom,
    Category.comp_id] using K.restrictionCyclesIso_hom_iCycles (hyperExtEmbedding ρ s) pq _
    (hyperExt_next s pq) (j' := (pq.1 + ρ, pq.2)) rfl rfl
    (by rw [hyperExt_next]; ext <;> dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)

@[reassoc]
private theorem hyperExtHomologyIso_π {B : Type*} [Category* B] [Abelian B]
    (ρ s : ℤ) (K : HomologicalComplex B (ComplexShape.up' (s, 1 - s))) (pq : ℤ × ℤ) :
    (K.restriction (hyperExtEmbedding ρ s)).homologyπ pq ≫
        (hyperExtHomologyIso ρ s K pq).hom =
      (hyperExtCyclesIso ρ s K pq).hom ≫ K.homologyπ (pq.1 + ρ, pq.2) := by
  exact K.homologyπ_restrictionHomologyIso_hom (hyperExtEmbedding ρ s) _ pq _
    (hyperExt_prev s pq) (hyperExt_next s pq) rfl rfl rfl
    (by rw [hyperExt_prev]; congr 1; dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)
    (by rw [hyperExt_next]; congr 1; dsimp [hyperExtEmbedding, ComplexShape.Embedding.mk']; omega)

private theorem hyperExtRestriction_square {B : Type*} [Category* B] [Abelian B]
    (ρ s : ℤ) (K : HomologicalComplex B (ComplexShape.up' (s, 1 - s)))
    (pq : ℤ × ℤ) {Z : B} (u : K.X (pq.1 + ρ, pq.2) ⟶ Z)
    (v : K.homology (pq.1 + ρ, pq.2) ⟶ Z)
    (h : K.iCycles (pq.1 + ρ, pq.2) ≫ u = K.homologyπ (pq.1 + ρ, pq.2) ≫ v) :
    (K.restriction (hyperExtEmbedding ρ s)).iCycles pq ≫ u =
      (K.restriction (hyperExtEmbedding ρ s)).homologyπ pq ≫
        (hyperExtHomologyIso ρ s K pq).hom ≫ v := by
  rw [← Category.assoc, hyperExtHomologyIso_π, Category.assoc, ← h,
    ← Category.assoc, hyperExtCyclesIso_i]

private noncomputable def hyperExtTranslate {B : Type*} [Category* B] [Abelian B]
    (ρ : ℤ) : E₂CohomologicalSpectralSequence B ⥤ E₂CohomologicalSpectralSequence B where
  obj E :=
    { page s hs := (E.page s hs).restriction (hyperExtEmbedding ρ s)
      iso s t pq h hs := hyperExtHomologyIso ρ s (E.page s hs) pq ≪≫
        E.iso s t (pq.1 + ρ, pq.2) h hs }
  map {E G} f :=
    { hom s hs := HomologicalComplex.restrictionMap (f.hom s hs) (hyperExtEmbedding ρ s)
      comm s t pq h hs := by
        dsimp
        rw [← Category.assoc]
        have hn : HomologicalComplex.homologyMap
            (HomologicalComplex.restrictionMap (f.hom s hs) (hyperExtEmbedding ρ s)) pq ≫
              (hyperExtHomologyIso ρ s (G.page s hs) pq).hom =
            (hyperExtHomologyIso ρ s (E.page s hs) pq).hom ≫
              HomologicalComplex.homologyMap (f.hom s hs) (pq.1 + ρ, pq.2) := by
          apply (cancel_epi (((E.page s hs).restriction
            (hyperExtEmbedding ρ s)).homologyπ pq)).1
          try simp only [Category.assoc]
          rw [HomologicalComplex.homologyπ_naturality_assoc]
          rw [hyperExtHomologyIso_π]
          conv_rhs => rw [← Category.assoc, hyperExtHomologyIso_π]
          rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
          simp only [← Category.assoc]
          apply congrArg (fun k ↦ k ≫ (G.page s hs).homologyπ (pq.1 + ρ, pq.2))
          apply (cancel_mono ((G.page s hs).iCycles (pq.1 + ρ, pq.2))).1
          simp only [Category.assoc, HomologicalComplex.cyclesMap_i, hyperExtCyclesIso_i,
            hyperExtCyclesIso_i_assoc]
          rfl
        rw [hn, Category.assoc, f.comm s t (pq.1 + ρ, pq.2) h hs]
        simp only [Category.assoc]
        rfl }

set_option backward.isDefEq.respectTransparency false in
private theorem hyperExtPullback_transport {C : Type u} [Category.{v} C] [Abelian C]
    {A B P Q : C} (U : Subobject A) (V : Subobject B)
    (px : (U : C) ⟶ P) (py : (V : C) ⟶ Q)
    (t : A ⟶ B) (z : (U : C) ⟶ (V : C)) (e : P ⟶ Q)
    (hz : z ≫ V.arrow = U.arrow ≫ t) (hp : z ≫ py = px ≫ e)
    (S : Subobject P) (R : Subobject Q)
    (h : R.Factors (S.arrow ≫ e)) :
    ((Subobject.«exists» V.arrow).obj ((Subobject.pullback py).obj R)).Factors
      (((Subobject.«exists» U.arrow).obj ((Subobject.pullback px).obj S)).arrow ≫ t) := by
  classical
  let SX := (Subobject.pullback px).obj S
  let SY := (Subobject.pullback py).obj R
  let UX := (Subobject.«exists» U.arrow).obj SX
  let VY := (Subobject.«exists» V.arrow).obj SY
  have heq : UX = Subobject.mk (SX.arrow ≫ U.arrow) := by
    dsimp [UX]
    rw [Subobject.exists_iso_map, ← Subobject.map_mk, Subobject.mk_arrow]
  let ux := (Subobject.isoOfEqMk UX (SX.arrow ≫ U.arrow) heq).hom
  have hux : ux ≫ SX.arrow ≫ U.arrow = UX.arrow := by
    simpa only [ux, Subobject.isoOfEqMk_hom, Category.assoc] using
      (Subobject.ofLEMk_comp heq.le)
  have hf : R.Factors (SX.arrow ≫ z ≫ py) := by
    rw [hp]
    have hs : S.Factors (SX.arrow ≫ px) :=
      (pullback_factors_iff px S SX.arrow).mp (Subobject.factors_self SX)
    have hh := Subobject.factors_of_factors_right (S.factorThru _ hs) h
    simpa only [← Category.assoc, Subobject.factorThru_arrow] using hh
  have hsy : SY.Factors (SX.arrow ≫ z) :=
    pullback_factors py R _ (by simpa only [Category.assoc] using hf)
  let sy := SY.factorThru _ hsy
  let vy : (SY : C) ⟶ (VY : C) := (Subobject.imageFactorisation V.arrow SY).F.e
  have hvy : vy ≫ VY.arrow = SY.arrow ≫ V.arrow :=
    (Subobject.imageFactorisation V.arrow SY).F.fac
  apply (Subobject.factors_iff _ _).mpr
  refine ⟨ux ≫ sy ≫ vy, ?_⟩
  change (ux ≫ sy ≫ vy) ≫ VY.arrow = UX.arrow ≫ t
  rw [Category.assoc, Category.assoc, hvy,
    ← Category.assoc sy, Subobject.factorThru_arrow, Category.assoc,
    hz]
  simpa only [Category.assoc] using congrArg (fun a ↦ a ≫ t) hux

private theorem hyperExtTower_natural {C : Type u} [Category.{v} C] [Abelian C]
    (X Y : BigradedExactCouple C 0)
    (t : ∀ p q : ℤ, X.E p q ⟶ Y.E p q)
    (e : ∀ (r : ℕ) (p q : ℤ), (X.pageCouple r).E p q ⟶ (Y.pageCouple r).E p q)
    (hzero : ∀ p q, e 0 p q = t p q)
    (hd : ∀ r p q, e r p q ≫ (Y.pageCouple r).d p q =
      (X.pageCouple r).d p q ≫ e r (p + 2 + r) (q - 1 - r))
    (hnext : ∀ r p q,
      ∃ k : kernel ((X.pageCouple r).d p q) ⟶ kernel ((Y.pageCouple r).d p q),
        k ≫ kernel.ι ((Y.pageCouple r).d p q) =
          kernel.ι ((X.pageCouple r).d p q) ≫ e r p q ∧
        (X.pageCouple r).derivedEProjection p q ≫ e (r + 1) p q =
          k ≫ (Y.pageCouple r).derivedEProjection p q) :
    ∀ r p q, ∃ z : (X.cycleBoundaryTower.Z r p q : C) ⟶
        (Y.cycleBoundaryTower.Z r p q : C),
      z ≫ (Y.cycleBoundaryTower.Z r p q).arrow =
        (X.cycleBoundaryTower.Z r p q).arrow ≫ t p q ∧
      z ≫ Y.cycleBoundaryTower.projection r p q =
        X.cycleBoundaryTower.projection r p q ≫ e r p q := by
  classical
  let TX := X.cycleBoundaryTower
  let TY := Y.cycleBoundaryTower
  have hind : ∀ r p q, ∃ z : (TX.Z r p q : C) ⟶ (TY.Z r p q : C),
      z ≫ (TY.Z r p q).arrow = (TX.Z r p q).arrow ≫ t p q ∧
      z ≫ TY.projection r p q = TX.projection r p q ≫ e r p q := by
    intro r
    induction r with
    | zero =>
      intro p q
      have hz : (TY.Z 0 p q).Factors ((TX.Z 0 p q).arrow ≫ t p q) := by
        rw [TY.Z_zero]
        exact Subobject.top_factors _
      refine ⟨(TY.Z 0 p q).factorThru _ hz, Subobject.factorThru_arrow _ _ _, ?_⟩
      rw [TX.projection_zero, TY.projection_zero, hzero]
      exact Subobject.factorThru_arrow _ _ _
    | succ r ih =>
      intro p q
      obtain ⟨z, hz, hp⟩ := ih p q
      have hkern : (kernelSubobject ((Y.pageCouple r).d p q)).Factors
          ((kernelSubobject ((X.pageCouple r).d p q)).arrow ≫ e r p q) := by
        apply kernelSubobject_factors
        rw [Category.assoc, hd, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
      have hZ := hyperExtPullback_transport (TX.Z r p q) (TY.Z r p q)
        (TX.projection r p q) (TY.projection r p q) (t p q) z (e r p q) hz hp
        (kernelSubobject ((X.pageCouple r).d p q))
        (kernelSubobject ((Y.pageCouple r).d p q)) hkern
      rw [← TX.Z_succ, ← TY.Z_succ] at hZ
      let zn := (TY.Z (r + 1) p q).factorThru _ hZ
      have hzn : zn ≫ (TY.Z (r + 1) p q).arrow =
          (TX.Z (r + 1) p q).arrow ≫ t p q := Subobject.factorThru_arrow _ _ _
      refine ⟨zn, hzn, ?_⟩
      obtain ⟨k, hk, hkn⟩ := hnext r p q
      have hc : TX.cycleLift r p q ≫ k = zn ≫ TY.cycleLift r p q := by
        apply (cancel_mono (kernel.ι ((Y.pageCouple r).d p q))).mp
        rw [Category.assoc, hk, ← Category.assoc, TX.cycleLift_comm,
          Category.assoc, ← hp, ← Category.assoc,
          Category.assoc zn, TY.cycleLift_comm, ← Category.assoc]
        congr 1
        apply (cancel_mono (TY.Z r p q).arrow).mp
        rw [Category.assoc, hz, ← Category.assoc, Subobject.ofLE_arrow,
          Category.assoc, Subobject.ofLE_arrow, hzn]
      rw [TX.projection_succ, TY.projection_succ, ← Category.assoc, ← hc,
        Category.assoc, ← hkn, Category.assoc]
  exact hind

private theorem hyperExtLimitCycle_eq {B : Type*} [Category* B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects) (i : ℕ) (p q : ℤ)
    (hs : ∀ j : ℕ, i ≤ j → ∃ z : (X.pageCouple j).E p q ≅
        (X.pageCouple (j + 1)).E p q,
      kernel.ι ((X.pageCouple j).d p q) ≫ z.hom =
        (X.pageCouple j).derivedEProjection p q) :
    L.Z p q = X.cycleBoundaryTower.Z i p q := by
  let T := X.cycleBoundaryTower
  have hd (j : ℕ) (hj : i ≤ j) : (X.pageCouple j).d p q = 0 := by
    obtain ⟨z, hz⟩ := hs j hj
    have he : kernel.ι ((X.pageCouple j).d p q) =
        (X.pageCouple j).derivedEProjection p q ≫ z.inv := by
      rw [← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    have : Epi (kernel.ι ((X.pageCouple j).d p q)) := by rw [he]; infer_instance
    exact (cancel_epi (kernel.ι ((X.pageCouple j).d p q))).1 (by simp)
  have hz (j : ℕ) (hj : i ≤ j) : T.Z (j + 1) p q = T.Z j p q := by
    rw [T.Z_succ, hd j hj, kernelSubobject_zero]
    simp only [Subobject.pullback_top, Subobject.exists_iso_map, Subobject.map_top,
      Subobject.mk_arrow]
  have hall (j : ℕ) (hj : i ≤ j) : T.Z j p q = T.Z i p q := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.add_succ] using (hz (i + k) (by omega)).trans (ih (by omega))
  apply le_antisymm ((L.Z_glb p q).1 ⟨i, rfl⟩)
  apply (L.Z_glb p q).2
  rintro _ ⟨j, rfl⟩
  by_cases h : i ≤ j
  · exact (hall j h).ge
  · exact (antitone_nat_of_succ_le (f := fun j ↦ T.Z j p q)
      (fun j ↦ T.Z_decreasing j p q)) (show j ≤ i by omega)

private theorem hyperExtLate_epi {B : Type*} [Category* B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects) (i : ℕ) (p q : ℤ)
    (hZ : L.Z p q = X.cycleBoundaryTower.Z i p q)
    (z : (L.Z p q : B) ⟶ (X.cycleBoundaryTower.Z i p q : B))
    (hz : z ≫ (X.cycleBoundaryTower.Z i p q).arrow = (L.Z p q).arrow) : IsIso z := by
  have : z = (Subobject.isoOfEq _ _ hZ).hom := by
    apply (cancel_mono (X.cycleBoundaryTower.Z i p q).arrow).1
    simpa using hz
  rw [this]
  infer_instance

private theorem hyperExtLate_transition {B : Type*} [Category* B] [Abelian B]
    (X : BigradedExactCouple B 0) (L : X.LimitSubobjects) (i : ℕ) (p q : ℤ)
    (zi : (L.Z p q : B) ⟶ (X.cycleBoundaryTower.Z i p q : B)) [IsIso zi]
    (zj : (L.Z p q : B) ⟶ (X.cycleBoundaryTower.Z (i + 1) p q : B)) [IsIso zj]
    (hi : zi ≫ (X.cycleBoundaryTower.Z i p q).arrow = (L.Z p q).arrow)
    (hj : zj ≫ (X.cycleBoundaryTower.Z (i + 1) p q).arrow = (L.Z p q).arrow)
    (vi : (X.pageCouple i).E p q ≅ X.pageInfinity L p q)
    (vj : (X.pageCouple (i + 1)).E p q ≅ X.pageInfinity L p q)
    (hvi : zi ≫ X.cycleBoundaryTower.projection i p q ≫ vi.hom =
      cokernel.π (Subobject.ofLE _ _ (BigradedExactCouple.limitBoundary_le_cycle X L p q)))
    (hvj : zj ≫ X.cycleBoundaryTower.projection (i + 1) p q ≫ vj.hom =
      cokernel.π (Subobject.ofLE _ _ (BigradedExactCouple.limitBoundary_le_cycle X L p q))) :
    kernel.ι ((X.pageCouple i).d p q) ≫ vi.hom =
      (X.pageCouple i).derivedEProjection p q ≫ vj.hom := by
  let T := X.cycleBoundaryTower
  have hz : zj ≫ Subobject.ofLE _ _ (T.Z_decreasing i p q) = zi := by
    apply (cancel_mono (T.Z i p q).arrow).1
    simpa only [Category.assoc, Subobject.ofLE_arrow] using hj.trans hi.symm
  have hi : IsIso (Subobject.ofLE _ _ (T.Z_decreasing i p q)) := by
    have heq : Subobject.ofLE _ _ (T.Z_decreasing i p q) = inv zj ≫ zi := by
      rw [IsIso.eq_inv_comp, hz]
    rw [heq]
    infer_instance
  have hec : Epi (T.cycleLift i p q ≫ kernel.ι ((X.pageCouple i).d p q)) := by
    rw [T.cycleLift_comm]
    let := T.projection_epi i p q
    infer_instance
  have hek : Epi (kernel.ι ((X.pageCouple i).d p q)) := epi_of_epi (T.cycleLift i p q) _
  have hik : IsIso (kernel.ι ((X.pageCouple i).d p q)) := isIso_of_mono_of_epi _
  have he : Epi (T.cycleLift i p q) :=
    (epi_comp_iff_of_isIso _ (kernel.ι ((X.pageCouple i).d p q))).mp hec
  apply (cancel_epi (zj ≫ T.cycleLift i p q)).1
  calc
    (zj ≫ T.cycleLift i p q) ≫ kernel.ι ((X.pageCouple i).d p q) ≫ vi.hom =
        (zj ≫ Subobject.ofLE _ _ (T.Z_decreasing i p q)) ≫
          T.projection i p q ≫ vi.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ zj ≫ k ≫ vi.hom) (T.cycleLift_comm i p q)
    _ = zi ≫ T.projection i p q ≫ vi.hom := by rw [hz]
    _ = cokernel.π _ := hvi
    _ = zj ≫ T.projection (i + 1) p q ≫ vj.hom := hvj.symm
    _ = (zj ≫ T.cycleLift i p q) ≫ (X.pageCouple i).derivedEProjection p q ≫
        vj.hom := by rw [T.projection_succ]; simp only [Category.assoc]

private theorem hyperExtLate_natural {B : Type*} [Category* B] [Abelian B]
    (X Y : BigradedExactCouple B 0) (LX : X.LimitSubobjects) (LY : Y.LimitSubobjects)
    (i : ℕ) (p q : ℤ) (t : X.E p q ⟶ Y.E p q)
    (e : (X.pageCouple i).E p q ⟶ (Y.pageCouple i).E p q)
    (zx : (LX.Z p q : B) ⟶ (X.cycleBoundaryTower.Z i p q : B)) [IsIso zx]
    (zy : (LY.Z p q : B) ⟶ (Y.cycleBoundaryTower.Z i p q : B))
    (hx : zx ≫ (X.cycleBoundaryTower.Z i p q).arrow = (LX.Z p q).arrow)
    (hy : zy ≫ (Y.cycleBoundaryTower.Z i p q).arrow = (LY.Z p q).arrow)
    (vx : (X.pageCouple i).E p q ≅ X.pageInfinity LX p q)
    (vy : (Y.pageCouple i).E p q ≅ Y.pageInfinity LY p q)
    (hvx : zx ≫ X.cycleBoundaryTower.projection i p q ≫ vx.hom =
      cokernel.π (Subobject.ofLE _ _ (BigradedExactCouple.limitBoundary_le_cycle X LX p q)))
    (hvy : zy ≫ Y.cycleBoundaryTower.projection i p q ≫ vy.hom =
      cokernel.π (Subobject.ofLE _ _ (BigradedExactCouple.limitBoundary_le_cycle Y LY p q)))
    (z : (LX.Z p q : B) ⟶ (LY.Z p q : B))
    (v : X.pageInfinity LX p q ⟶ Y.pageInfinity LY p q)
    (hz : z ≫ (LY.Z p q).arrow = (LX.Z p q).arrow ≫ t)
    (hv : cokernel.π (Subobject.ofLE _ _
        (BigradedExactCouple.limitBoundary_le_cycle X LX p q)) ≫ v =
      z ≫ cokernel.π (Subobject.ofLE _ _
        (BigradedExactCouple.limitBoundary_le_cycle Y LY p q)))
    (hn : ∃ f : (X.cycleBoundaryTower.Z i p q : B) ⟶
        (Y.cycleBoundaryTower.Z i p q : B),
      f ≫ (Y.cycleBoundaryTower.Z i p q).arrow =
        (X.cycleBoundaryTower.Z i p q).arrow ≫ t ∧
      f ≫ Y.cycleBoundaryTower.projection i p q =
        X.cycleBoundaryTower.projection i p q ≫ e) :
    e ≫ vy.hom = vx.hom ≫ v := by
  obtain ⟨f, hf, hfp⟩ := hn
  have hw : zx ≫ f = z ≫ zy := by
    apply (cancel_mono (Y.cycleBoundaryTower.Z i p q).arrow).1
    simp only [Category.assoc]
    rw [hf, hy, ← Category.assoc, hx, hz]
  let : Epi (X.cycleBoundaryTower.projection i p q) :=
    X.cycleBoundaryTower.projection_epi _ _ _
  apply (cancel_epi (zx ≫ X.cycleBoundaryTower.projection i p q)).1
  calc
    (zx ≫ X.cycleBoundaryTower.projection i p q) ≫ e ≫ vy.hom =
        (zx ≫ f) ≫ Y.cycleBoundaryTower.projection i p q ≫ vy.hom := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ zx ≫ k ≫ vy.hom) hfp.symm
    _ = (z ≫ zy) ≫ Y.cycleBoundaryTower.projection i p q ≫ vy.hom := by rw [hw]
    _ = z ≫ (zy ≫ Y.cycleBoundaryTower.projection i p q ≫ vy.hom) := by
      simp only [Category.assoc]
    _ = z ≫ cokernel.π _ := by rw [hvy]
    _ = cokernel.π _ ≫ v := hv.symm
    _ = (zx ≫ X.cycleBoundaryTower.projection i p q) ≫ vx.hom ≫ v := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ v) hvx.symm

private noncomputable def hyperExtFiltration {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) : DecreasingFiltration Y where
  F p := Subobject.mk ((F.F p).arrow ≫ e.hom)
  F_succ_le p := Subobject.mk_le_mk_of_comm (Subobject.ofLE _ _ (F.F_succ_le p))
    (by simp)

private noncomputable def hyperExtStepIso {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) :
    (F.F p : B) ≅ ((hyperExtFiltration F e).F p : B) :=
  (Subobject.underlyingIso ((F.F p).arrow ≫ e.hom)).symm

@[reassoc]
private theorem hyperExtStepIso_arrow {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) :
    (hyperExtStepIso F e p).hom ≫ ((hyperExtFiltration F e).F p).arrow =
      (F.F p).arrow ≫ e.hom := Subobject.underlyingIso_arrow _

private noncomputable def hyperExtGrIso {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) :
    F.gr p ≅ (hyperExtFiltration F e).gr p :=
  cokernel.mapIso _ _ (hyperExtStepIso F e (p + 1)) (hyperExtStepIso F e p) (by
    apply (cancel_mono ((hyperExtFiltration F e).F p).arrow).1
    simp only [Category.assoc, Subobject.ofLE_arrow, hyperExtStepIso_arrow,
      Subobject.ofLE_arrow_assoc])

@[reassoc]
private theorem hyperExtGrIso_π {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (F.F_succ_le p)) ≫ (hyperExtGrIso F e p).hom =
      (hyperExtStepIso F e p).hom ≫ cokernel.π
        (Subobject.ofLE _ _ ((hyperExtFiltration F e).F_succ_le p)) := by
  simp [hyperExtGrIso, cokernel.map]

private theorem hyperExtFiltration_top {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) (hp : F.F p = ⊤) :
    (hyperExtFiltration F e).F p = ⊤ := by
  let : IsIso (F.F p).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr hp
  exact Subobject.mk_eq_top_of_isIso _

private theorem hyperExtFiltration_bot {B : Type*} [Category* B] [Abelian B]
    {X Y : B} (F : DecreasingFiltration X) (e : X ≅ Y) (p : ℤ) (hp : F.F p = ⊥) :
    (hyperExtFiltration F e).F p = ⊥ := by
  apply Subobject.mk_eq_bot_iff_zero.mpr
  have hz : IsZero (F.F p : B) := by rw [hp]; exact (isZero_zero B).of_iso Subobject.botCoeIsoZero
  exact hz.eq_of_src _ _

@[reassoc]
private theorem hyperExtRestriction_arrow {B : Type*} [Category* B] [Abelian B]
    {X Y : FilteredObject B} (f : FilteredObject.Hom X Y) (p : ℤ) :
    FilteredObject.restrictionSteps f p ≫ (Y.filtration.F p).arrow =
      (X.filtration.F p).arrow ≫ f.hom := Classical.choose_spec (f.preserves p)

@[reassoc]
private theorem hyperExtGraded_π {B : Type*} [Category* B] [Abelian B]
    {X Y : FilteredObject B} (f : FilteredObject.Hom X Y) (p : ℤ) :
    cokernel.π (Subobject.ofLE _ _ (X.filtration.F_succ_le p)) ≫
        FilteredObject.gradedMapSteps f p =
      FilteredObject.restrictionSteps f p ≫
        cokernel.π (Subobject.ofLE _ _ (Y.filtration.F_succ_le p)) :=
  Classical.choose_spec (FilteredObject.exists_gradedMap_steps X Y f p)

private theorem hyperExtGrIso_natural {B : Type*} [Category* B] [Abelian B]
    {X Y X' Y' : B} (F : DecreasingFiltration X) (G : DecreasingFiltration Y)
    (ex : X ≅ X') (ey : Y ≅ Y') (t : X ⟶ Y) (t' : X' ⟶ Y')
    (ht : t ≫ ey.hom = ex.hom ≫ t')
    (f : FilteredObject.Hom ⟨X', hyperExtFiltration F ex⟩ ⟨Y', hyperExtFiltration G ey⟩)
    (hf : f.hom = t') (p : ℤ) (l : (F.F p : B) ⟶ (G.F p : B))
    (hl : l ≫ (G.F p).arrow = (F.F p).arrow ≫ t)
    (g : F.gr p ⟶ G.gr p)
    (hg : cokernel.π (Subobject.ofLE _ _ (F.F_succ_le p)) ≫ g =
      l ≫ cokernel.π (Subobject.ofLE _ _ (G.F_succ_le p))) :
    (hyperExtGrIso F ex p).hom ≫ FilteredObject.gradedMapSteps f p =
      g ≫ (hyperExtGrIso G ey p).hom := by
  have hs : (hyperExtStepIso F ex p).hom ≫ FilteredObject.restrictionSteps f p =
      l ≫ (hyperExtStepIso G ey p).hom := by
    apply (cancel_mono ((hyperExtFiltration G ey).F p).arrow).1
    have hr := hyperExtRestriction_arrow f p
    dsimp only at hr
    simp only [Category.assoc]
    rw [hr, hf, ← Category.assoc, hyperExtStepIso_arrow, Category.assoc, ← ht]
    rw [← Category.assoc, ← hl, Category.assoc, hyperExtStepIso_arrow]
  apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ (F.F_succ_le p)))).1
  calc
    _ = (hyperExtStepIso F ex p).hom ≫
        FilteredObject.restrictionSteps f p ≫ cokernel.π _ := by
      have hπ := hyperExtGraded_π f p
      dsimp only at hπ
      rw [← Category.assoc, hyperExtGrIso_π, Category.assoc, hπ]
    _ = l ≫ (hyperExtStepIso G ey p).hom ≫ cokernel.π _ := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ cokernel.π _) hs
    _ = l ≫ cokernel.π _ ≫ (hyperExtGrIso G ey p).hom := by
      rw [hyperExtGrIso_π]
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun k ↦ k ≫ (hyperExtGrIso G ey p).hom) hg.symm

private theorem hyperExtFromPostnikov
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (U : ℤ → DerivedCategory A ⥤ A) (r c : ℤ)
    (hadd : ∀ n, (U n).Additive) (hhom : (U 0).IsHomological)
    (ε : ∀ n, DerivedCategory.postnikovValue (U 0) n ≅ U n)
    (hamp : ∀ (b n : ℤ) (M : DerivedCategory A), M.IsGE b → n < b - r →
      IsZero ((DerivedCategory.postnikovValue (U 0) n).obj M)) :
    ∃ E : DerivedCategory.postnikovLowerCategory A c ⥤ E₂CohomologicalSpectralSequence A,
    ∃ e2 : ∀ (L : DerivedCategory.postnikovLowerCategory A c) (p q : ℤ),
      ((E.obj L).page 2).X (p, q) ≅
        (U p).obj ((DerivedCategory.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A q).obj L.obj)),
    ∃ F : ∀ (L : DerivedCategory.postnikovLowerCategory A c) (n : ℤ),
      DecreasingFiltration ((U n).obj L.obj),
    ∃ a : ∀ (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c} (_f : L ⟶ M),
      FilteredObject.Hom ⟨(U n).obj L.obj, F L n⟩ ⟨(U n).obj M.obj, F M n⟩,
    ∃ conv : ∀ (L : DerivedCategory.postnikovLowerCategory A c) (s : ℤ)
      (hs : 2 ≤ s) (p q : ℤ), max (q - c + 1) (p + r) < s →
        (((E.obj L).page s hs).X (p, q) ≅ (F L (p + q)).gr p),
      (∀ (L : DerivedCategory.postnikovLowerCategory A c) (s : ℤ)
          (hs : 2 ≤ s) (hs' : 2 ≤ s + 1) (p q : ℤ)
          (hst : max (q - c + 1) (p + r) < s)
          (hst' : max (q - c + 1) (p + r) < s + 1),
        ((E.obj L).page s hs).iCycles (p, q) ≫ (conv L s hs p q hst).hom =
          ((E.obj L).page s hs).homologyπ (p, q) ≫
            ((E.obj L).iso s (s + 1) (p, q) rfl hs).hom ≫
              (conv L (s + 1) hs' p q hst').hom) ∧
      (∀ {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M) (p q : ℤ),
        ((E.map f).hom 2).f (p, q) ≫ (e2 M p q).hom =
          (e2 L p q).hom ≫ (U p).map ((DerivedCategory.singleFunctor A 0).map
            ((DerivedCategory.homologyFunctor A q).map f.hom))) ∧
      (∀ {L M : DerivedCategory.postnikovLowerCategory A c} (f g : L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ),
        ((E.map (f + g)).hom s hs).f (p, q) =
          ((E.map f).hom s hs).f (p, q) + ((E.map g).hom s hs).f (p, q)) ∧
      (∀ (L : DerivedCategory.postnikovLowerCategory A c) (s : ℤ)
          (hs : 2 ≤ s) (p q : ℤ), p < -r ∨ q < c →
        IsZero (((E.obj L).page s hs).X (p, q))) ∧
      (∀ (L : DerivedCategory.postnikovLowerCategory A c) (n : ℤ),
        (F L n).IsFinite ∧ (F L n).IsExhaustive ∧ (F L n).IsSeparated ∧
          (F L n).F (-r) = ⊤ ∧ IsZero ((F L n).F (n - c + 1) : A)) ∧
      (∀ (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M),
        (a n f).hom = (U n).map f.hom) ∧
      (∀ {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ) (hst : max (q - c + 1) (p + r) < s),
        ((E.map f).hom s hs).f (p, q) ≫ (conv M s hs p q hst).hom =
          (conv L s hs p q hst).hom ≫ FilteredObject.gradedMapSteps (a (p + q) f) p) ∧
      (∀ (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c}
          (f g : L ⟶ M) (p : ℤ),
        FilteredObject.restrictionSteps (a n (f + g)) p =
          FilteredObject.restrictionSteps (a n f) p +
            FilteredObject.restrictionSteps (a n g) p) ∧
      (∀ (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c}
          (f g : L ⟶ M) (p : ℤ),
        FilteredObject.gradedMapSteps (a n (f + g)) p =
          FilteredObject.gradedMapSteps (a n f) p +
            FilteredObject.gradedMapSteps (a n g) p) ∧
      (∀ (L : DerivedCategory.postnikovLowerCategory A c) (n p q : ℤ),
        p + q = n → ¬ IsZero (((E.obj L).page 2).X (p, q)) → c ≤ q ∧ q ≤ n + r) ∧
      (∀ (L : DerivedCategory.postnikovLowerCategory A c) (n : ℤ), n < c - r →
        IsZero ((U n).obj L.obj)) := by
  classical
  let T := U 0
  let : T.Additive := hadd 0
  let : T.IsHomological := hhom
  obtain ⟨D, P, ⟨Q⟩, ⟨Z⟩, H, hH⟩ :=
    DerivedCategory.exists_postnikov_additive_exact_couple T
  have hc := DerivedCategory.postnikov_finite_cutoff_abutment T r c hamp
    (fun L ↦ D.couple r L.obj) (fun L ↦ D.dIso r L.obj)
    (fun L ↦ D.eIso r L.obj) (fun L ↦ D.alpha_eq r L.obj)
    (fun L ↦ D.g_eq r L.obj) (fun L ↦ D.f_eq r L.obj)
  obtain ⟨hcut, hnat, hzero, hD, hsupport, hdiag, hstable, lim, ab, hab, α, F₀, hF₀,
    gr₀, hnorm, hα, hconv, htransport, hfinite, htop, hbot, hgr, hlate, hmaps⟩ := hc
  clear hcut hnat hD hab hnorm hα hconv htransport hfinite hgr Z H hH
  let E := ObjectProperty.ι (fun L : DerivedCategory A ↦ L.IsGE c) ⋙ Q.sequence r ⋙
    hyperExtTranslate r
  let η (p q : ℤ) : DerivedCategory.postnikovE T r (p + r) q ≅
      DerivedCategory.homologyFunctor A q ⋙ DerivedCategory.singleFunctor A 0 ⋙ U p :=
    D.initialPageIso r (p + r) q ≪≫
      (by
        simpa only [add_sub_cancel_right, DerivedCategory.postnikovValue, T] using
          Functor.isoWhiskerLeft (DerivedCategory.homologyFunctor A q)
            (Functor.isoWhiskerLeft (DerivedCategory.singleFunctor A 0) (ε p)))
  let e2 (L : DerivedCategory.postnikovLowerCategory A c) (p q : ℤ) :
      ((E.obj L).page 2).X (p, q) ≅
        (U p).obj ((DerivedCategory.singleFunctor A 0).obj
          ((DerivedCategory.homologyFunctor A q).obj L.obj)) :=
    Q.iso r L.obj 0 (p + r) q ≪≫ D.eIso r L.obj (p + r) q ≪≫ (η p q).app L.obj
  have he2 {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M) (p q : ℤ) :
      ((E.map f).hom 2 (by omega)).f (p, q) ≫ (e2 M p q).hom =
        (e2 L p q).hom ≫ (U p).map ((DerivedCategory.singleFunctor A 0).map
          ((DerivedCategory.homologyFunctor A q).map f.hom)) := by
    clear hzero hsupport hdiag hstable lim ab α F₀ hF₀ gr₀ htop hbot hlate hmaps
    change (((Q.sequence r).map f.hom).hom 2 (by omega)).f (p + r, q) ≫
      (Q.iso r M.obj 0 (p + r) q).hom ≫ (D.eIso r M.obj (p + r) q).hom ≫
        (η p q).hom.app M.obj = _
    have hQ : (((Q.sequence r).map f.hom).hom 2 (by omega)).f (p + r, q) ≫
        (Q.iso r M.obj 0 (p + r) q).hom =
      (Q.iso r L.obj 0 (p + r) q).hom ≫ (P.map r 0 f.hom).tE (p + r) q :=
        Q.naturality r f.hom 0 (p + r) q
    calc
      _ = (Q.iso r L.obj 0 (p + r) q).hom ≫ (P.map r 0 f.hom).tE (p + r) q ≫
          (D.eIso r M.obj (p + r) q).hom ≫ (η p q).hom.app M.obj := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ (D.eIso r M.obj (p + r) q).hom ≫ (η p q).hom.app M.obj)
          hQ
      _ = (Q.iso r L.obj 0 (p + r) q).hom ≫ (D.eIso r L.obj (p + r) q).hom ≫
          (DerivedCategory.postnikovE T r (p + r) q).map f.hom ≫
            (η p q).hom.app M.obj := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (Q.iso r L.obj 0 (p + r) q).hom ≫ k ≫ (η p q).hom.app M.obj)
          (P.initialE r f.hom (p + r) q)
      _ = _ := by
        rw [(η p q).hom.naturality]
        simp only [e2, Iso.trans_hom, Iso.app_hom, Category.assoc, Functor.comp_map]
  have haddE {L M : DerivedCategory.postnikovLowerCategory A c} (f g : L ⟶ M)
      (s : ℤ) (hs : 2 ≤ s) (p q : ℤ) :
      ((E.map (f + g)).hom s hs).f (p, q) =
        ((E.map f).hom s hs).f (p, q) + ((E.map g).hom s hs).f (p, q) := by
    clear hzero hsupport hdiag hstable lim ab α F₀ hF₀ gr₀ htop hbot hlate hmaps
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, s = (i : ℤ) + 2 := ⟨(s - 2).toNat, by omega⟩
    change (((Q.sequence r).map (f.hom + g.hom)).hom ((i : ℤ) + 2)).f (p + r, q) = _
    apply (cancel_mono (Q.iso r M.obj i (p + r) q).hom).1
    erw [Preadditive.add_comp, Q.naturality r (f.hom + g.hom) i (p + r) q,
      Q.naturality r f.hom i (p + r) q, Q.naturality r g.hom i (p + r) q]
    rw [P.mapE, P.mapE, P.mapE]
    let := P.additiveE r i (p + r) q
    simp only [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]
  have hsupportE (L : DerivedCategory.postnikovLowerCategory A c) (s : ℤ)
      (hs : 2 ≤ s) (p q : ℤ) (h : p < -r ∨ q < c) :
      IsZero (((E.obj L).page s hs).X (p, q)) := by
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, s = (i : ℤ) + 2 := ⟨(s - 2).toNat, by omega⟩
    exact (Q.iso r L.obj i (p + r) q).isZero_iff.mpr (hsupport L i p q h)
  let F (L : DerivedCategory.postnikovLowerCategory A c) (n : ℤ) :=
    hyperExtFiltration (F₀ L n) ((ε n).app L.obj)
  let stepIso (L : DerivedCategory.postnikovLowerCategory A c) (n p : ℤ) :=
    hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p
  let grIso (L : DerivedCategory.postnikovLowerCategory A c) (n p : ℤ) :=
    hyperExtGrIso (F₀ L n) ((ε n).app L.obj) p
  have hpres (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M) :
      ∀ p : ℤ, ∃ l : ((F L n).F p : A) ⟶ ((F M n).F p : A),
        l ≫ ((F M n).F p).arrow =
          ((F L n).F p).arrow ≫ (U n).map f.hom := by
    obtain ⟨_, l, _, _, _, _, _, hl, _⟩ := hmaps L M f
    intro p
    refine ⟨(stepIso L n p).inv ≫ l n p ≫ (stepIso M n p).hom, ?_⟩
    dsimp only [stepIso]
    calc
      _ = (hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p).inv ≫
          l n p ≫ ((F₀ M n).F p).arrow ≫ ((ε n).app M.obj).hom := by
        simp only [Category.assoc]
        erw [hyperExtStepIso_arrow]
      _ = (hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p).inv ≫
          ((F₀ L n).F p).arrow ≫ (DerivedCategory.postnikovValue T n).map f.hom ≫
            ((ε n).app M.obj).hom := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ (hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p).inv ≫
            k ≫ ((ε n).app M.obj).hom) (hl n p)
      _ = (hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p).inv ≫
          ((F₀ L n).F p).arrow ≫ ((ε n).app L.obj).hom ≫ (U n).map f.hom := by
        simpa only [Category.assoc, T, Iso.app_hom] using congrArg
          (fun k ↦ (hyperExtStepIso (F₀ L n) ((ε n).app L.obj) p).inv ≫
            ((F₀ L n).F p).arrow ≫ k) ((ε n).hom.naturality f.hom)
      _ = _ := by
        rw [← hyperExtStepIso_arrow_assoc (F₀ L n) ((ε n).app L.obj) p]
        simp only [Iso.inv_hom_id_assoc]
        rfl
  let a (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c} (f : L ⟶ M) :
      FilteredObject.Hom ⟨(U n).obj L.obj, F L n⟩
        ⟨(U n).obj M.obj, F M n⟩ :=
    ⟨(U n).map f.hom, hpres n f⟩
  have hstep (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c}
      (f g : L ⟶ M) (p : ℤ) :
      FilteredObject.restrictionSteps (a n (f + g)) p =
        FilteredObject.restrictionSteps (a n f) p +
          FilteredObject.restrictionSteps (a n g) p := by
    apply (cancel_mono ((F M n).F p).arrow).1
    rw [Preadditive.add_comp, hyperExtRestriction_arrow (a n (f + g)) p,
      hyperExtRestriction_arrow (a n f) p, hyperExtRestriction_arrow (a n g) p]
    change ((F L n).F p).arrow ≫ (U n).map (f.hom + g.hom) = _
    let := hadd n
    rw [Functor.map_add, Preadditive.comp_add]
  have hgraded (n : ℤ) {L M : DerivedCategory.postnikovLowerCategory A c}
      (f g : L ⟶ M) (p : ℤ) :
      FilteredObject.gradedMapSteps (a n (f + g)) p =
        FilteredObject.gradedMapSteps (a n f) p + FilteredObject.gradedMapSteps (a n g) p := by
    apply (cancel_epi (cokernel.π (Subobject.ofLE _ _ ((F L n).F_succ_le p)))).1
    rw [Preadditive.comp_add, hyperExtGraded_π (a n (f + g)) p,
      hyperExtGraded_π (a n f) p, hyperExtGraded_π (a n g) p,
      hstep, Preadditive.add_comp]
  have hfiniteF (L : DerivedCategory.postnikovLowerCategory A c) (n : ℤ) :
      (F L n).IsFinite ∧ (F L n).IsExhaustive ∧ (F L n).IsSeparated ∧
        (F L n).F (-r) = ⊤ ∧ IsZero ((F L n).F (n - c + 1) : A) := by
    have ht := hyperExtFiltration_top (F₀ L n) ((ε n).app L.obj) (-r) (htop L n _ le_rfl)
    have hb := hyperExtFiltration_bot (F₀ L n) ((ε n).app L.obj) (n - c + 1)
      (hbot L n _ le_rfl)
    refine ⟨⟨-r, n - c + 1, ht, hb⟩, ?_, ?_, ht, ?_⟩
    · intro X hX
      exact top_unique (ht ▸ hX (-r))
    · intro X hX
      exact bot_unique (hb ▸ hX (n - c + 1))
    · rw [hb]
      exact (isZero_zero A).of_iso Subobject.botCoeIsoZero
  choose zlate vlate hzlate hvlate using hlate
  have hziso (L : DerivedCategory.postnikovLowerCategory A c) (i : ℕ) (p q : ℤ)
      (h : max (q - c + 1) (p + r) < (i : ℤ) + 2) :
      IsIso (zlate L i p q h) := by
    apply hyperExtLate_epi (D.couple r L.obj) (lim L) i (p + r) q _ _ (hzlate L i p q h)
    apply hyperExtLimitCycle_eq
    intro j hj
    exact hstable L j p q (by omega)
  let convNat (L : DerivedCategory.postnikovLowerCategory A c) (i : ℕ)
      (p q : ℤ) (h : max (q - c + 1) (p + r) < (i : ℤ) + 2) :
      ((E.obj L).page ((i : ℤ) + 2) (by omega)).X (p, q) ≅
        (F L (p + q)).gr p :=
    Q.iso r L.obj i (p + r) q ≪≫ vlate L i p q h ≪≫
      gr₀ L p q ≪≫ grIso L (p + q) p
  let conv (L : DerivedCategory.postnikovLowerCategory A c) (s : ℤ) (hs : 2 ≤ s)
      (p q : ℤ) (h : max (q - c + 1) (p + r) < s) :
      ((E.obj L).page s hs).X (p, q) ≅ (F L (p + q)).gr p :=
    hyperExtPageExtend
      (fun t ↦ max (q - c + 1) (p + r) < t.val →
        (((E.obj L).page t.val t.property).X (p, q) ≅ (F L (p + q)).gr p))
      (fun i ↦ convNat L i p q) s hs h
  refine ⟨E, e2, F, a, conv, ?_, he2, haddE, hsupportE, hfiniteF, ?_, ?_, hstep, hgraded,
    ?_, ?_⟩
  · intro L s hs hs' p q h h'
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, s = (i : ℤ) + 2 := ⟨(s - 2).toNat, by omega⟩
    have hi' : max (q - c + 1) (p + r) < ((i + 1 : ℕ) : ℤ) + 2 := by omega
    let := hziso L i p q h
    let := hziso L (i + 1) p q hi'
    have htr := hyperExtLate_transition (D.couple r L.obj) (lim L) i (p + r) q
      (zlate L i p q h) (zlate L (i + 1) p q hi')
      (hzlate L i p q h) (hzlate L (i + 1) p q hi')
      (vlate L i p q h) (vlate L (i + 1) p q hi')
      (hvlate L i p q h) (hvlate L (i + 1) p q hi')
    obtain ⟨k, hk, hπ⟩ := Q.homology r L.obj i (p + r) q
    have hcomp :
        (((Q.sequence r).obj L.obj).page ((i : ℤ) + 2) (by omega)).iCycles (p + r, q) ≫
          (Q.iso r L.obj i (p + r) q).hom ≫ (vlate L i p q h).hom =
        (((Q.sequence r).obj L.obj).page ((i : ℤ) + 2) (by omega)).homologyπ (p + r, q) ≫
          (((Q.sequence r).obj L.obj).iso ((i : ℤ) + 2) ((i + 1 : ℕ) + (2 : ℤ))
            (p + r, q) (by omega) (by omega)).hom ≫ (Q.iso r L.obj (i + 1) (p + r) q).hom ≫
              (vlate L (i + 1) p q hi').hom := by
      calc
        _ = k.hom ≫ kernel.ι _ ≫ (vlate L i p q h).hom := by
          simpa only [Category.assoc] using congrArg
            (fun f ↦ f ≫ (vlate L i p q h).hom) hk.symm
        _ = k.hom ≫ (D.couple r L.obj |>.pageCouple i).derivedEProjection
            (p + r) q ≫ (vlate L (i + 1) p q hi').hom := by rw [htr]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun f ↦ f ≫ (vlate L (i + 1) p q hi').hom) hπ
    suffices htransition : ∀ (t : ℤ) (e : (i : ℤ) + 2 + 1 = t)
        (ht : 2 ≤ t) (ht' : max (q - c + 1) (p + r) < t),
        ((E.obj L).page ((i : ℤ) + 2) hs).iCycles (p, q) ≫
            (conv L ((i : ℤ) + 2) hs p q h).hom =
          ((E.obj L).page ((i : ℤ) + 2) hs).homologyπ (p, q) ≫
            ((E.obj L).iso ((i : ℤ) + 2) t (p, q) e hs).hom ≫
              (conv L t ht p q ht').hom by
      exact htransition ((i : ℤ) + 2 + 1) rfl hs' h'
    intro t e ht ht'
    have heq : t = ((i + 1 : ℕ) : ℤ) + 2 := by omega
    revert e ht ht'
    rw [heq]
    intro e ht ht'
    have hraw := hyperExtRestriction_square r ((i : ℤ) + 2)
      (((Q.sequence r).obj L.obj).page ((i : ℤ) + 2) hs) (p, q)
      ((Q.iso r L.obj i (p + r) q).hom ≫ (vlate L i p q h).hom ≫
        (gr₀ L p q).hom ≫ (grIso L (p + q) p).hom)
      ((((Q.sequence r).obj L.obj).iso ((i : ℤ) + 2) (((i + 1 : ℕ) : ℤ) + 2)
        (p + r, q) e hs |>.hom) ≫ (Q.iso r L.obj (i + 1) (p + r) q).hom ≫
          (vlate L (i + 1) p q hi').hom ≫ (gr₀ L p q).hom ≫
            (grIso L (p + q) p).hom)
      (by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ (gr₀ L p q).hom ≫ (grIso L (p + q) p).hom) hcomp)
    dsimp only [E, Functor.comp_obj, hyperExtTranslate]
    simpa only [conv, hyperExtPageExtend_nat, convNat, ObjectProperty.ι_obj, F,
      Iso.trans_hom, Category.assoc] using hraw
  · intro n L M f
    rfl
  · intro L M f s hs p q h
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, s = (i : ℤ) + 2 := ⟨(s - 2).toNat, by omega⟩
    obtain ⟨_, lift, gr, z, tInf, _, _, hl, hg, hz, hv, hgg⟩ := hmaps L M f
    have hn := hyperExtTower_natural (D.couple r L.obj) (D.couple r M.obj)
      (fun p q ↦ (P.map r 0 f.hom).tE p q)
      (fun j p q ↦ (P.map r j f.hom).tE p q) (by intros; rfl)
      (by
        intro j p q
        dsimp [BigradedExactCouple.d]
        rw [← Category.assoc, (P.map r j f.hom).f_comm, Category.assoc,
          (P.map r j f.hom).g_comm, Category.assoc])
      (fun j p q ↦ P.homology_square r j f.hom p q)
    have ht0 : (P.map r 0 f.hom).tE (p + r) q =
        (D.eIso r L.obj (p + r) q).hom ≫
          (DerivedCategory.postnikovE T r (p + r) q).map f.hom ≫
            (D.eIso r M.obj (p + r) q).inv := by
      simpa only [Category.assoc] using
        (Iso.eq_comp_inv (D.eIso r M.obj (p + r) q)).mpr
        (P.initialE r f.hom (p + r) q)
    have hzn := hz p q
    rw [← ht0] at hzn
    let := hziso L i p q h
    have hvn := hyperExtLate_natural (D.couple r L.obj) (D.couple r M.obj)
      (lim L) (lim M) i (p + r) q (P.map r 0 f.hom |>.tE (p + r) q)
      ((P.map r i f.hom).tE (p + r) q)
      (zlate L i p q h) (zlate M i p q h)
      (hzlate L i p q h) (hzlate M i p q h)
      (vlate L i p q h) (vlate M i p q h)
      (hvlate L i p q h) (hvlate M i p q h)
      (z p q) (tInf p q) hzn (hv p q) (hn i (p + r) q)
    have hgn := hyperExtGrIso_natural (F₀ L (p + q)) (F₀ M (p + q))
      ((ε (p + q)).app L.obj) ((ε (p + q)).app M.obj)
      ((DerivedCategory.postnikovValue T (p + q)).map f.hom)
      ((U (p + q)).map f.hom) ((ε (p + q)).hom.naturality f.hom)
      (a (p + q) f) rfl p (lift (p + q) p) (hl (p + q) p) (gr p q) (hg p q)
    simp only [conv, hyperExtPageExtend_nat, convNat, Iso.trans_hom, Category.assoc]
    change (((Q.sequence r).map f.hom).hom ((i : ℤ) + 2) hs).f (p + r, q) ≫
        (Q.iso r M.obj i (p + r) q).hom ≫ (vlate M i p q h).hom ≫
          (gr₀ M p q).hom ≫ (grIso M (p + q) p).hom =
      (Q.iso r L.obj i (p + r) q).hom ≫ (vlate L i p q h).hom ≫
        (gr₀ L p q).hom ≫ (grIso L (p + q) p).hom ≫
          FilteredObject.gradedMapSteps (a (p + q) f) p
    rw [← Category.assoc, Q.naturality, Category.assoc,
      ← Category.assoc ((P.map r i f.hom).tE (p + r) q), hvn, Category.assoc,
      ← Category.assoc (tInf p q), ← hgg p q, Category.assoc, ← hgn]
  · intro L n p q hn hnz
    apply hdiag L 0 n p q hn
    intro hz
    exact hnz ((Q.iso r L.obj 0 (p + r) q).isZero_iff.mpr hz)
  · intro L n hn
    exact ((ε n).app L.obj).isZero_iff.mp (hzero L n hn)



variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max uC vC u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC u}]
  (R : Sheaf J CommRingCat.{max uC vC u})
  [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
    CommRingCat.{max uC vC u}
    RingCat.{max uC vC u})).obj R))]

/-- The functor T^n(M) = H^n RHom(K,M), with its actual derived morphism maps.
Source: Stacks Tags 0A94, 0A95; the internal-Hom version of Tag 015W.
(blueprint: lem-per-bounded-above-rhom-hyperext). -/
noncomputable abbrev ringedSiteRHomCohomology (K : DerivedCategory (ringedSiteModules.{max uC vC u}
  ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) (n : ℤ) :
    DerivedCategory (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC
      vC u}
      RingCat.{max uC vC u})).obj R)) ⥤ (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{uC, vC, u, w} J R)).obj (op K) ⋙
    DerivedCategory.homologyFunctor _ n

/-- Sheaf Ext^p(K,F) is H^p RHom(K,F[0]), for every integer p.
Source: the internal-Hom/Postnikov variant of Stacks Tag 015W, using Tags 0A94 and 0A95.
(blueprint: lem-per-bounded-above-rhom-hyperext). -/
noncomputable abbrev ringedSiteHyperExt (K : DerivedCategory (ringedSiteModules.{max uC vC u}
  ((sheafCompose J
  (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) (p : ℤ) :
    (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) ⥤
      (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
        RingCat.{max uC vC u})).obj R)) :=
  DerivedCategory.singleFunctor _ 0 ⋙ ringedSiteRHomCohomology.{uC, vC, u, w} J R K p

set_option maxHeartbeats 800000 in
-- Extract only the cohomological functor data from the large local comparison.
private theorem hyperExtRHomData
    (K : LocalRHom.D.{uC, vC, u, w} J R) (r : ℤ) (hK : K.IsLE r) :
    (∀ n : ℤ, (ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).Additive) ∧
      (ringedSiteRHomCohomology.{uC, vC, u, w} J R K 0).IsHomological ∧
      ∃ _ε : ∀ n : ℤ,
        DerivedCategory.postnikovValue (ringedSiteRHomCohomology.{uC, vC, u, w} J R K 0) n ≅
          ringedSiteRHomCohomology.{uC, vC, u, w} J R K n,
        ∀ (b n : ℤ) (M : LocalRHom.D.{uC, vC, u, w} J R), M.IsGE b → n < b - r →
          IsZero ((DerivedCategory.postnikovValue
            (ringedSiteRHomCohomology.{uC, vC, u, w} J R K 0) n).obj M) := by
  classical
  let A := LocalRHom.Mod.{uC, vC, u} J R
  let T := ringedSiteRHomCohomology.{uC, vC, u, w} J R K 0
  let (U : C) : HasSheafify (J.over U) AddCommGrpCat.{max uC vC u} :=
    SheafOfModules.hasSheafify_coefficientUniverse
  let (U : C) : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max uC vC u} :=
    SheafOfModules.wEqualsLocallyBijective_coefficientUniverse
  let (U : C) : HasDerivedCategory.{(max uC vC u) + 1}
      (SheafOfModules.{max uC vC u} ((LocalRHom.rings.{uC, vC, u} J R).over U)) :=
    HasDerivedCategory.standard _
  obtain ⟨P₀, e₀, σ, S, τ, hτ, hadd, hhom, hrest⟩ :=
    LocalRHom.local_cohomological_bound.{uC, vC, u, w, (max uC vC u) + 1} J R K
  let : T.Additive := hadd 0
  let : T.IsHomological := hhom
  let : T.ShiftSequence ℤ := S
  let ε (n : ℤ) : DerivedCategory.postnikovValue T n ≅
      ringedSiteRHomCohomology.{uC, vC, u, w} J R K n :=
    T.isoShift n ≪≫ τ n
  have hamp : ∀ (b n : ℤ) (M : DerivedCategory A), M.IsGE b → n < b - r →
      IsZero ((DerivedCategory.postnikovValue T n).obj M) := by
    intro b n M hb hn
    exact ((ε n).app M).isZero_iff.mpr (hrest.2.2.2.2.2 r b n M hK hb hn)
  clear hrest hτ σ e₀ P₀
  exact ⟨hadd, hhom, ε, hamp⟩

set_option linter.unusedVariables false in
-- The general-universe local RHom comparison has a large dependent witness type.
/-- A bounded-above source and a bounded-below target give the finite-diagonal
internal hyper-Ext spectral sequence, naturally and additively in the target.
Here E is a functor on the full subcategory D^{>=c}; e2 is the natural E2 identification;
a is the actual cohomology map as a filtered morphism. The isomorphisms conv identify
any sufficiently late page with the graded piece, and their squares identify its maps.

Source: Stacks Tag 015W (method), Tags 0A94, 0A95, 03EI, 08J5, 011R, 011T and 012U;
ILO XVII 10.1.1, proof p. 325 (the Ext-to-representable-sums passage).
(blueprint: lem-per-bounded-above-rhom-hyperext).

Proof:
1. Resolve the second argument by a K-injective complex. The local calculation
   lem-pur-rhom-into-kinjective-local, applied to the source shifted by -n, identifies
   T^n(M) with the sheafification of U |-> Hom(K|U,M|U[n]). The signed Hom-complex
   shift formula and exact module sheafification (Tag 03EI) give this identification
   naturally and additively in M and under restriction.
2. Exact restriction (lem-pur-site-restriction-module-adjunction-exact) preserves
   cohomology. Standard t-structure orthogonality gives T^n(M)=0 for n<b-r when
   M>=b. In particular Ext^p(K,F)=0 for p<-r and T^n(L)=0 for n<c-r.
3. Restrict a distinguished triangle to each localized site, apply the representable
   Hom exact sequence (lem-weil-pbc-hom-into-triangle-exact), and sheafify exactly.
   The boundary is postcomposition with the shifted third arrow; the last square of
   a triangle morphism proves its naturality. This makes the T^n a cohomological functor.
4. Apply T to the successive functorial Postnikov triangles
   tau<=q-1 L -> tau<=q L -> H^q(L)[-q] ->.
   By lem-weil-pbc-truncation-triangle their long exact sequences give the exact couple
   D^{p,q}=T^{p+q}(tau<=q L), E^{p,q}=T^{p+q}(H^q(L)[-q]), with alpha of degree
   (-1,1), f of degree (2,-1), and g of degree (0,0).
   Lem-sp-derived-couple-exact constructs its pages with d_s of degree (s,1-s).
5. Lem-pur-derived-internal-hom-shift-right identifies E2 with Ext^p(K,H^q L).
   Step 2 gives p>=-r and q>=c support, and D=0 for q<c. Subquotients preserve support.
6. Reindex by P=p+r. Thm-sp-half-plane-convergence applies with lower row c.
   The stable pages have s>max(q-c+1,p+r); total degree n has c<=q<=n+r.
   Its initial abutment is T^n(tau<=n+r L).
7. The tail tau>=n+r+1 L has T^{n-1}=T^n=0 by Step 2. The truncation triangle
   (lem-sf-derived-truncation-triangle) and Step 3 identify this initial abutment
   isomorphically with T^n(L), naturally in L, also when n+r<c.
8. Transport the image filtration to T^n(L). Its p-step is the image of
   T^n(tau<=n-p L) -> T^n(L). The tail argument gives F^{-r}=top, and q<c gives
   F^{n-c+1}=bottom. The half-plane theorem supplies the graded identifications.
   These finite bounds imply exhaustiveness, separatedness and completeness.
9. Functorial truncation triangles and the natural boundaries give couple morphisms.
   Lem-sp-couple-morphism gives compatible maps on pages, abutments and graded pieces.
   The abutment map is T^n(u) by Step 7. Truncation and local postcomposition are
   additive. Induction through kernels, images and quotients gives additivity on
   every page; uniqueness through the monic filtration inclusions gives additivity
   of step maps, and then of graded maps. The same uniqueness gives identities and
   composition. This proves all stated functorialities without dimension or Tor bounds. -/
theorem exists_boundedAbove_rhom_hyperExt
    (K : DerivedCategory (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂ CommRingCat.{max
      uC vC u}
      RingCat.{max uC vC u})).obj R))) (r c : ℤ) (_hK : K.IsLE r) :
    ∃ E : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC u}
      ((sheafCompose J (forget₂ CommRingCat.{max uC vC u}
      RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c)) ⥤
      E₂CohomologicalSpectralSequence (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)),
    ∃ e2 : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max
      uC vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (p q :
      ℤ),
      ((E.obj L).page 2).X (p, q) ≅
        (ringedSiteHyperExt.{uC, vC, u, w} J R K p).obj ((DerivedCategory.homologyFunctor _ q).obj
          L.obj),
    ∃ F : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
      vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
      ℤ),
      DecreasingFiltration ((ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj),
    ∃ a : ∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
      (ringedSiteModules.{max uC vC u} ((sheafCompose J
      (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f : L ⟶ M),
      FilteredObject.Hom
        ⟨(ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj, F L n⟩
        ⟨(ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj M.obj, F M n⟩,
    ∃ conv : ∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max
      uC vC u}
      ((sheafCompose J (forget₂
      CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (s : ℤ)
      (hs : 2 ≤ s) (p q : ℤ),
      max (q - c + 1) (p + r) < s →
        (((E.obj L).page s hs).X (p, q) ≅ (F L (p + q)).gr p),
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE
          c))) (s : ℤ) (hs : 2 ≤ s)
          (hs' : 2 ≤ s + 1) (p q : ℤ)
          (hst : max (q - c + 1) (p + r) < s)
          (hst' : max (q - c + 1) (p + r) < s + 1),
        ((E.obj L).page s hs).iCycles (p, q) ≫ (conv L s hs p q hst).hom =
          ((E.obj L).page s hs).homologyπ (p, q) ≫
            ((E.obj L).iso s (s + 1) (p, q) rfl hs).hom ≫
              (conv L (s + 1) hs' p q hst').hom) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M) (p q : ℤ),
        ((E.map f).hom 2).f (p, q) ≫ (e2 M p q).hom =
          (e2 L p q).hom ≫ (ringedSiteHyperExt.{uC, vC, u, w} J R K p).map
            ((DerivedCategory.homologyFunctor _ q).map f.hom)) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ),
        ((E.map (f + g)).hom s hs).f (p, q) =
          ((E.map f).hom s hs).f (p, q) + ((E.map g).hom s hs).f (p, q)) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (s :
        ℤ) (hs : 2 ≤ s) (p q : ℤ),
        p < -r ∨ q < c → IsZero (((E.obj L).page s hs).X (p, q))) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
        ℤ),
        (F L n).IsFinite ∧ (F L n).IsExhaustive ∧ (F L n).IsSeparated ∧
          (F L n).F (-r) = ⊤ ∧ IsZero ((F L n).F (n - c + 1) : ringedSiteModules.{max uC vC u}
            ((sheafCompose J (forget₂ CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R))) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M),
        (a n f).hom = (ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).map f.hom) ∧
      (∀ {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC
        vC u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f :
        L ⟶ M)
          (s : ℤ) (hs : 2 ≤ s) (p q : ℤ) (hst : max (q - c + 1) (p + r) < s),
        ((E.map f).hom s hs).f (p, q) ≫ (conv M s hs p q hst).hom =
          (conv L s hs p q hst).hom ≫ FilteredObject.gradedMapSteps (a (p + q) f) p) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M) (p : ℤ),
        FilteredObject.restrictionSteps (a n (f + g)) p =
          FilteredObject.restrictionSteps (a n f) p +
            FilteredObject.restrictionSteps (a n g) p) ∧
      (∀ (n : ℤ) {L M : (ObjectProperty.FullSubcategory (fun L : DerivedCategory
        (ringedSiteModules.{max uC vC u} ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))} (f g
        : L ⟶ M) (p : ℤ),
        FilteredObject.gradedMapSteps (a n (f + g)) p =
          FilteredObject.gradedMapSteps (a n f) p +
            FilteredObject.gradedMapSteps (a n g) p) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n p
        q : ℤ),
        p + q = n → ¬ IsZero (((E.obj L).page 2).X (p, q)) → c ≤ q ∧ q ≤ n + r) ∧
      (∀ (L : (ObjectProperty.FullSubcategory (fun L : DerivedCategory (ringedSiteModules.{max uC vC
        u}
        ((sheafCompose J (forget₂
        CommRingCat.{max uC vC u} RingCat.{max uC vC u})).obj R)) ↦ L.IsGE c))) (n :
        ℤ), n < c - r →
        IsZero ((ringedSiteRHomCohomology.{uC, vC, u, w} J R K n).obj L.obj)) := by
  obtain ⟨hadd, hhom, ε, hamp⟩ := hyperExtRHomData.{uC, vC, u, w} J R K r _hK
  exact hyperExtFromPostnikov
    (fun n ↦ ringedSiteRHomCohomology.{uC, vC, u, w} J R K n) r c hadd hhom ε hamp

end CategoryTheory
