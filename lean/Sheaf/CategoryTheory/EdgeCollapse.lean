/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru
import WeilConjectures.CategoryTheory.Abelian.Filtration
import WeilConjectures.CategoryTheory.ExactCouple

/-!
# Edge collapse and edge maps

Source: blueprint node `lem-sp-edge-collapse` (blueprint: lem-sp-edge-collapse).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

-- A zero term stays zero because each next page is a subquotient of it.
private theorem edge_page_zero (X : BigradedExactCouple C 0) (R : ℕ)
    (h : ∀ p q : ℤ, p ≠ 0 → IsZero ((X.pageCouple R).E p q))
    (r : ℕ) (hr : R ≤ r) (p q : ℤ) (hp : p ≠ 0) :
    IsZero ((X.pageCouple r).E p q) := by
  induction r, hr using Nat.le_induction with
  | base => exact h p q hp
  | succ r hr ih =>
    have : Epi ((X.pageCouple r).derivedEProjection p q) := by
      dsimp [derivedEProjection, derivedE]
      infer_instance
    exact IsZero.of_epi ((X.pageCouple r).derivedEProjection p q)
      (IsZero.of_mono (kernel.ι ((X.pageCouple r).d p q)) ih)

private theorem edge_d_zero (X : BigradedExactCouple C 0) (R : ℕ)
    (h : ∀ p q : ℤ, p ≠ 0 → IsZero ((X.pageCouple R).E p q))
    (r : ℕ) (hr : R ≤ r) (p q : ℤ) : (X.pageCouple r).d p q = 0 := by
  by_cases hp : p = 0
  · exact (edge_page_zero X R h r hr _ _ (by omega)).eq_zero_of_tgt _
  · exact (edge_page_zero X R h r hr p q hp).eq_zero_of_src _

private theorem edge_pullback_bot {U V : C} (f : U ⟶ V) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (Subobject.factors_pullback_obj_iff f (⊥ : Subobject V) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    obtain ⟨t, ht⟩ := (Subobject.factors_iff _ _).mp hf
    rw [← ht]
    have hz : (⊥ : Subobject V).arrow = 0 :=
      (Subobject.botCoeIsoZero.isZero_iff.mpr (isZero_zero C)).eq_zero_of_src _
    change t ≫ (⊥ : Subobject V).arrow = 0
    rw [hz, comp_zero]
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    rw [kernelSubobject_arrow_comp]
    exact Subobject.factors_zero

private theorem edge_tower_step (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ)
    (hout : (X.pageCouple r).d p q = 0)
    (hin : (X.pageCouple r).dInto p q = 0) :
    X.cycleBoundaryTower.Z (r + 1) p q = X.cycleBoundaryTower.Z r p q ∧
      X.cycleBoundaryTower.B (r + 1) p q = X.cycleBoundaryTower.B r p q := by
  let T := X.cycleBoundaryTower
  constructor
  · rw [T.Z_succ, hout, kernelSubobject_zero, Subobject.pullback_top,
      Subobject.exists_iso_map, Subobject.map_top, Subobject.mk_arrow]
  · rw [T.B_succ, hin, imageSubobject_zero, edge_pullback_bot, T.projection_kernel,
      Subobject.exists_iso_map, Subobject.map_mk]
    simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
    rfl

-- Two epimorphisms with the same kernel present the same quotient, canonically.
private theorem edge_quotient_comparison {S P : C} (B Z : Subobject S) (h : B ≤ Z)
    (π : (Z : C) ⟶ P) [Epi π]
    (hk : kernelSubobject π = Subobject.mk (Subobject.ofLE B Z h)) :
    ∃ e : cokernel (Subobject.ofLE B Z h) ≅ P,
      cokernel.π (Subobject.ofLE B Z h) ≫ e.hom = π := by
  let k := Subobject.ofLE B Z h
  have hz : k ≫ π = 0 := by
    apply (kernelSubobject_factors_iff π k).mp
    rw [hk]
    exact Subobject.mk_factors_self k
  have hw : kernel.ι π ≫ cokernel.π k = 0 := by
    have hfac : (Subobject.mk k).Factors (kernel.ι π) := by
      rw [← hk]
      exact kernelSubobject_factors π _ (kernel.condition π)
    obtain ⟨t, ht⟩ := (Subobject.mk_factors_iff k _).mp hfac
    change t ≫ k = kernel.ι π at ht
    rw [← ht, Category.assoc, cokernel.condition, comp_zero]
  let e : cokernel k ≅ P :=
    { hom := cokernel.desc k π hz
      inv := Abelian.epiDesc π (cokernel.π k) hw
      hom_inv_id := by
        apply (cancel_epi (cokernel.π k)).mp
        simp
      inv_hom_id := by
        apply (cancel_epi π).mp
        simp }
  exact ⟨e, cokernel.π_desc k π hz⟩

private theorem edge_stabilized_comparison {S P : C}
    (B Z B' Z' : Subobject S) (hB : B = B') (hZ : Z = Z')
    (h : B ≤ Z) (h' : B' ≤ Z') (hle : Z ≤ Z')
    (π : (Z' : C) ⟶ P) [Epi π]
    (hk : kernelSubobject π = Subobject.mk (Subobject.ofLE B' Z' h')) :
    ∃ e : cokernel (Subobject.ofLE B Z h) ≅ P,
      cokernel.π (Subobject.ofLE B Z h) ≫ e.hom = Subobject.ofLE Z Z' hle ≫ π := by
  subst B'
  subst Z'
  simpa only [Subobject.ofLE_refl, Category.id_comp] using
    edge_quotient_comparison B Z h π hk

private theorem edge_filtration_step {T : C} (F : PBCDecreasingFiltration T)
    (p : ℤ) (hz : IsZero (F.gradedPiece p)) : F.step (p + 1) = F.step p := by
  let f := Subobject.ofLE _ _ (F.antitone_step (show p ≤ p + 1 by omega))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hz
  have : IsIso f := isIso_of_mono_of_epi f
  exact Subobject.eq_of_comm (asIso f) (Subobject.ofLE_arrow _)

/-- (blueprint: lem-sp-edge-collapse) If a convergent exact-couple spectral sequence
    is concentrated in one column
from page `r₀` onward, then all later differentials vanish, the pages are
stationary, and the edge map is an isomorphism.

Source: blueprint node `lem-sp-edge-collapse`.
Proof: the bidegree of each differential forces both its source and target
outside the surviving column, so all differentials vanish.  The cycle and
boundary descriptions in the convergence data then identify every later page
with the initial one at `r₀` and identify the limiting page with it.  The
finite exhaustive separated filtration has only its zeroth graded piece, so
its canonical edge map is an isomorphism. -/
theorem edge_collapse
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0)
    (L : X.LimitSubobjects)
    (A : ∀ n : ℤ, X.AlphaColimit n)
    (hconv : X.ConvergesTo L A)
    (hfinite : ∀ n : ℤ, (X.imageFiltration n (A n)).IsFinite)
    (r₀ : ℕ) (hr₀ : 2 ≤ r₀)
    (hvanish : ∀ (p q : ℤ), p ≠ 0 → IsZero (X.page r₀ p q)) :
    (∀ (r : ℕ), r₀ ≤ r → ∀ (p q : ℤ),
      X.pageDifferential r p q = 0) ∧
      (∀ (r : ℕ), r₀ ≤ r → ∀ (p q : ℤ),
        ∃ (e : X.page r₀ p q ≅ X.page r p q)
          (i : (X.cycleBoundaryTower.Z (r₀ - 2) p q : C) ⟶
            (X.cycleBoundaryTower.Z (r - 2) p q : C)),
          i ≫ (X.cycleBoundaryTower.Z (r - 2) p q).arrow =
            (X.cycleBoundaryTower.Z (r₀ - 2) p q).arrow ∧
          X.cycleBoundaryTower.projection (r₀ - 2) p q ≫ e.hom =
            i ≫ X.cycleBoundaryTower.projection (r - 2) p q) ∧
      (∃ t : ∀ (p q : ℤ), X.pageInfinity L p q ≅ X.page r₀ p q,
        (∀ (p q : ℤ),
          ∃ i : (L.Z p q : C) ⟶ (X.cycleBoundaryTower.Z (r₀ - 2) p q : C),
            i ≫ (X.cycleBoundaryTower.Z (r₀ - 2) p q).arrow = (L.Z p q).arrow ∧
            cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
              (X.limitBoundary_le_cycle L p q)) ≫ (t p q).hom =
                i ≫ X.cycleBoundaryTower.projection (r₀ - 2) p q) ∧
        (∀ n : ℤ, ∃ e : (A n).obj ≅ X.page r₀ 0 n,
          eqToHom (by simp) ≫ (A n).ι 0 ≫ e.hom =
            X.toPageInfinity L 0 n ≫ (t 0 n).hom)) := by
  classical
  let R := r₀ - 2
  let T := X.cycleBoundaryTower
  have hzero : ∀ p q : ℤ, p ≠ 0 → IsZero ((X.pageCouple R).E p q) := hvanish
  have hd (r : ℕ) (hr : R ≤ r) (p q : ℤ) : (X.pageCouple r).d p q = 0 :=
    edge_d_zero X R hzero r hr p q
  have hin (r : ℕ) (hr : R ≤ r) (p q : ℤ) : (X.pageCouple r).dInto p q = 0 := by
    simp only [dInto, hd r hr, zero_comp]
  have hs (r : ℕ) (hr : R ≤ r) (p q : ℤ) :
      T.Z (r + 1) p q = T.Z r p q ∧ T.B (r + 1) p q = T.B r p q :=
    edge_tower_step X r p q (hd r hr p q) (hin r hr p q)
  have htail (r : ℕ) (hr : R ≤ r) (p q : ℤ) :
      T.Z r p q = T.Z R p q ∧ T.B r p q = T.B R p q := by
    induction r, hr using Nat.le_induction with
    | base => exact ⟨rfl, rfl⟩
    | succ r hr ih => exact ⟨(hs r hr p q).1.trans ih.1, (hs r hr p q).2.trans ih.2⟩
  have hlimits (p q : ℤ) : L.Z p q = T.Z R p q ∧ L.B p q = T.B R p q := by
    constructor
    · apply le_antisymm ((L.Z_glb p q).1 ⟨R, rfl⟩)
      apply (L.Z_glb p q).2
      rintro _ ⟨r, rfl⟩
      by_cases hr : R ≤ r
      · exact (htail r hr p q).1.ge
      · exact antitone_nat_of_succ_le (f := fun s ↦ T.Z s p q)
          (fun s ↦ T.Z_decreasing s p q) (by omega)
    · apply le_antisymm
      · apply (L.B_lub p q).2
        rintro _ ⟨r, rfl⟩
        by_cases hr : R ≤ r
        · exact (htail r hr p q).2.le
        · exact monotone_nat_of_le_succ (f := fun s ↦ T.B s p q)
            (fun s ↦ T.B_increasing s p q) (by omega)
      · exact (L.B_lub p q).1 ⟨R, rfl⟩
  have hfinitePages (r : ℕ) (hr : R ≤ r) (p q : ℤ) :
      ∃ (e : (X.pageCouple R).E p q ≅ (X.pageCouple r).E p q)
        (i : (T.Z R p q : C) ⟶ (T.Z r p q : C)),
        i ≫ (T.Z r p q).arrow = (T.Z R p q).arrow ∧
        T.projection R p q ≫ e.hom = i ≫ T.projection r p q := by
    have : Epi (T.projection R p q) := T.projection_epi R p q
    have : Epi (T.projection r p q) := T.projection_epi r p q
    obtain ⟨e₀, he₀⟩ := edge_quotient_comparison (T.B R p q) (T.Z R p q)
      (T.B_le_Z R p q) (T.projection R p q) (T.projection_kernel R p q)
    have hZ : T.Z R p q ≤ T.Z r p q := (htail r hr p q).1.ge
    obtain ⟨e₁, he₁⟩ := edge_stabilized_comparison
      (T.B R p q) (T.Z R p q) (T.B r p q) (T.Z r p q)
      (htail r hr p q).2.symm (htail r hr p q).1.symm
      (T.B_le_Z R p q) (T.B_le_Z r p q) hZ
      (T.projection r p q) (T.projection_kernel r p q)
    refine ⟨e₀.symm ≪≫ e₁, Subobject.ofLE _ _ hZ, Subobject.ofLE_arrow _, ?_⟩
    simp only [Iso.trans_hom, Iso.symm_hom]
    rw [← he₀, Category.assoc, ← Category.assoc e₀.hom, Iso.hom_inv_id,
      Category.id_comp, he₁]
  have hinfinity (p q : ℤ) :
      ∃ e : X.pageInfinity L p q ≅ (X.pageCouple R).E p q,
      ∃ i : (L.Z p q : C) ⟶ (T.Z R p q : C),
        i ≫ (T.Z R p q).arrow = (L.Z p q).arrow ∧
        cokernel.π (Subobject.ofLE (L.B p q) (L.Z p q)
          (X.limitBoundary_le_cycle L p q)) ≫ e.hom = i ≫ T.projection R p q := by
    have : Epi (T.projection R p q) := T.projection_epi R p q
    have hZ : L.Z p q ≤ T.Z R p q := (hlimits p q).1.le
    obtain ⟨e, he⟩ := edge_stabilized_comparison
      (L.B p q) (L.Z p q) (T.B R p q) (T.Z R p q)
      (hlimits p q).2 (hlimits p q).1
      (X.limitBoundary_le_cycle L p q) (T.B_le_Z R p q) hZ
      (T.projection R p q) (T.projection_kernel R p q)
    exact ⟨e, Subobject.ofLE _ _ hZ, Subobject.ofLE_arrow _, he⟩
  choose t ht using hinfinity
  refine ⟨?_, ?_, t, ht, ?_⟩
  · intro r hr p q
    exact hd (r - 2) (by dsimp [R]; omega) p q
  · intro r hr p q
    exact hfinitePages (r - 2) (by dsimp [R]; omega) p q
  · intro n
    let F := X.imageFiltration n (A n)
    have hgr (p : ℤ) (hp : p ≠ 0) : IsZero (F.gradedPiece p) := by
      obtain ⟨e, _, _⟩ := X.weakConvergence_comparison L A hconv.2.1.1 p (n - p)
      have hz : IsZero (X.pageInfinity L p (n - p)) :=
        (hvanish p (n - p) hp).of_iso (t p (n - p))
      have hz' := hz.of_iso e.symm
      rw [show p + (n - p) = n by omega] at hz'
      exact hz'
    have hstep (p : ℤ) (hp : p ≠ 0) : F.step (p + 1) = F.step p :=
      edge_filtration_step F p (hgr p hp)
    have hhead (k : ℕ) : F.step (-(k : ℤ)) = F.step 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [← hstep (-((k + 1 : ℕ) : ℤ)) (by omega),
          show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by omega]
        exact ih
    have htailF (k : ℕ) : F.step (1 + k) = F.step 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [show (1 : ℤ) + (k + 1 : ℕ) = (1 + k) + 1 by omega,
          hstep (1 + k) (by omega)]
        exact ih
    obtain ⟨lo, hi, hlo, hhi⟩ := hfinite n
    have htop : F.step 0 = ⊤ := by
      by_cases hp : 0 ≤ lo
      · apply top_unique
        rw [← hlo]
        exact F.antitone_step hp
      · have hh : F.step lo = F.step 0 := by
          simpa only [show -(((-lo).toNat : ℕ) : ℤ) = lo by omega] using hhead (-lo).toNat
        exact hh.symm.trans hlo
    have hbot : F.step 1 = ⊥ := by
      by_cases hp : hi ≤ 1
      · apply bot_unique
        rw [← hhi]
        exact F.antitone_step hp
      · have hh : F.step hi = F.step 1 := by
          simpa only [show (1 : ℤ) + ((hi - 1).toNat : ℕ) = hi by omega]
            using htailF (hi - 1).toNat
        exact hh.symm.trans hhi
    have ha : IsIso (F.step 0).arrow := (Subobject.isIso_arrow_iff_eq_top _).mpr htop
    let k := Subobject.ofLE (F.step (0 + 1)) (F.step 0)
      (F.antitone_step (show (0 : ℤ) ≤ 0 + 1 by omega))
    have hk : k = 0 := by
      apply (cancel_mono (F.step 0).arrow).mp
      rw [zero_comp]
      change Subobject.ofLE _ _ _ ≫ _ = _
      rw [Subobject.ofLE_arrow]
      exact Subobject.mk_eq_bot_iff_zero.mp (by simpa using hbot)
    have hπ : IsIso (cokernel.π k) := cokernel.π_of_zero hk
    let a : (A n).obj ≅ F.gradedPiece 0 := (asIso (F.step 0).arrow).symm ≪≫
      asIso (cokernel.π k)
    have he : ∃ e : X.pageInfinity L 0 n ≅ F.gradedPiece 0,
        X.toPageInfinity L 0 n ≫ e.hom =
          eqToHom (by simp) ≫ factorThruImageSubobject ((A n).ι 0) ≫ cokernel.π k := by
      have hm : ∀ (m : ℤ) (hm : 0 + n = m),
          ∃ e : X.pageInfinity L 0 n ≅ (X.imageFiltration m (A m)).gradedPiece 0,
          X.toPageInfinity L 0 n ≫ e.hom =
            eqToHom (by congr 1; omega) ≫ factorThruImageSubobject ((A m).ι 0) ≫
              cokernel.π (Subobject.ofLE _ _
                ((X.imageFiltration m (A m)).antitone_step (by omega))) := by
        intro m hm
        subst m
        exact (X.weakConvergence_comparison L A hconv.2.1.1 0 n).exists
      exact hm n (zero_add n)
    obtain ⟨e, he⟩ := he
    refine ⟨a ≪≫ e.symm ≪≫ t 0 n, ?_⟩
    have ha_comm : (A n).ι 0 ≫ a.hom =
        factorThruImageSubobject ((A n).ι 0) ≫ cokernel.π k := by
      change (A n).ι 0 ≫ (inv (F.step 0).arrow ≫ cokernel.π k) = _
      calc
        _ = (factorThruImageSubobject ((A n).ι 0) ≫ (F.step 0).arrow) ≫
            (inv (F.step 0).arrow ≫ cokernel.π k) := by
          congr 1
          exact (imageSubobject_arrow_comp ((A n).ι 0)).symm
        _ = _ := by simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    change eqToHom _ ≫ (A n).ι 0 ≫ (a.hom ≫ e.inv ≫ (t 0 n).hom) =
      X.toPageInfinity L 0 n ≫ (t 0 n).hom
    calc
      _ = (eqToHom _ ≫ ((A n).ι 0 ≫ a.hom)) ≫ e.inv ≫ (t 0 n).hom := by
        simp only [Category.assoc]
      _ = (X.toPageInfinity L 0 n ≫ e.hom) ≫ e.inv ≫ (t 0 n).hom := by
        rw [ha_comm, ← Category.assoc, ← he]
        simp only [Category.assoc]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id_assoc]

end CategoryTheory.BigradedExactCouple
