/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import WeilConjectures.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-!
# Five-term exact sequence of a first-quadrant spectral sequence

Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term).

The bottom edge `E₂^{p,0} → Hᵖ` and the left edge `H^q → E₂^{0,q}` are constructed
from the convergence data: the quotient `E₂ → E_∞` (resp. inclusion `E_∞ → E₂`), the
canonical comparison `E_∞^{p,q} ≅ grᵖ H^{p+q}` of weak convergence, and the inclusion
`grᵖ Hᵖ = Fᵖ Hᵖ ⊆ Hᵖ` (resp. the quotient `H^q = F⁰ H^q → gr⁰ H^q`).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_kernel {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

private theorem pullback_bot {U V : C} (f : U ⟶ V) :
    (Subobject.pullback f).obj ⊥ = kernelSubobject f := by
  have : kernelSubobject (𝟙 V) = ⊥ := by
    apply Subobject.mk_eq_bot_iff_zero.mpr
    exact kernel.ι_of_mono _
  rw [← this, pullback_kernel, Category.comp_id]

/-- A page system is first-quadrant when all page terms with a negative index vanish.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
def IsFirstQuadrant (X : BigradedExactCouple C 0) : Prop :=
  ∀ (r : ℕ) (p q : ℤ), p < 0 ∨ q < 0 → IsZero (X.page r p q)

private theorem page_zero (X : BigradedExactCouple C 0) (hquadrant : X.IsFirstQuadrant)
    (r : ℕ) (p q : ℤ) (h : p < 0 ∨ q < 0) : IsZero ((X.pageCouple r).E p q) := by
  have hz := hquadrant (r + 2) p q h
  change IsZero ((X.pageCouple (r + 2 - 2)).E p q) at hz
  rw [show r + 2 - 2 = r by omega] at hz
  exact hz

private theorem cycles_stable (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (R : ℕ) (p q : ℤ) (hout : ∀ r : ℕ, R ≤ r → (X.pageCouple r).d p q = 0) :
    L.Z p q = X.cycleBoundaryTower.Z R p q := by
  let T := X.cycleBoundaryTower
  have hs (r : ℕ) (hr : R ≤ r) : T.Z (r + 1) p q = T.Z r p q := by
    rw [T.Z_succ, hout r hr, kernelSubobject_zero, Subobject.pullback_top,
      Subobject.exists_iso_map, Subobject.map_top, Subobject.mk_arrow]
  have ht (k : ℕ) : T.Z (R + k) p q = T.Z R p q := by
    induction k with
    | zero => simp
    | succ k ih => rw [← Nat.add_assoc, hs _ (by omega), ih]
  apply le_antisymm ((L.Z_glb p q).1 ⟨R, rfl⟩)
  apply (L.Z_glb p q).2
  rintro _ ⟨r, rfl⟩
  change T.Z R p q ≤ T.Z r p q
  by_cases hr : r ≤ R
  · exact (antitone_nat_of_succ_le (f := fun r ↦ T.Z r p q)
      (fun r ↦ T.Z_decreasing r p q)) hr
  · have hh : T.Z r p q = T.Z R p q := by
      simpa only [Nat.add_sub_of_le (show R ≤ r by omega)] using ht (r - R)
    exact hh.ge

private theorem boundaries_stable (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (R : ℕ) (p q : ℤ) (hin : ∀ r : ℕ, R ≤ r → (X.pageCouple r).dInto p q = 0) :
    L.B p q = X.cycleBoundaryTower.B R p q := by
  let T := X.cycleBoundaryTower
  have hs (r : ℕ) (hr : R ≤ r) : T.B (r + 1) p q = T.B r p q := by
    rw [T.B_succ, hin r hr, imageSubobject_zero, pullback_bot, T.projection_kernel,
      Subobject.exists_iso_map, Subobject.map_mk]
    simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
  have ht (k : ℕ) : T.B (R + k) p q = T.B R p q := by
    induction k with
    | zero => simp
    | succ k ih => rw [← Nat.add_assoc, hs _ (by omega), ih]
  apply le_antisymm
  · apply (L.B_lub p q).2
    rintro _ ⟨r, rfl⟩
    change T.B r p q ≤ T.B R p q
    by_cases hr : r ≤ R
    · exact (monotone_nat_of_le_succ (f := fun r ↦ T.B r p q)
        (fun r ↦ T.B_increasing r p q)) hr
    · have hh : T.B r p q = T.B R p q := by
        simpa only [Nat.add_sub_of_le (show R ≤ r by omega)] using ht (r - R)
      exact hh.le
  · exact (L.B_lub p q).1 ⟨R, rfl⟩

private theorem first_cycles (X : BigradedExactCouple C 0) (p q : ℤ) :
    X.cycleBoundaryTower.Z 1 p q = kernelSubobject (X.d p q) := by
  rw [show 1 = 0 + 1 from rfl, X.cycleBoundaryTower.Z_succ,
    X.cycleBoundaryTower.projection_zero, Subobject.exists_iso_map,
    ← Subobject.inf_eq_map_pullback, X.cycleBoundaryTower.Z_zero, inf_of_le_right le_top]
  rfl

private theorem first_boundaries (X : BigradedExactCouple C 0) (p q : ℤ) :
    X.cycleBoundaryTower.B 1 p q = imageSubobject (X.dInto p q) := by
  rw [show 1 = 0 + 1 from rfl, X.cycleBoundaryTower.B_succ,
    X.cycleBoundaryTower.projection_zero, Subobject.exists_iso_map,
    ← Subobject.inf_eq_map_pullback, X.cycleBoundaryTower.Z_zero, inf_of_le_right le_top]
  rfl

/-- On the bottom row of a first-quadrant spectral sequence every outgoing differential
lands in a zero term, so every finite cycle object, hence the limiting one, is everything.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem limitCycles_bottom_eq_top (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (hquadrant : X.IsFirstQuadrant) (p : ℤ) : L.Z p 0 = ⊤ := by
  rw [cycles_stable X L 0 p 0 (fun r _ ↦
    (page_zero X hquadrant r _ _ (Or.inr (by omega))).eq_zero_of_tgt _),
    X.cycleBoundaryTower.Z_zero]

/-- On the left column of a first-quadrant spectral sequence every incoming differential
starts at a zero term, so every finite boundary object, hence the limiting one, is zero;
thus the limiting boundaries map to zero in the initial page.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem limitBoundaries_left_comp_eq_zero (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (hquadrant : X.IsFirstQuadrant) (q : ℤ) :
    Subobject.ofLE (L.B 0 q) (L.Z 0 q) (limitBoundary_le_cycle X L 0 q) ≫
      (L.Z 0 q).arrow = 0 := by
  have hB : L.B 0 q = ⊥ := by
    rw [boundaries_stable X L 0 0 q (fun r _ ↦
      (page_zero X hquadrant r _ _ (Or.inl (by omega))).eq_zero_of_src _),
      X.cycleBoundaryTower.B_zero]
  rw [Subobject.ofLE_arrow]
  exact Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Subobject.mk_arrow] using hB)

private theorem infinity_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (p q : ℤ) (hz : IsZero (X.E p q)) : IsZero (X.pageInfinity L p q) := by
  exact (hz.of_mono (L.Z p q).arrow).of_epi (cokernel.π _)

private theorem graded_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (n p : ℤ) (hp : p < 0 ∨ n < p) :
    IsZero ((X.imageFiltration n (A n)).gradedPiece p) := by
  have hz : IsZero (X.E p (n - p)) := hquadrant 2 p (n - p) (by omega)
  have e := Classical.choose
    (X.weakConvergence_comparison L A hconverges.2.1.1 p (n - p)).exists
  have h := e.isZero_iff.mp (infinity_zero X L p (n - p) hz)
  rw [show p + (n - p) = n by omega] at h
  exact h

private theorem filtration_eq_of_graded_zero {T : C} (F : PBCDecreasingFiltration T)
    (p : ℤ) (hz : IsZero (F.gradedPiece p)) : F.step (p + 1) = F.step p := by
  let f := Subobject.ofLE _ _ (F.antitone_step (show p ≤ p + 1 by omega))
  have : Epi f := Preadditive.epi_of_isZero_cokernel f hz
  have : IsIso f := isIso_of_mono_of_epi f
  exact Subobject.eq_of_comm (asIso f) (Subobject.ofLE_arrow _)

/-- For a convergent first-quadrant spectral sequence, `F^{p+1} Hⁿ = 0` for `p ≥ n`, so the
inclusion `F^{p+1} Hⁿ ⊆ Fᵖ Hⁿ` is zero: the graded pieces `grᵖ Hⁿ ≅ E_∞^{p,n-p}` vanish for
`p > n`, so the steps from `n+1` on agree, and separation makes them zero.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem imageFiltration_ofLE_eq_zero (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (n p : ℤ) (hp : n ≤ p) :
    Subobject.ofLE ((X.imageFiltration n (A n)).step (p + 1))
      ((X.imageFiltration n (A n)).step p)
      ((X.imageFiltration n (A n)).antitone_step (by omega)) ≫ 𝟙 _ = 0 := by
  let F := X.imageFiltration n (A n)
  have heq (i : ℤ) (hi : n < i) : F.step (i + 1) = F.step i :=
    filtration_eq_of_graded_zero F i (graded_zero X L A hquadrant hconverges n i (Or.inr hi))
  have htail (k : ℕ) : F.step (p + 1 + k) = F.step (p + 1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show p + 1 + (k + 1 : ℕ) = (p + 1 + k) + 1 by omega, heq _ (by omega)]
      exact ih
  have hbot : F.step (p + 1) = ⊥ := by
    apply hconverges.2.1.2 n |>.1
    intro i
    by_cases hi : i ≤ p + 1
    · exact F.antitone_step hi
    · have ht : F.step i = F.step (p + 1) := by
        simpa only [show p + 1 + ((i - (p + 1)).toNat : ℤ) = i by omega] using
          htail (i - (p + 1)).toNat
      exact ht.ge
  rw [Category.comp_id]
  apply (cancel_mono (F.step p).arrow).mp
  rw [Subobject.ofLE_arrow, zero_comp]
  exact Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Subobject.mk_arrow] using hbot)

/-- For a convergent first-quadrant spectral sequence, `F⁰ Hⁿ = Hⁿ`: the graded pieces
`grᵖ Hⁿ ≅ E_∞^{p,n-p}` vanish for `p < 0`, so the steps up to `0` agree, and exhaustiveness
makes them everything.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
theorem imageFiltration_zero_eq_top (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (n : ℤ) :
    (X.imageFiltration n (A n)).step 0 = ⊤ := by
  let F := X.imageFiltration n (A n)
  have heq (i : ℤ) (hi : i < 0) : F.step (i + 1) = F.step i :=
    filtration_eq_of_graded_zero F i (graded_zero X L A hquadrant hconverges n i (Or.inl hi))
  have hhead (k : ℕ) : F.step (-(k : ℤ)) = F.step 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← heq (-((k + 1 : ℕ) : ℤ)) (by omega),
        show -((k + 1 : ℕ) : ℤ) + 1 = -(k : ℤ) by omega]
      exact ih
  apply hconverges.2.1.2 n |>.2
  intro i
  by_cases hi : 0 ≤ i
  · exact F.antitone_step hi
  · have ht : F.step i = F.step 0 := by
      simpa only [show -(((-i).toNat : ℕ) : ℤ) = i by omega] using hhead (-i).toNat
    exact ht.le

/-- The canonical comparison `E_∞^{p,q} ≅ grᵖ H^{p+q}` of a weakly convergent couple,
the unique isomorphism compatible with the two canonical maps out of `D^{p,q}`.
Source: blueprint def-sp-convergence; Stacks Tag 012U (blueprint: lem-pqf-leray-five-term). -/
noncomputable def infinityGradedIso (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hconverges : X.ConvergesTo L A) (p q : ℤ) :
    X.pageInfinity L p q ≅ (X.imageFiltration (p + q) (A (p + q))).gradedPiece p :=
  Classical.choose (X.weakConvergence_comparison L A hconverges.2.1.1 p q).exists

/-- The bottom edge map `E₂^{p,0} → E_∞^{p,0} ≅ grᵖ Hᵖ = Fᵖ Hᵖ ⊆ Hᵖ` of a convergent
first-quadrant spectral sequence.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
noncomputable def bottomEdge (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (p : ℤ) : X.page 2 p 0 ⟶ (A p).obj :=
  (L.Z p 0).factorThru (𝟙 (X.E p 0))
      (by rw [X.limitCycles_bottom_eq_top L hquadrant p]; exact Subobject.top_factors _) ≫
    cokernel.π (Subobject.ofLE (L.B p 0) (L.Z p 0) (limitBoundary_le_cycle X L p 0)) ≫
    (X.infinityGradedIso L A hconverges p 0).hom ≫
    cokernel.desc _ (𝟙 _)
      (X.imageFiltration_ofLE_eq_zero L A hquadrant hconverges (p + 0) p (by omega)) ≫
    ((X.imageFiltration (p + 0) (A (p + 0))).step p).arrow ≫
    eqToHom (by rw [add_zero])

/-- The left edge map `H^q = F⁰ H^q → gr⁰ H^q ≅ E_∞^{0,q} ⊆ E₂^{0,q}` of a convergent
first-quadrant spectral sequence.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term). -/
noncomputable def leftEdge (X : BigradedExactCouple C 0) (L : LimitSubobjects X)
    (A : ∀ n : ℤ, AlphaColimit X n) (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) (q : ℤ) : (A q).obj ⟶ X.page 2 0 q :=
  eqToHom (by rw [zero_add]) ≫
    ((X.imageFiltration (0 + q) (A (0 + q))).step 0).factorThru (𝟙 _)
      (by rw [X.imageFiltration_zero_eq_top L A hquadrant hconverges];
          exact Subobject.top_factors _) ≫
    cokernel.π _ ≫
    (X.infinityGradedIso L A hconverges 0 q).inv ≫
    cokernel.desc _ (L.Z 0 q).arrow (X.limitBoundaries_left_comp_eq_zero L hquadrant q)

private theorem bottom_boundaries_one (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (hquadrant : X.IsFirstQuadrant) : L.B 1 0 = ⊥ := by
  rw [boundaries_stable X L 0 1 0 (fun r _ ↦
    (page_zero X hquadrant r _ _ (Or.inl (by omega))).eq_zero_of_src _),
    X.cycleBoundaryTower.B_zero]

private theorem left_cycles_one (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (hquadrant : X.IsFirstQuadrant) :
    L.Z 0 1 = kernelSubobject (X.pageDifferential 2 0 1) := by
  rw [cycles_stable X L 1 0 1 (fun r hr ↦
    (page_zero X hquadrant r _ _ (Or.inr (by omega))).eq_zero_of_tgt _), first_cycles]
  rfl

private theorem bottom_boundaries_two (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (hquadrant : X.IsFirstQuadrant) :
    L.B 2 0 = imageSubobject (X.pageDifferential 2 0 1) := by
  rw [boundaries_stable X L 1 2 0 (fun r hr ↦
    (page_zero X hquadrant r _ _ (Or.inl (by omega))).eq_zero_of_src _), first_boundaries]
  simp [dInto, pageDifferential, pageCouple]

private theorem iso_cokernel_of_zero {U V : C} (f : U ⟶ V) (hf : f = 0) :
    IsIso (cokernel.π f) :=
  CokernelCofork.IsColimit.isIso_π
    (CokernelCofork.ofπ _ (cokernel.condition _)) (cokernelIsCokernel _) hf

private theorem ofLE_zero {T : C} (B Z : Subobject T) (h : B ≤ Z) (hb : B = ⊥) :
    Subobject.ofLE B Z h = 0 := by
  apply (cancel_mono Z.arrow).mp
  rw [Subobject.ofLE_arrow, zero_comp]
  exact Subobject.mk_eq_bot_iff_zero.mp (by simpa only [Subobject.mk_arrow] using hb)

private theorem factor_id_isIso {T : C} (S : Subobject T) (h : S.Factors (𝟙 T)) :
    IsIso (S.factorThru (𝟙 T) h) := by
  have : Epi S.arrow := epi_of_epi_fac (S.factorThru_arrow (𝟙 T) h)
  have : IsIso S.arrow := isIso_of_mono_of_epi _
  have he : S.factorThru (𝟙 T) h = inv S.arrow := by
    apply (cancel_mono S.arrow).mp
    simp
  rw [he]
  infer_instance

private theorem desc_id_isIso {U V : C} (f : U ⟶ V) (h : f ≫ 𝟙 V = 0) :
    IsIso (cokernel.desc f (𝟙 V) h) := by
  have : IsIso (cokernel.π f) := iso_cokernel_of_zero f (by simpa using h)
  have he : cokernel.desc f (𝟙 V) h = inv (cokernel.π f) := by
    apply (cancel_epi (cokernel.π f)).mp
    simp
  rw [he]
  infer_instance

private theorem exact_of_factors {U T W B V Q : C}
    (f : U ⟶ T) (g : T ⟶ W) (b : B ⟶ V) (π : V ⟶ Q)
    (w : b ≫ π = 0) (hex : (ShortComplex.mk b π w).Exact)
    (i : T ⟶ V) [IsIso i] (e : U ⟶ B) [Epi e] (m : Q ⟶ W) [Mono m]
    (hf : f ≫ i = e ≫ b) (hg : g = i ≫ π ≫ m) :
    (ComposableArrows.mk₂ f g).Exact := by
  have wz : f ≫ (i ≫ π) = 0 := by rw [← Category.assoc, hf, Category.assoc, w, comp_zero]
  let S := ShortComplex.mk f (i ≫ π) wz
  let φ : S ⟶ ShortComplex.mk b π w :=
    { τ₁ := e, τ₂ := i, τ₃ := 𝟙 Q, comm₁₂ := hf.symm, comm₂₃ := by simp [S] }
  have hs : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hex
  have wz' : f ≫ g = 0 := by rw [hg, ← Category.assoc i, ← Category.assoc, wz, zero_comp]
  let ψ : S ⟶ ShortComplex.mk f g wz' :=
    { τ₁ := 𝟙 U, τ₂ := 𝟙 T, τ₃ := m,
      comm₁₂ := by simp [S], comm₂₃ := by simpa [S, Category.assoc] using hg }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hs).exact_toComposableArrows

/--
The canonical low-degree edge maps of a convergent first-quadrant spectral sequence
form the five-term exact sequence
`0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²`: the bottom edge in total degree 1,
the left edge in total degree 1, the page-two differential (the transgression), and the
bottom edge in total degree 2.
Source: Stacks Project, Homology, Lemma 0132 (blueprint: lem-pqf-leray-five-term).
Proof: in the first quadrant the entries (1,0), (0,1), (2,0) see only the differential
d₂ : E₂^{0,1} → E₂^{2,0} (d_r out of (1,0), (2,0) and into (0,1) start or end in zero
terms, and d_r for r ≥ 3 out of (0,1) lands in a zero term), so E_∞^{1,0} = E₂^{1,0},
E_∞^{0,1} = ker d₂ and E_∞^{2,0} = coker d₂ (uses def-sp-convergence). Convergence and the
vanishing of grᵖ outside 0..n give F⁰Hⁿ = Hⁿ and F^{n+1}Hⁿ = 0 (def-sp-filtration), so
0 → F¹H¹ = E_∞^{1,0} → H¹ → gr⁰H¹ = E_∞^{0,1} → 0 is exact and F²H² = E_∞^{2,0} ⊆ H².
Hence the degree-1 bottom edge is injective with image F¹H¹ = the kernel of the left edge,
whose image is ker d₂; and the kernel of the degree-2 bottom edge is the kernel of
E₂^{2,0} → E_∞^{2,0}, the image of d₂.
-/
theorem lerayFiveTerm (X : BigradedExactCouple C 0)
    (L : LimitSubobjects X) (A : ∀ n : ℤ, AlphaColimit X n)
    (hquadrant : X.IsFirstQuadrant)
    (hconverges : X.ConvergesTo L A) :
    (ComposableArrows.mk₅ (0 : (0 : C) ⟶ X.page 2 1 0)
      (X.bottomEdge L A hquadrant hconverges 1)
      (X.leftEdge L A hquadrant hconverges 1)
      (X.pageDifferential 2 0 1)
      (X.bottomEdge L A hquadrant hconverges 2)).Exact := by
  let F := X.imageFiltration 1 (A 1)
  let G := X.imageFiltration 2 (A 2)
  let c (p q : ℤ) := Subobject.ofLE (L.B p q) (L.Z p q) (limitBoundary_le_cycle X L p q)
  let z (p : ℤ) := (L.Z p 0).factorThru (𝟙 (X.E p 0))
    (by rw [X.limitCycles_bottom_eq_top L hquadrant p]; exact Subobject.top_factors _)
  have hz (p : ℤ) : IsIso (z p) := factor_id_isIso _ _
  have hc1 : c 1 0 = 0 := ofLE_zero _ _ _ (bottom_boundaries_one X L hquadrant)
  have hπ1 : IsIso (cokernel.π (c 1 0)) := iso_cokernel_of_zero _ hc1
  let t1 := cokernel.desc _ (𝟙 _)
    (X.imageFiltration_ofLE_eq_zero L A hquadrant hconverges 1 1 (by omega))
  let t2 := cokernel.desc _ (𝟙 _)
    (X.imageFiltration_ofLE_eq_zero L A hquadrant hconverges 2 2 (by omega))
  have ht1 : IsIso t1 := desc_id_isIso _ _
  have ht2 : IsIso t2 := desc_id_isIso _ _
  let e1 := z 1 ≫ cokernel.π (c 1 0) ≫
    (X.infinityGradedIso L A hconverges 1 0).hom ≫ t1
  have he1 : IsIso e1 := by dsimp [e1]; infer_instance
  have hb1 : X.bottomEdge L A hquadrant hconverges 1 = e1 ≫ (F.step 1).arrow := by
    simp [bottomEdge, e1, z, c, t1, F, Category.assoc]
  have hb1mono : Mono (X.bottomEdge L A hquadrant hconverges 1) := by
    rw [hb1]
    infer_instance
  let v := (F.step 0).factorThru (𝟙 (A 1).obj)
    (by rw [X.imageFiltration_zero_eq_top L A hquadrant hconverges 1]
        exact Subobject.top_factors _)
  have hv : IsIso v := factor_id_isIso _ _
  let b := Subobject.ofLE (F.step 1) (F.step 0) (F.antitone_step (by omega))
  let π := cokernel.π b
  let l := cokernel.desc (c 0 1) (L.Z 0 1).arrow
    (X.limitBoundaries_left_comp_eq_zero L hquadrant 1)
  have hleftB : L.B 0 1 = ⊥ := by
    rw [boundaries_stable X L 0 0 1 (fun r _ ↦
      (page_zero X hquadrant r _ _ (Or.inl (by omega))).eq_zero_of_src _),
      X.cycleBoundaryTower.B_zero]
  have hc0 : c 0 1 = 0 := ofLE_zero _ _ _ hleftB
  have hπ0 : IsIso (cokernel.π (c 0 1)) := iso_cokernel_of_zero _ hc0
  have hl : l = inv (cokernel.π (c 0 1)) ≫ (L.Z 0 1).arrow := by
    apply (cancel_epi (cokernel.π (c 0 1))).mp
    simp [l]
  have hlmono : Mono l := by rw [hl]; infer_instance
  let m := (X.infinityGradedIso L A hconverges 0 1).inv ≫ l
  have hm : Mono m := by dsimp [m]; infer_instance
  have hleft : X.leftEdge L A hquadrant hconverges 1 = v ≫ π ≫ m := by
    simp [leftEdge, v, π, b, m, l, c, F]
  have hex1 : (ComposableArrows.mk₂ (X.bottomEdge L A hquadrant hconverges 1)
      (X.leftEdge L A hquadrant hconverges 1)).Exact := by
    apply exact_of_factors _ _ b π (cokernel.condition b)
      (ShortComplex.cokernelSequence_exact b) v e1 m
    · apply (cancel_mono (F.step 0).arrow).mp
      simp [hb1, v, b, Category.assoc]
    · exact hleft
  let d := X.pageDifferential 2 0 1
  have wker : (L.Z 0 1).arrow ≫ d = 0 := by
    dsimp [d]
    rw [left_cycles_one X L hquadrant]
    exact kernelSubobject_arrow_comp _
  have hker : (ShortComplex.mk (L.Z 0 1).arrow d wker).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel, imageSubobject_mono, Subobject.mk_arrow]
    exact left_cycles_one X L hquadrant
  let e0 := v ≫ π ≫ (X.infinityGradedIso L A hconverges 0 1).inv ≫
    inv (cokernel.π (c 0 1))
  have he0 : Epi e0 := by dsimp [e0, π]; infer_instance
  have hex2 : (ComposableArrows.mk₂ (X.leftEdge L A hquadrant hconverges 1) d).Exact := by
    apply exact_of_factors _ _ (L.Z 0 1).arrow d wker hker (𝟙 _) e0 (𝟙 _)
    · simp [hleft, e0, m, hl, Category.assoc]
    · simp
  have hdFactors : (L.B 2 0).Factors d :=
    (Subobject.imageSubobject_le_iff d _).mp (bottom_boundaries_two X L hquadrant).ge
  let e2 := (L.B 2 0).factorThru d hdFactors
  have he2 : Epi e2 := by
    apply epi_of_imageSubobject_comp_arrow_eq e2
    rw [Subobject.factorThru_arrow]
    exact (bottom_boundaries_two X L hquadrant).symm
  let m2 := (X.infinityGradedIso L A hconverges 2 0).hom ≫ t2 ≫ (G.step 2).arrow
  have hm2 : Mono m2 := by dsimp [m2]; infer_instance
  have hex3 : (ComposableArrows.mk₂ d (X.bottomEdge L A hquadrant hconverges 2)).Exact := by
    apply exact_of_factors _ _ (c 2 0) (cokernel.π (c 2 0)) (cokernel.condition _)
      (ShortComplex.cokernelSequence_exact _) (z 2) e2 m2
    · apply (cancel_mono (L.Z 2 0).arrow).mp
      simp [z, e2, c, Category.assoc]
    · simp [bottomEdge, z, m2, c, t2, G]
  have hex0 : (ComposableArrows.mk₂ (0 : (0 : C) ⟶ X.page 2 1 0)
      (X.bottomEdge L A hquadrant hconverges 1)).Exact := by
    exact ((ShortComplex.mk _ _ (by simp)).exact_iff_mono rfl).mpr
      hb1mono |>.exact_toComposableArrows
  apply ComposableArrows.exact_of_δ₀ hex0
  apply ComposableArrows.exact_of_δ₀ hex1
  apply ComposableArrows.exact_of_δ₀ hex2
  exact hex3

end CategoryTheory.BigradedExactCouple
