/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-! # Pulling quotient boundaries back to a filtration step

Source: Stacks Project, Tag 012K, displayed boundary formula.
(blueprint: lem-sp-filtered-complex-boundary-pullback)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

private theorem factors_desc_epi {X Y A : C} (P : Subobject Y) (x : X ⟶ Y)
    (e : A ⟶ X) [Epi e] (h : P.Factors (e ≫ x)) : P.Factors x := by
  have hx : x ≫ cokernel.π P.arrow = 0 := by
    rw [← cancel_epi e, comp_zero, ← Category.assoc]
    have hh := congrArg (fun f => f ≫ cokernel.π P.arrow) (P.factorThru_arrow _ h)
    simpa only [Category.assoc, cokernel.condition, comp_zero] using hh.symm
  rw [← Abelian.monoLift_comp P.arrow x hx]
  exact Subobject.factors_comp_arrow _

private theorem image_refinement {X Y A : C} (f : X ⟶ Y) (x : A ⟶ Y)
    (h : (imageSubobject f).Factors x) :
    ∃ (A' : C) (e : A' ⟶ A) (_ : Epi e) (y : A' ⟶ X), e ≫ x = y ≫ f := by
  obtain ⟨A', e, he, y, hy⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject f) ((imageSubobject f).factorThru x h)
  refine ⟨A', e, he, y, ?_⟩
  simpa only [Category.assoc, Subobject.factorThru_arrow, imageSubobject_arrow_comp] using
    congrArg (fun a => a ≫ (imageSubobject f).arrow) hy

private theorem sup_refinement {Y A : C} (P Q : Subobject Y) (x : A ⟶ Y)
    (h : (P ⊔ Q).Factors x) :
    ∃ (A' : C) (e : A' ⟶ A) (_ : Epi e)
      (y : A' ⟶ (P : C)) (z : A' ⟶ (Q : C)),
      e ≫ x = y ≫ P.arrow + z ≫ Q.arrow := by
  have := Subobject.epi_supDesc P Q
  obtain ⟨A', e, he, t, ht⟩ := surjective_up_to_refinements_of_epi
    (Subobject.supDesc P Q) ((P ⊔ Q).factorThru x h)
  refine ⟨A', e, he, t ≫ biprod.fst, t ≫ biprod.snd, ?_⟩
  have ht' := congrArg (fun f => f ≫ (P ⊔ Q).arrow) ht
  simpa only [Category.assoc, Subobject.factorThru_arrow, Subobject.supDesc,
    biprod.desc_eq, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    Subobject.ofLE_arrow] using ht'

private theorem pullback_exists_of_kernel_le {X Y : C} (q : X ⟶ Y) [Epi q]
    (V : Subobject X) (h : kernelSubobject q ≤ V) :
    (Subobject.pullback q).obj ((Subobject.«exists» q).obj V) = V := by
  apply le_antisymm
  · have hk : kernel.ι q ≫ cokernel.π V.arrow = 0 := by
      have hf := (Subobject.le_iff_factors_arrow _ _).mp h
      have hh := congrArg (fun f => f ≫ cokernel.π V.arrow)
        (V.factorThru_arrow _ hf)
      have hh0 : (kernelSubobject q).arrow ≫ cokernel.π V.arrow = 0 := by
        simpa only [Category.assoc, cokernel.condition, comp_zero] using hh.symm
      rw [← kernelSubobject_arrow', Category.assoc, hh0, comp_zero]
    let c := Abelian.epiDesc q (cokernel.π V.arrow) hk
    have hc : q ≫ c = cokernel.π V.arrow := Abelian.comp_epiDesc _ _ _
    have hv : ((Subobject.«exists» q).obj V).arrow ≫ c = 0 := by
      obtain ⟨e, he, heq⟩ := Subobject.exists_fac q V
      rw [← cancel_epi e, comp_zero, ← Category.assoc, heq, Category.assoc, hc]
      simp
    apply Subobject.le_of_factors
    have hp := (pullback_factors_iff _ _ _).mp (Subobject.factors_self
      ((Subobject.pullback q).obj ((Subobject.«exists» q).obj V)))
    have hp0 : ((Subobject.pullback q).obj ((Subobject.«exists» q).obj V)).arrow ≫
        cokernel.π V.arrow = 0 := by
      rw [← hc, ← Category.assoc,
        ← ((Subobject.«exists» q).obj V).factorThru_arrow _ hp]
      simp only [Category.assoc, hv, comp_zero]
    rw [← Abelian.monoLift_comp V.arrow _ hp0]
    exact Subobject.factors_comp_arrow _
  · exact (Subobject.gc_exists_pullback q).le_u_l V

private theorem quotient_epi (F : DecreasingFiltration K) (a b n : ℤ) (h : a ≤ b) :
    Epi ((F.complexQuotientπ a b h).f n) := by
  change Epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
    (cokernel.π (Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h))))
  infer_instance

private theorem quotient_exact (F : DecreasingFiltration K) (a b n : ℤ) (h : a ≤ b) :
    (ShortComplex.mk
      ((Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h)).f n)
      ((F.complexQuotientπ a b h).f n)
      (congrArg (fun f => f.f n) (cokernel.condition
        (Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h))))).Exact := by
  let l := Subobject.ofLE (F.step b) (F.step a) (F.antitone_step h)
  exact (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk l (cokernel.π l) (cokernel.condition l))
    (cokernelIsCokernel l)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_zero_iff (F : DecreasingFiltration K) (p n r : ℤ)
    (ha : p - r + 1 ≤ p) {X : C} (x : X ⟶ (F.step p : CochainComplex C ℤ).X n) :
    let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
    let T := F.complexQuotient (p - r + 1) (p + 1) ht
    (x ≫ (Subobject.ofLE (F.step p) (F.step (p - r + 1))
      (F.antitone_step ha)).f n ≫ (F.complexQuotientπ (p - r + 1) (p + 1) ht).f n) ≫
        T.pOpcycles n = 0 ↔
    ((F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
      (F.complexStep (p - r + 1) (n - 1))) ⊔ F.complexStep (p + 1) n).Factors
      (x ≫ (F.step p).arrow.f n) := by
  let a := p - r + 1
  let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
  let A : CochainComplex C ℤ := F.step a
  let T := F.complexQuotient a (p + 1) ht
  let q := F.complexQuotientπ a (p + 1) ht
  let l := Subobject.ofLE (F.step p) (F.step a) (F.antitone_step ha)
  let i := Subobject.ofLE (F.step (p + 1)) (F.step a) (F.antitone_step ht)
  let j := Subobject.ofLE (F.step (p + 1)) (F.step p)
    (F.antitone_step (Int.le_add_one (show p ≤ p from le_rfl)))
  let D := F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
    (F.complexStep a (n - 1))
  let V := D ⊔ F.complexStep (p + 1) n
  have hmA : Mono ((F.step a).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step a).arrow)
    infer_instance
  have hmP : Mono ((F.step p).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
    infer_instance
  have hq := quotient_epi F a (p + 1) (n - 1) ht
  have hl : l.f n ≫ (F.step a).arrow.f n = (F.step p).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step ha))
  have hi : i.f n ≫ (F.step a).arrow.f n = (F.step (p + 1)).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step ht))
  have hj : j.f n ≫ (F.step p).arrow.f n = (F.step (p + 1)).arrow.f n :=
    congrArg (fun f => f.f n) (Subobject.ofLE_arrow
      (F.antitone_step (Int.le_add_one (show p ≤ p from le_rfl))))
  have hd : (Subobject.«exists» (K.d (n - 1) n)).obj (F.complexStep a (n - 1)) =
      imageSubobject ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) := by
    dsimp only [complexStep]
    rw [← Subobject.exists_obj_top ((F.step a).arrow.f (n - 1)),
      Subobject.exists_obj_comp, Subobject.exists_obj_top]
  change (x ≫ l.f n ≫ q.f n) ≫ T.pOpcycles n = 0 ↔
    V.Factors (x ≫ (F.step p).arrow.f n)
  constructor
  · intro hx
    obtain ⟨X₁, e₁, he₁, y₁, hy₁⟩ :=
      (CokernelCofork.IsColimit.comp_π_eq_zero_iff_up_to_refinements
        (T.opcyclesIsCokernel (n - 1) n (by simp)) (x ≫ l.f n ≫ q.f n)).mp hx
    obtain ⟨X₂, e₂, he₂, y₂, hy₂⟩ :=
      surjective_up_to_refinements_of_epi (q.f (n - 1)) y₁
    have hdiff : (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n) ≫ q.f n = 0 := by
      rw [Preadditive.sub_comp]
      have hh := congrArg (fun f => e₂ ≫ f) hy₁
      simp only [Category.assoc]
      rw [← q.comm]
      rw [reassoc_of% hy₂] at hh
      simpa only [Category.assoc, sub_self] using congrArg
        (fun f => f - (y₂ ≫ q.f (n - 1) ≫ T.d (n - 1) n)) hh
    obtain ⟨X₃, e₃, he₃, f, hf⟩ :=
      (quotient_exact F a (p + 1) n ht).exact_up_to_refinements
        (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n) hdiff
    have hdecomp : (e₃ ≫ e₂ ≫ e₁) ≫ x ≫ (F.step p).arrow.f n =
        (e₃ ≫ y₂ ≫ A.d (n - 1) n) ≫ (F.step a).arrow.f n +
          f ≫ (F.step (p + 1)).arrow.f n := by
      have hh := congrArg (fun t => t ≫ (F.step a).arrow.f n) hf
      change (e₃ ≫ (e₂ ≫ e₁ ≫ x ≫ l.f n - y₂ ≫ A.d (n - 1) n)) ≫
        (F.step a).arrow.f n = (f ≫ i.f n) ≫ (F.step a).arrow.f n at hh
      simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, hl, hi] at hh
      simpa only [Category.assoc, add_comm] using (sub_eq_iff_eq_add.mp hh)
    let b := (e₃ ≫ y₂ ≫ A.d (n - 1) n) ≫ (F.step a).arrow.f n
    have hbP : (F.complexStep p n).Factors b := by
      have hb : (e₃ ≫ e₂ ≫ e₁ ≫ x - f ≫ j.f n) ≫ (F.step p).arrow.f n = b := by
        simp only [Preadditive.sub_comp, Category.assoc, hj]
        simpa only [Category.assoc, b] using
          (eq_sub_iff_add_eq.mpr hdecomp.symm).symm
      rw [complexStep, imageSubobject_mono]
      exact ⟨e₃ ≫ e₂ ≫ e₁ ≫ x - f ≫ j.f n, hb⟩
    have hbD : D.Factors b := by
      apply (Subobject.inf_factors _).mpr
      refine ⟨hbP, ?_⟩
      rw [hd]
      have hh : b = (e₃ ≫ y₂) ≫
          ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) := by
        dsimp only [b]
        rw [Category.assoc, (F.step a).arrow.comm]
        simp only [Category.assoc]
        rfl
      rw [hh]
      exact imageSubobject_factors_comp_self _ _
    have hfN : (F.complexStep (p + 1) n).Factors
        (f ≫ (F.step (p + 1)).arrow.f n) := by
      exact imageSubobject_factors_comp_self _ _
    apply factors_desc_epi V (x ≫ (F.step p).arrow.f n) (e₃ ≫ e₂ ≫ e₁)
    rw [hdecomp]
    exact Subobject.factors_add _ _
      (Subobject.sup_factors_of_factors_left hbD)
      (Subobject.sup_factors_of_factors_right hfN)
  · intro hx
    obtain ⟨X₁, e₁, he₁, y₁, f₁, hy₁⟩ := sup_refinement D
      (F.complexStep (p + 1) n) (x ≫ (F.step p).arrow.f n) hx
    have hyD : (imageSubobject ((F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n)).Factors
        (y₁ ≫ D.arrow) := by
      rw [← hd]
      exact Subobject.factors_of_factors_right _ (Subobject.inf_arrow_factors_right _ _)
    obtain ⟨X₂, e₂, he₂, y₂, hy₂⟩ := image_refinement _ _ hyD
    have hfN : (Subobject.mk ((F.step (p + 1)).arrow.f n)).Factors
        (f₁ ≫ (F.complexStep (p + 1) n).arrow) := by
      rw [← imageSubobject_mono, ← complexStep]
      exact Subobject.factors_comp_arrow _
    obtain ⟨f, hf⟩ := hfN
    have hdecomp : (e₂ ≫ e₁) ≫ x ≫ l.f n =
        y₂ ≫ A.d (n - 1) n + (e₂ ≫ f) ≫ i.f n := by
      apply (cancel_mono ((F.step a).arrow.f n)).mp
      simp only [Preadditive.add_comp, Category.assoc, hl, hi]
      have hh := congrArg (fun t => e₂ ≫ t) hy₁
      simp only [Preadditive.comp_add] at hh
      rw [hy₂, ← hf] at hh
      change e₂ ≫ e₁ ≫ x ≫ (F.step p).arrow.f n =
        (y₂ ≫ (F.step a).arrow.f (n - 1) ≫ K.d (n - 1) n) +
          e₂ ≫ f ≫ (F.step (p + 1)).arrow.f n at hh
      rw [(F.step a).arrow.comm] at hh
      simpa only [Category.assoc] using hh
    rw [← cancel_epi (e₂ ≫ e₁), comp_zero]
    have hiq : i.f n ≫ q.f n = 0 :=
      congrArg (fun f => f.f n) (cokernel.condition i)
    have hdq : A.d (n - 1) n ≫ q.f n ≫ T.pOpcycles n = 0 := by
      rw [← Category.assoc, ← q.comm, Category.assoc, T.d_pOpcycles, comp_zero]
    have hh := congrArg (fun t => t ≫ q.f n ≫ T.pOpcycles n) hdecomp
    simpa only [Preadditive.add_comp, Category.assoc, hdq, reassoc_of% hiq, comp_zero, zero_comp,
      zero_add] using hh

/-- The inverse image of the boundaries of `F^{p-r+1}/F^{p+1}` in `F^p`
is the inverse image of `B_r` under the graded projection.
Source: Stacks Project, Tag 012K, displayed formula for `B_r`.
(blueprint: lem-sp-filtered-complex-boundary-pullback)

Proof: Write A = F^{p-r+1}, P = F^p, and N = F^{p+1}; then N ≤ P ≤ A.
For any generalized element x of P^n, its image in the opcycles of A/N
vanishes precisely when its image in A/N is an incoming boundary. The
cokernel universal property, expressed through epimorphic refinements,
lifts this boundary to y in A^{n-1}, since A → A/N is degreewise epic.
The difference x - dy is killed by A^n → (A/N)^n; degreewise exactness of
N → A → A/N lifts it to f in N^n after another epimorphic refinement.
Thus x = dy + f. Since x and f belong to P^n, dy belongs to the
intersection of P^n with d(A^{n-1}). This decomposition factors through
V = (P^n intersect d(A^{n-1})) + N^n. Factorization descends along the
composite epimorphism: it is equivalent to vanishing after the cokernel
of V's inclusion. Conversely a factorization through V lifts through
the epic map from the biproduct of its two summands, and then through
the epic map onto the differential image. The resulting decomposition
x = dy + f vanishes in the opcycles of A/N, since both dy and f do.
Canceling the refinement epimorphism proves vanishing for x itself.
Let W be V pulled back to P^n. Degreewise exactness identifies the kernel
of P^n → P^n/N^n with the image of N^n → P^n; this is contained in W.
For any epimorphism q and subobject W containing its kernel, pulling
back q(W) gives W: the quotient by W descends along q, and its vanishing
on q(W) proves the reverse inclusion, while the adjunction proves the
forward inclusion. Apply this to the graded projection. Its image of
W is complexBoundaries by definition. The preceding vanishing
criterion identifies the other pullback with W as well, by testing
factorization of the respective subobject arrows. This proves the
claimed equality without any assumption that C is concrete. -/
theorem filteredComplex_boundary_pullback (F : DecreasingFiltration K)
    (p n r : ℤ) (ha : p - r + 1 ≤ p) :
    let ht := ha.trans (Int.le_add_one (show p ≤ p from le_rfl))
    let T := F.complexQuotient (p - r + 1) (p + 1) ht
    (Subobject.pullback
      ((Subobject.ofLE (F.step p) (F.step (p - r + 1)) (F.antitone_step ha)).f n ≫
        (F.complexQuotientπ (p - r + 1) (p + 1) ht).f n)).obj
      (kernelSubobject (T.pOpcycles n)) =
    (Subobject.pullback
      ((F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n)).obj
      (F.complexBoundaries p n r) := by
  dsimp only
  let hp := Int.le_add_one (show p ≤ p from le_rfl)
  let q := (F.complexQuotientπ p (p + 1) hp).f n
  let m := (F.step p).arrow.f n
  let j := (Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step hp)).f n
  let V := (F.complexStep p n ⊓ (Subobject.«exists» (K.d (n - 1) n)).obj
    (F.complexStep (p - r + 1) (n - 1))) ⊔ F.complexStep (p + 1) n
  let W := (Subobject.pullback m).obj V
  have hq := quotient_epi F p (p + 1) n hp
  have hk : kernelSubobject q ≤ W := by
    have heq : imageSubobject j = kernelSubobject q :=
      (ShortComplex.exact_iff_image_eq_kernel _).mp
        (quotient_exact F p (p + 1) n hp)
    rw [← heq]
    apply (Subobject.gc_exists_pullback m _ _).mp
    rw [← Subobject.exists_obj_top j, Subobject.exists_obj_comp,
      Subobject.exists_obj_top]
    have hj : j ≫ m = (F.step (p + 1)).arrow.f n :=
      congrArg (fun f => f.f n) (Subobject.ofLE_arrow (F.antitone_step hp))
    rw [hj]
    exact le_sup_right
  have hsat : (Subobject.pullback q).obj (F.complexBoundaries p n r) = W := by
    change (Subobject.pullback q).obj ((Subobject.«exists» q).obj W) = W
    exact pullback_exists_of_kernel_le q W hk
  rw [hsat]
  let ht := ha.trans hp
  let T := F.complexQuotient (p - r + 1) (p + 1) ht
  let t := (Subobject.ofLE (F.step p) (F.step (p - r + 1))
    (F.antitone_step ha)).f n ≫ (F.complexQuotientπ (p - r + 1) (p + 1) ht).f n
  change (Subobject.pullback t).obj (kernelSubobject (T.pOpcycles n)) = W
  apply le_antisymm
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff _ _ _).mpr
    apply (boundary_zero_iff F p n r ha _).mp
    have h := (pullback_factors_iff _ _ _).mp
      (Subobject.factors_self ((Subobject.pullback t).obj (kernelSubobject (T.pOpcycles n))))
    simpa only [t, Category.assoc] using
      (kernelSubobject_factors_iff _ _).mp h
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff _ _ _).mpr
    apply kernelSubobject_factors
    apply (boundary_zero_iff F p n r ha _).mpr
    exact (pullback_factors_iff _ _ _).mp (Subobject.factors_self W)

end CategoryTheory.DecreasingFiltration
