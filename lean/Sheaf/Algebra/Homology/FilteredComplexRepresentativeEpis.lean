/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Epimorphic cycle representative maps

Source: Stacks Project, Tag 012K, displayed cycle-boundary formulas.
(blueprint: lem-sp-filtered-complex-representative-epis)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DecreasingFiltration

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K : CochainComplex C ℤ}

private theorem quotient_epi (F : DecreasingFiltration K) (p b n : ℤ) (h : p ≤ b) :
    Epi ((F.complexQuotientπ p b h).f n) := by
  change Epi ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
    (cokernel.π (Subobject.ofLE (F.step b) (F.step p) (F.antitone_step h))))
  infer_instance

private theorem quotient_kernel (F : DecreasingFiltration K) (p b n : ℤ) (h : p ≤ b) :
    kernelSubobject ((F.complexQuotientπ p b h).f n) =
      imageSubobject ((Subobject.ofLE (F.step b) (F.step p)
        (F.antitone_step h)).f n) := by
  let l := Subobject.ofLE (F.step b) (F.step p) (F.antitone_step h)
  have h := (ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk l (cokernel.π l) (cokernel.condition l))
    (cokernelIsCokernel l)).map (HomologicalComplex.eval C (ComplexShape.up ℤ) n)
  exact ((ShortComplex.exact_iff_image_eq_kernel _).mp h).symm

private theorem step_pullback_next (F : DecreasingFiltration K) (p b n : ℤ) (h : p ≤ b) :
    (Subobject.pullback ((F.step p).arrow.f n)).obj (F.complexStep b n) =
      imageSubobject ((Subobject.ofLE (F.step b) (F.step p)
        (F.antitone_step h)).f n) := by
  have : Mono ((F.step p).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
    infer_instance
  let l := Subobject.ofLE (F.step b) (F.step p) (F.antitone_step h)
  have hl : l.f n ≫ (F.step p).arrow.f n = (F.step b).arrow.f n :=
    congrArg (fun f ↦ f.f n) (Subobject.ofLE_arrow (F.antitone_step h))
  have hex {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
      (Subobject.«exists» g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject f),
      ← Category.assoc, imageSubobject_arrow_comp]
  dsimp only [complexStep]
  simp only [← hl]
  rw [← hex, Subobject.exists_iso_map ((F.step p).arrow.f n),
    Subobject.pullback_map_self]

private theorem step_next_image (F : DecreasingFiltration K) (p b n : ℤ) (h : p ≤ b) :
    F.complexStep b n =
      (Subobject.«exists» ((F.step p).arrow.f n)).obj
        (imageSubobject ((Subobject.ofLE (F.step b) (F.step p)
          (F.antitone_step h)).f n)) := by
  let l := Subobject.ofLE (F.step b) (F.step p) (F.antitone_step h)
  have hl : l.f n ≫ (F.step p).arrow.f n = (F.step b).arrow.f n :=
    congrArg (fun f ↦ f.f n)
      (Subobject.ofLE_arrow (F.antitone_step h))
  have hex {A B D : C} (f : A ⟶ B) (g : B ⟶ D) :
      (Subobject.«exists» g).obj (imageSubobject f) = imageSubobject (f ≫ g) := by
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject f),
      ← Category.assoc, imageSubobject_arrow_comp]
  dsimp only [complexStep]
  rw [hex, hl]

private theorem exists_pullback_of_le {A B : C} (m : A ⟶ B) [Mono m]
    (P : Subobject B) (h : P ≤ Subobject.mk m) :
    (Subobject.«exists» m).obj ((Subobject.pullback m).obj P) = P := by
  rw [Subobject.exists_iso_map]
  have hm := Subobject.inf_eq_map_pullback' (MonoOver.mk m) P
  change Subobject.mk m ⊓ P = (Subobject.map m).obj ((Subobject.pullback m).obj P) at hm
  rw [← hm, inf_eq_right.mpr h]

/-- Cycle representatives cover both the filtered cycles and the cycles of the quotient.
Source: Stacks Project, Tag 012K, displayed formula for Z_r.
(blueprint: lem-sp-filtered-complex-representative-epis)

Proof: Evaluation preserves the cokernel defining S, so its projection q is epic
and has kernel F^{p+r}. Its inverse image of ker(d_S) consists of the x in F^p
such that dx belongs to F^{p+r}, namely R. Pulling back the epic q along the cycle
inclusion is epic in an abelian category; this gives g and its equation. The image
of R under the graded projection is Z: adding F^{p+1} to R before projecting does
not change the image, since the graded projection kills F^{p+1}. The image
factorization therefore gives the epic z and its equation. These arguments use
images, inverse images and pullbacks of epimorphisms, hence work in every abelian
category, with no elementwise or finiteness assumption. -/
theorem filteredComplex_representative_epis (F : DecreasingFiltration K)
    (p n r : ℤ) (hs : p ≤ p + r) :
    let R := F.complexCycleRepresentatives p n r
    let Z := F.complexCycles p n r
    let S := F.complexQuotient p (p + r) hs
    ∃ (z : (R : C) ⟶ (Z : C)) (g : (R : C) ⟶ S.cycles n),
      Epi z ∧ Epi g ∧
      z ≫ Z.arrow = R.arrow ≫
        (F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))).f n ∧
      g ≫ S.iCycles n = R.arrow ≫ (F.complexQuotientπ p (p + r) hs).f n := by
  have : Mono ((F.step p).arrow.f n) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).map (F.step p).arrow)
    infer_instance
  have : Mono ((F.step p).arrow.f (n + 1)) := by
    change Mono ((HomologicalComplex.eval C (ComplexShape.up ℤ) (n + 1)).map (F.step p).arrow)
    infer_instance
  have := quotient_epi F p (p + r) n hs
  let R := F.complexCycleRepresentatives p n r
  let S := F.complexQuotient p (p + r) hs
  let q := F.complexQuotientπ p (p + r) hs
  let q₀ := F.complexQuotientπ p (p + 1) (Int.le_add_one (show p ≤ p from le_rfl))
  have hR : R = (Subobject.pullback (q.f n)).obj
      (kernelSubobject (S.d n (n + 1))) := by
    dsimp only [R, complexCycleRepresentatives]
    have h_inf {A B : C} (f : A ⟶ B) (S T : Subobject B) :
        (Subobject.pullback f).obj (S ⊓ T) =
          (Subobject.pullback f).obj S ⊓ (Subobject.pullback f).obj T :=
      (Subobject.gc_exists_pullback f).u_inf
    rw [h_inf]
    have hself : (Subobject.pullback ((F.step p).arrow.f n)).obj
        (F.complexStep p n) = ⊤ := by
      rw [complexStep, imageSubobject_mono, Subobject.pullback_self]
    rw [hself, top_inf_eq, ← Subobject.pullback_comp]
    rw [(F.step p).arrow.comm, Subobject.pullback_comp,
      step_pullback_next F p (p + r) (n + 1) hs,
      ← quotient_kernel F p (p + r) (n + 1) hs]
    have hpk {A B D : C} (f : A ⟶ B) (g : B ⟶ D) (k : A ⟶ D)
        (hk : f ≫ g = k) :
        (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject k := by
      subst k
      apply le_antisymm
      · apply le_kernelSubobject
        have hf := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
          ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
        simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
      · apply (Subobject.le_iff_factors_arrow _ _).mpr
        apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
        apply kernelSubobject_factors
        simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)
    rw [hpk _ _ _ rfl]
    change kernelSubobject ((F.step p : CochainComplex C ℤ).d n (n + 1) ≫
      q.f (n + 1)) = _
    rw [← q.comm, ← hpk _ _ _ rfl]
  have hZ : imageSubobject (R.arrow ≫ q₀.f n) = F.complexCycles p n r := by
    let A := F.complexStep p n ⊓ (Subobject.pullback (K.d n (n + 1))).obj
      (F.complexStep (p + r) (n + 1))
    let L := imageSubobject ((Subobject.ofLE (F.step (p + 1)) (F.step p)
      (F.antitone_step (show p ≤ p + 1 by omega))).f n)
    have hA : (Subobject.«exists» ((F.step p).arrow.f n)).obj R = A := by
      apply exists_pullback_of_le
      exact (inf_le_left : A ≤ F.complexStep p n).trans_eq (imageSubobject_mono _)
    have hJ := step_next_image F p (p + 1) n (show p ≤ p + 1 by omega)
    unfold complexCycles
    change imageSubobject (R.arrow ≫ q₀.f n) =
      (Subobject.«exists» (q₀.f n)).obj
        ((Subobject.pullback ((F.step p).arrow.f n)).obj (A ⊔ _))
    rw [← hA, hJ, ← Subobject.exists_obj_sup,
      Subobject.exists_iso_map ((F.step p).arrow.f n), Subobject.pullback_map_self,
      Subobject.exists_obj_sup, Subobject.exists_obj_eq_imageSubobject,
      Subobject.exists_obj_eq_imageSubobject]
    have hzero : L.arrow ≫ q₀.f n = 0 := by
      apply imageSubobject_arrow_comp_eq_zero
      exact congrArg (fun f ↦ f.f n) (cokernel.condition
        (Subobject.ofLE (F.step (p + 1)) (F.step p)
          (F.antitone_step (show p ≤ p + 1 by omega))))
    rw [hzero, imageSubobject_zero, sup_bot_eq]
  let z := factorThruImageSubobject (R.arrow ≫ q₀.f n) ≫
    (Subobject.isoOfEq _ _ hZ).hom
  let eR := Subobject.isoOfEq _ _ hR
  let P := kernelSubobject (S.d n (n + 1))
  let eP : (P : C) ≅ S.cycles n :=
    kernelSubobjectIso _ ≪≫ (kernelIsKernel _).conePointUniqueUpToIso
      (S.cyclesIsKernel n (n + 1) (by simp))
  let g := eR.hom ≫ Subobject.pullbackπ (q.f n) P ≫ eP.hom
  have h_epi : Epi (Subobject.pullbackπ (q.f n) P) :=
    Abelian.epi_fst_of_isLimit P.arrow (q.f n)
      (Subobject.isPullback (q.f n) P).isLimit
  refine ⟨z, g, inferInstance, inferInstance, ?_, ?_⟩
  · dsimp only [z]
    simp only [Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
      imageSubobject_arrow_comp]
    rfl
  · have heP : eP.hom ≫ S.iCycles n = P.arrow := by
      dsimp only [eP, Iso.trans_hom]
      rw [Category.assoc]
      have hh := (kernelIsKernel (S.d n (n + 1))).conePointUniqueUpToIso_hom_comp
        (S.cyclesIsKernel n (n + 1) (by simp)) WalkingParallelPair.zero
      change _ ≫ S.iCycles n = kernel.ι (S.d n (n + 1)) at hh
      rw [hh, kernelSubobject_arrow]
    dsimp only [g]
    rw [Category.assoc, Category.assoc, heP,
      (Subobject.isPullback (q.f n) P).w, ← Category.assoc]
    simp only [eR, P, Subobject.isoOfEq_hom, Subobject.ofLE_arrow]
    rfl

end CategoryTheory.DecreasingFiltration
