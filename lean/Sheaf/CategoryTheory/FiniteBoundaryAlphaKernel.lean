/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

import Mathlib.CategoryTheory.Abelian.Refinements
import Sheaf.CategoryTheory.DerivedCoupleExact
import Sheaf.CategoryTheory.FiniteCycleDerivedComparison
import Sheaf.CategoryTheory.FiniteCycleFormula
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits

/-! # Finite boundaries as outgoing alpha kernels

Source: Stacks Project, Tag 011T, finite exact-couple boundary formula.
(blueprint: lem-sp-finite-boundary-alpha-kernel)
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

private theorem incomingAlphaIter_succ
    {C : Type u} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0)
    (n : ℕ) (p q : ℤ) :
    X.incomingAlphaIter (n + 1) p q =
      X.alpha (p + (n + 1 : ℕ)) (q - (n + 1 : ℕ)) ≫
        eqToHom (by congr 1 <;> omega) ≫ X.incomingAlphaIter n p q := by
  apply eq_of_heq
  dsimp [incomingAlphaIter, alphaIter]
  simp only [Category.assoc]
  apply heq_comp rfl rfl rfl HEq.rfl
  simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rw [heq_eqToHom_comp_iff]
  congr! 1 <;> omega

private theorem alphaIter_image
    {C : Type u} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0)
    (r : ℕ) (p q : ℤ) :
    imageSubobject (X.alphaIter r p q) =
      imageSubobject (X.incomingAlphaIter r (p - r) (q + r)) := by
  have h : X.incomingAlphaIter r (p - r) (q + r) =
      eqToHom (by congr 1 <;> omega) ≫ X.alphaIter r p q := by
    apply eq_of_heq
    unfold incomingAlphaIter
    simp only [comp_eqToHom_heq_iff]
    apply HEq.trans ?_ (eqToHom_comp_heq _ _).symm
    congr! 1 <;> omega
  rw [h, imageSubobject_iso_comp]

private theorem alphaIter_succ_append
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    X.alphaIter (r + 1) p q = X.alphaIter r p q ≫
      X.alpha (p - r) (q + r) ≫ eqToHom (by congr 1 <;> omega) := by
  induction r generalizing p q with
  | zero =>
    apply eq_of_heq
    simp only [alphaIter, ← Category.assoc, comp_eqToHom_heq_iff,
      heq_comp_eqToHom_iff]
    rw [heq_eqToHom_comp_iff]
    congr! 1 <;> omega
  | succ r ih =>
    rw [alphaIter, ih, alphaIter]
    apply eq_of_heq
    simp only [Category.assoc]
    apply heq_comp rfl rfl rfl HEq.rfl
    simp only [← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
    simp only [Category.assoc]
    apply heq_comp rfl rfl (by congr 1 <;> omega) HEq.rfl
    rw [heq_eqToHom_comp_iff]
    congr! 1 <;> omega

private theorem incoming_d_image
    {C : Type u} [Category.{v} C] [Abelian C]
    {s : ℕ} (Y : BigradedExactCouple C s) (p q : ℤ) :
    imageSubobject (Y.dInto p q) =
      (Subobject.«exists»
        (Y.g (p - s) (q + s) ≫ eqToHom (by congr 1 <;> omega))).obj
        (kernelSubobject (Y.alpha (p - s) (q + s))) := by
  have transport_exact (a b t w : ℤ) (ht : a + 2 = t) (hw : b - 1 = w) :
      imageSubobject (Y.f a b ≫ eqToHom (congrArg₂ Y.D ht hw)) =
        kernelSubobject (Y.alpha t w) := by
    subst t
    subst w
    simpa using Y.exact_alpha a b
  have hf := transport_exact (p - s - 2) (q + s + 1) (p - s) (q + s)
    (by omega) (by omega)
  rw [Subobject.exists_obj_eq_imageSubobject, ← hf]
  rw [← imageSubobject_comp_of_epi (factorThruImageSubobject
    (Y.f (p - s - 2) (q + s + 1) ≫ eqToHom (by congr 1 <;> omega))),
    imageSubobject_arrow_comp_assoc]
  congr 1
  have transport (a b t w p' q' : ℤ) (ht : a + 2 = t) (hw : b - 1 = w)
      (hp : t + s = p') (hq : w - s = q') :
      Y.d a b ≫ eqToHom (show Y.E (a + 2 + s) (b - 1 - s) =
          Y.E p' q' by congr 1 <;> omega) =
        (Y.f a b ≫ eqToHom (congrArg₂ Y.D ht hw)) ≫
          Y.g t w ≫ eqToHom (congrArg₂ Y.E hp hq) := by
    subst t
    subst w
    subst p'
    subst q'
    simp [d]
  exact transport (p - s - 2) (q + s + 1) (p - s) (q + s) p q
    (by omega) (by omega) (by omega) (by omega)

/-- Collect the image and cycle maps for the boundary induction.

Source: Stacks Project, Tags 011R, 011S and 0AMJ. The image formula for the iterated
mono inclusion identifies its domain with the image of `alphaIter`; compose this
isomorphism with the image epimorphism to construct `e`. Alpha compatibility and
monicity identify both displayed kernels. The finite cycle formula gives the lift
`c` since initial g followed by f is zero; `finiteCycle_derived_comparison` gives
its projection equation. Finally `incoming_d_image` gives the incoming boundary. -/
private theorem iteratedG_presentation
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    let Y := X.pageCouple r
    let g : Y.D (p - r) (q + r) ⟶ Y.E p q :=
      Y.g (p - r) (q + r) ≫ eqToHom (by congr 1 <;> omega)
    ∃ (e : X.D p q ⟶ Y.D (p - r) (q + r))
      (c : X.D p q ⟶ (X.cycleBoundaryTower.Z r p q : C)),
      Epi e ∧
      kernelSubobject e = kernelSubobject (X.alphaIter r p q) ∧
      kernelSubobject (e ≫ Y.alpha (p - r) (q + r)) =
        kernelSubobject (X.alphaIter (r + 1) p q) ∧
      c ≫ (X.cycleBoundaryTower.Z r p q).arrow = X.initialG p q ∧
      c ≫ X.cycleBoundaryTower.projection r p q = e ≫ g ∧
      imageSubobject (Y.dInto p q) =
        (Subobject.«exists» g).obj (kernelSubobject (Y.alpha (p - r) (q + r))) := by
  dsimp only
  obtain ⟨A, I, hA0, hAs, hI0, hIs, hmono, himage, hcomm⟩ := X.pageCouple_image_prefix
  have hA : ∀ (n : ℕ) (a b : ℤ), A n a b = X.incomingAlphaIter n a b := by
    intro n a b
    induction n with
    | zero =>
      rw [hA0]
      simp only [incomingAlphaIter, alphaIter, eqToHom_trans]
    | succ n ih => rw [hAs, ih, incomingAlphaIter_succ]
  have hi := hmono r (p - r) (q + r)
  have him : Subobject.mk (imageSubobject (X.alphaIter r p q)).arrow =
      Subobject.mk (I r (p - r) (q + r)) := by
    rw [Subobject.mk_arrow, ← imageSubobject_mono, himage, hA, alphaIter_image]
  let j := Subobject.isoOfMkEqMk (imageSubobject (X.alphaIter r p q)).arrow
    (I r (p - r) (q + r)) him
  let e := factorThruImageSubobject (X.alphaIter r p q) ≫ j.hom
  have hepi : Epi e := by dsimp [e]; infer_instance
  have he : e ≫ I r (p - r) (q + r) = X.alphaIter r p q := by
    dsimp [e, j]
    simp only [Category.assoc, Subobject.isoOfMkEqMk_hom, Subobject.ofMkLEMk_comp,
      imageSubobject_arrow_comp]
  have hg : (X.cycleBoundaryTower.Z r p q).Factors (X.initialG p q) := by
    rw [finiteCycle_formula]
    apply pullback_factors
    have hgf : X.initialG p q ≫ X.f p q = 0 := by
      rw [initialG, Category.assoc,
        ← eqToHom_naturality (fun pq : ℤ × ℤ ↦ X.f pq.1 pq.2)
          (show (p + (0 : ℕ), q - (0 : ℕ)) = (p, q) by ext <;> simp),
        ← Category.assoc, X.f_g_zero, zero_comp]
    rw [hgf]
    exact Subobject.factors_zero
  let c := (X.cycleBoundaryTower.Z r p q).factorThru (X.initialG p q) hg
  refine ⟨e, c, hepi, ?_, ?_, by simp [c], ?_, ?_⟩
  · exact (kernelSubobject_comp_mono e (I r (p - r) (q + r))).symm.trans
      (congrArg (fun f ↦ kernelSubobject f) he)
  · have hnext := hmono r ((p - r) - 1) ((q + r) + 1)
    have heq : (e ≫ (X.pageCouple r).alpha (p - r) (q + r)) ≫
        I r ((p - r) - 1) ((q + r) + 1) ≫
          eqToHom (by congr 1 <;> omega) = X.alphaIter (r + 1) p q := by
      rw [Category.assoc, ← Category.assoc ((X.pageCouple r).alpha _ _), hcomm,
        ← Category.assoc e, ← Category.assoc e, he, alphaIter_succ_append]
      rw [Category.assoc]
    have hk := congrArg (fun f ↦ kernelSubobject f) heq
    simpa only [kernelSubobject_comp_mono] using hk
  · exact (X.finiteCycle_derived_comparison I hI0 hIs hmono r p q hg e he).symm
  · exact incoming_d_image (X.pageCouple r) p q

private theorem factors_of_epi {C : Type u} [Category.{v} C] [Abelian C]
    {A T E : C} (S : Subobject E) (x : T ⟶ E) (π : A ⟶ T) [Epi π]
    (h : S.Factors (π ≫ x)) : S.Factors x := by
  have hz : x ≫ cokernel.π S.arrow = 0 := by
    apply (cancel_epi π).mp
    rw [← Category.assoc, ← S.factorThru_arrow (π ≫ x) h, Category.assoc,
      cokernel.condition, comp_zero, comp_zero]
  rw [← Abelian.monoLift_comp S.arrow x hz]
  exact Subobject.factors_comp_arrow _

private theorem lift_image {C : Type u} [Category.{v} C] [Abelian C]
    {A T E : C} (f : A ⟶ E) (x : T ⟶ E)
    (h : (imageSubobject f).Factors x) :
    ∃ (T' : C) (π : T' ⟶ T), Epi π ∧ ∃ y : T' ⟶ A, π ≫ x = y ≫ f := by
  obtain ⟨T', π, hπ, y, hy⟩ := surjective_up_to_refinements_of_epi
    (factorThruImageSubobject f) ((imageSubobject f).factorThru x h)
  refine ⟨T', π, hπ, y, ?_⟩
  simpa only [Category.assoc, Subobject.factorThru_arrow,
    imageSubobject_arrow_comp] using hy =≫ (imageSubobject f).arrow

private theorem pullback_image_kernel {C : Type u} [Category.{v} C] [Abelian C]
    {D R A Z P : C} (e : D ⟶ R) [Epi e] (a : R ⟶ A)
    (c : D ⟶ Z) (π : Z ⟶ P) (g : R ⟶ P)
    (hcomm : c ≫ π = e ≫ g)
    (hker : kernelSubobject π ≤
      (Subobject.«exists» c).obj (kernelSubobject (e ≫ a))) :
    (Subobject.pullback π).obj
        ((Subobject.«exists» g).obj (kernelSubobject a)) =
      (Subobject.«exists» c).obj (kernelSubobject (e ≫ a)) := by
  let K := kernelSubobject (e ≫ a)
  let S := (Subobject.«exists» c).obj K
  let L := (Subobject.pullback π).obj
    ((Subobject.«exists» g).obj (kernelSubobject a))
  apply le_antisymm
  · apply Subobject.le_of_factors
    have hx : (imageSubobject ((kernelSubobject a).arrow ≫ g)).Factors
        (L.arrow ≫ π) := by
      rw [← Subobject.exists_obj_eq_imageSubobject]
      exact (pullback_factors_iff π _ _).mp (Subobject.factors_self L)
    obtain ⟨T₁, ρ₁, hρ₁, y, hy⟩ := lift_image _ _ hx
    let : Epi ρ₁ := hρ₁
    obtain ⟨T₂, ρ₂, hρ₂, z, hz⟩ := surjective_up_to_refinements_of_epi e
      (y ≫ (kernelSubobject a).arrow)
    let : Epi ρ₂ := hρ₂
    have hza : z ≫ (e ≫ a) = 0 := by
      rw [← Category.assoc, ← hz]
      simp
    have hzc : S.Factors (z ≫ c) := by
      dsimp only [S]
      rw [Subobject.exists_obj_eq_imageSubobject]
      have hf := kernelSubobject_factors (e ≫ a) z hza
      rw [← K.factorThru_arrow z hf, Category.assoc]
      exact imageSubobject_factors_comp_self _ _
    let w := ρ₂ ≫ ρ₁ ≫ L.arrow - z ≫ c
    have hw : w ≫ π = 0 := by
      dsimp [w]
      rw [Preadditive.sub_comp]
      rw [Category.assoc z, hcomm, ← Category.assoc z, ← hz]
      simpa only [Category.assoc, sub_self] using
        congrArg (fun t ↦ ρ₂ ≫ t - ρ₂ ≫ (y ≫ (kernelSubobject a).arrow ≫ g)) hy
    have hwS : S.Factors w :=
      Subobject.factors_of_le _ hker (kernelSubobject_factors π w hw)
    have hall : S.Factors (ρ₂ ≫ ρ₁ ≫ L.arrow) := by
      have hh := Subobject.factors_add w (z ≫ c) hwS hzc
      simpa only [w, sub_add_cancel] using hh
    exact factors_of_epi S L.arrow (ρ₂ ≫ ρ₁) (by
      simpa only [Category.assoc] using hall)
  · apply (Subobject.exists_le_iff c K L).mpr
    apply pullback_factors
    have hk : (kernelSubobject a).Factors (K.arrow ≫ e) := by
      apply kernelSubobject_factors
      simpa only [Category.assoc] using kernelSubobject_arrow_comp (e ≫ a)
    rw [Category.assoc, hcomm, ← Category.assoc]
    rw [Subobject.exists_obj_eq_imageSubobject,
      ← (kernelSubobject a).factorThru_arrow (K.arrow ≫ e) hk, Category.assoc]
    exact imageSubobject_factors_comp_self _ _

/-- Finite boundaries are the initial g-image of the outgoing iterated alpha kernel.
Source: Stacks Project, Tag 011T, exact-couple boundary formula, and Tag 0AMJ.
(blueprint: lem-sp-finite-boundary-alpha-kernel).

Proof: Induct on r using the canonical tower's successor boundary and projection
formulas. At zero alphaIter is an isomorphism, so its kernel and the tower's
boundary are zero. Recursively compose image projections to obtain an epimorphism
from D(p,q) onto the r-th derived D at (p-r,q+r). The canonical inclusion of
this derived D into the original D is mono and its composite with that epimorphism
is alphaIter r. The derived alpha and g restriction equations imply that the next
alpha kills a representative exactly when alphaIter (r+1) does, and that its g
image equals the projection of initialG of that representative into the r-th page.
Exactness identifies the incoming differential image with derived g of the kernel
of derived alpha. Lift a representative of the successor boundary first through
this image and then through the iterated image epimorphism, after epimorphic
refinements. Its lift is killed by alphaIter (r+1). The difference from its
initialG image has zero projection and hence lies in the old boundary. By induction
that difference is initialG of an element killed by alphaIter r, after refinement.
Adding the two lifts gives an element killed by alphaIter (r+1) representing the
original successor boundary. Conversely an element killed by alphaIter (r+1)
projects to a derived-alpha kernel, so its g image is an incoming differential
boundary; the tower's successor pullback puts its initialG image in B(r+1).
These two factorization tests descend along the epimorphic refinements, since
subobjects in an abelian category are kernels of their cokernels, and prove equality.
The argument uses no colimit, tail, regularity or vanishing hypothesis. -/
theorem finiteBoundary_alphaKernel
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (r : ℕ) (p q : ℤ) :
    X.cycleBoundaryTower.B r p q =
      (Subobject.«exists» (X.initialG p q)).obj (kernelSubobject (X.alphaIter r p q)) := by
  induction r with
  | zero =>
    rw [X.cycleBoundaryTower.B_zero]
    have hk : kernelSubobject (X.alphaIter 0 p q) = ⊥ := by
      change kernelSubobject (eqToHom _) = ⊥
      exact Subobject.mk_eq_bot_iff_zero.mpr (kernel.ι_of_mono _)
    rw [hk, Subobject.exists_obj_eq_imageSubobject]
    simp
  | succ r ih =>
    let T := X.cycleBoundaryTower
    let Y := X.pageCouple r
    let g : Y.D (p - r) (q + r) ⟶ Y.E p q :=
      Y.g (p - r) (q + r) ≫ eqToHom (by congr 1 <;> omega)
    obtain ⟨e, c, he, hke, hka, hc, hcp, hd⟩ := iteratedG_presentation X r p q
    let : Epi e := he
    let S := (Subobject.«exists» c).obj
      (kernelSubobject (e ≫ Y.alpha (p - r) (q + r)))
    have hker : kernelSubobject (T.projection r p q) ≤ S := by
      apply (Subobject.map_obj_le_map_obj_iff (T.Z r p q).arrow _ _).mp
      have hleft : (Subobject.map (T.Z r p q).arrow).obj
          (kernelSubobject (T.projection r p q)) = T.B r p q := by
        rw [T.projection_kernel, Subobject.map_mk]
        simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
      rw [hleft]
      have hright : (Subobject.map (T.Z r p q).arrow).obj S =
          (Subobject.«exists» (X.initialG p q)).obj
            (kernelSubobject (e ≫ Y.alpha (p - r) (q + r))) := by
        rw [← Subobject.exists_iso_map, Subobject.exists_obj_comp, hc]
      rw [hright, ih, ← hke]
      exact (Subobject.«exists» (X.initialG p q)).monotone
        (kernelSubobject_comp_le e (Y.alpha (p - r) (q + r)))
    rw [T.B_succ, hd, pullback_image_kernel e _ c _ g hcp hker]
    rw [Subobject.exists_obj_comp, hc, hka]

end CategoryTheory.BigradedExactCouple
