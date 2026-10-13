module

public import Sheaf.CategoryTheory.ExactCoupleConvergence

import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
import Sheaf.CategoryTheory.FiniteCoconeLimitCycles
import Sheaf.CategoryTheory.FiniteCoconeLimitBoundaries

/-! Canonical weak-convergence maps for a finite diagonal exact couple.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-weak-maps).
-/

@[expose] public section

universe u v
open CategoryTheory.Limits
namespace CategoryTheory.BigradedExactCouple

private theorem pullback_kernel
    {C : Type u} [Category.{v} C] [Abelian C] {D E F : C} (f : D ⟶ E) (g : E ⟶ F) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have h := (Subobject.factors_pullback_obj_iff f (kernelSubobject g) _).mp
      ((Subobject.le_iff_factors_arrow _ _).mp le_rfl)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp h
  · apply (Subobject.le_iff_factors_arrow _ _).mpr
    apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

private theorem kernel_cokernel
    {C : Type u} [Category.{v} C] [Abelian C] {D E : C} (f : D ⟶ E) :
    kernelSubobject (cokernel.π f) = imageSubobject f := by
  exact ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).exact_iff_image_eq_kernel.mp
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f))).symm

private theorem pullback_image
    {C : Type u} [Category.{v} C] [Abelian C] {D E : C} (f : D ⟶ E) (S : Subobject D) :
    (Subobject.pullback f).obj ((Subobject.«exists» f).obj S) =
      kernelSubobject f ⊔ S := by
  let T := (Subobject.«exists» f).obj S
  let P := (Subobject.pullback f).obj T
  let V := kernelSubobject f ⊔ S
  have hV : kernelSubobject (cokernel.π V.arrow) = V := by
    rw [kernel_cokernel, imageSubobject_mono, Subobject.mk_arrow]
  apply le_antisymm
  · change P ≤ V
    rw [← hV]
    apply le_kernelSubobject
    obtain ⟨e, he, hef⟩ := Subobject.exists_fac f S
    let := he
    obtain ⟨R, π, hπ, t, ht⟩ := surjective_up_to_refinements_of_epi e
      (Subobject.pullbackπ f T)
    let := hπ
    have hcomm : (π ≫ P.arrow) ≫ f = (t ≫ S.arrow) ≫ f := by
      rw [Category.assoc, ← (Subobject.isPullback f T).w,
        ← Category.assoc, ht, Category.assoc, hef, Category.assoc]
    have hdiff : (π ≫ P.arrow - t ≫ S.arrow) ≫ f = 0 := by
      rw [Preadditive.sub_comp, hcomm, sub_self]
    have hfac : V.Factors (π ≫ P.arrow - t ≫ S.arrow) :=
      Subobject.factors_of_le _ le_sup_left (kernelSubobject_factors f _ hdiff)
    have hS : V.Factors (t ≫ S.arrow) :=
      Subobject.factors_of_le _ le_sup_right (Subobject.factors_comp_arrow t)
    have hsum : V.Factors (π ≫ P.arrow) := by
      simpa only [sub_add_cancel] using Subobject.factors_add _ _ hfac hS
    have hz : (π ≫ P.arrow) ≫ cokernel.π V.arrow = 0 := by
      rw [← V.factorThru_arrow _ hsum, Category.assoc, cokernel.condition, comp_zero]
    apply (cancel_epi π).mp
    simpa only [Category.assoc, comp_zero] using hz
  · apply sup_le
    · apply (Subobject.le_iff_factors_arrow _ _).mpr
      apply (Subobject.factors_pullback_obj_iff _ _ _).mpr
      rw [kernelSubobject_arrow_comp]
      exact Subobject.factors_zero
    · exact (Subobject.gc_exists_pullback f).le_u_l S

private theorem quotient_kernel
    {C : Type u} [Category.{v} C] [Abelian C] {D E : C} (B Z : Subobject E) (h : B ≤ Z)
    (f : D ⟶ (Z : C)) :
    kernelSubobject (f ≫ cokernel.π (Subobject.ofLE B Z h)) =
      (Subobject.pullback (f ≫ Z.arrow)).obj B := by
  have hmap : (Subobject.map Z.arrow).obj
      (kernelSubobject (cokernel.π (Subobject.ofLE B Z h))) = B := by
    rw [kernel_cokernel, imageSubobject_mono, Subobject.map_mk]
    simp only [Subobject.ofLE_arrow, Subobject.mk_arrow]
  conv_rhs => rw [← hmap, Subobject.pullback_comp, Subobject.pullback_map_self,
    pullback_kernel]

private theorem initialG_kernel
    {C : Type u} [Category.{v} C] [Abelian C] (X : BigradedExactCouple C 0) (n p : ℤ) :
    kernelSubobject (X.initialG p (n - p)) = imageSubobject (X.alphaDiagonal n p) := by
  let a := X.alpha (p + 1) (n - (p + 1))
  let e := eqToIso (show X.D (p + 1 - 1) (n - (p + 1) + 1) =
    X.D p (n - p) by congr 1 <;> omega)
  have h : e.hom ≫ X.initialG p (n - p) =
      X.g (p + 1 - 1) (n - (p + 1) + 1) ≫
        eqToHom (by congr 1 <;> omega) := by
    dsimp [e, initialG]
    rw [← Category.assoc, ← eqToHom_naturality
      (fun pq : ℤ × ℤ ↦ X.g pq.1 pq.2)
      (show (p + 1 - 1, n - (p + 1) + 1) = (p, n - p) by ext <;> omega)]
    simp only [Category.assoc, eqToHom_trans]
  have hk : kernelSubobject (e.hom ≫ X.initialG p (n - p)) = imageSubobject a := by
    simp only [h, kernelSubobject_comp_mono]
    exact (X.exact_g (p + 1) (n - (p + 1))).symm
  have hm : (Subobject.map e.hom).obj
      (kernelSubobject (e.hom ≫ X.initialG p (n - p))) =
      kernelSubobject (X.initialG p (n - p)) := by
    rw [← pullback_kernel, ← Subobject.exists_iso_map,
      Subobject.exists_obj_pullback_obj]
  rw [← hm, hk, ← Subobject.exists_iso_map, Subobject.exists_obj_eq_imageSubobject,
    ← imageSubobject_comp_of_epi (factorThruImageSubobject a),
    imageSubobject_arrow_comp_assoc]
  rfl

/-- Under finite diagonal tails, any regular limiting tower has the canonical weak convergence.
Source: Stacks Project, Homology, Tag 012W.
(blueprint: lem-sp-finite-cocone-weak-maps).

Proof: Use the stationary cycle and boundary descriptions from the derived
exact-couple recursion. Exactness identifies stationary cycles with the image
of the initial `g`, so the canonical map from `D` onto the limiting quotient
is epi. Its kernel is the sum of the image of `Alpha` and the kernel of the
diagonal cocone map. The canonical map to the graded image of the cocone is
also epi by image factorisation. Pulling the next cocone image back along the
current map gives the same sum by the cocone equation and abelian
image/kernel calculus; exactness identifies the image of `Alpha` with the
kernel of `g`. Thus the two canonical epimorphisms have equal kernels, which
is precisely `WeaklyConvergesTo`. -/
theorem finiteCocone_weakMaps
    {C : Type u} [Category.{v} C] [Abelian C]
    (X : BigradedExactCouple C 0) (A : ∀ n : ℤ, X.AlphaColimit n)
    (hA : ∀ n : ℤ, ∃ a b : ℤ,
      (∀ P : ℤ, P ≤ a → IsIso ((A n).ι P)) ∧
      (∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P))))
    (L : X.LimitSubobjects) (hreg : X.IsRegular) : X.WeaklyConvergesTo L A := by
  have hzero : ∀ n : ℤ, ∃ b : ℤ, ∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)) := by
    intro n
    obtain ⟨a, b, _, hb⟩ := hA n
    exact ⟨b, hb⟩
  have hleft : ∀ n : ℤ, ∃ a : ℤ, ∀ P : ℤ, P ≤ a → IsIso ((A n).ι P) := by
    intro n
    obtain ⟨a, b, ha, _⟩ := hA n
    exact ⟨a, ha⟩
  intro p q
  let g := X.initialG p q
  let t := eqToHom (show X.D p q = X.D p (p + q - p) by congr 1; omega)
  let j := t ≫ (A (p + q)).ι p
  have hZ : L.Z p q = imageSubobject g := finiteCocone_limitCycles X L hreg hzero p q
  have hB : L.B p q = (Subobject.«exists» g).obj (kernelSubobject j) :=
    finiteCocone_limitBoundaries X A hleft L p q
  have hpage : Epi (X.toPageInfinity L p q) := by
    have : Epi ((L.Z p q).factorThru g (g_factors_limitCycles X L p q)) := by
      apply epi_of_imageSubobject_comp_arrow_eq
      simpa only [Subobject.factorThru_arrow] using hZ.symm
    dsimp [toPageInfinity]
    infer_instance
  have hgraded : Epi (X.toGradedPiece A p q) := by
    dsimp [toGradedPiece]
    infer_instance
  have hpageker : kernelSubobject (X.toPageInfinity L p q) =
      kernelSubobject g ⊔ kernelSubobject j := by
    dsimp only [toPageInfinity]
    rw [quotient_kernel, Subobject.factorThru_arrow, hB, pullback_image]
  have hgker : kernelSubobject g =
      (Subobject.pullback t).obj (imageSubobject (X.alphaDiagonal (p + q) p)) := by
    rw [← initialG_kernel, pullback_kernel]
    have hn := eqToHom_naturality (fun b : ℤ ↦ X.initialG p b)
      (show q = p + q - p by omega)
    change g ≫ eqToHom _ = t ≫ X.initialG p (p + q - p) at hn
    simp only [← hn, kernelSubobject_comp_mono]
  have hnext : (Subobject.«exists» j).obj (kernelSubobject g) =
      imageSubobject ((A (p + q)).ι (p + 1)) := by
    rw [hgker]
    dsimp only [j]
    rw [← Subobject.exists_obj_comp, Subobject.exists_obj_pullback_obj,
      Subobject.exists_obj_eq_imageSubobject,
      ← imageSubobject_comp_of_epi (factorThruImageSubobject
        (X.alphaDiagonal (p + q) p)), imageSubobject_arrow_comp_assoc, (A (p + q)).comm]
  have hgradedker : kernelSubobject (X.toGradedPiece A p q) =
      kernelSubobject j ⊔ kernelSubobject g := by
    simp only [toGradedPiece, imageFiltration, DecreasingFiltration.gradedPiece,
      ← Category.assoc, quotient_kernel]
    simp only [Category.assoc, imageSubobject_arrow_comp]
    change (Subobject.pullback j).obj (imageSubobject ((A (p + q)).ι (p + 1))) = _
    rw [← hnext, pullback_image]
  exact ⟨hpage, hgraded, hpageker.trans ((sup_comm _ _).trans hgradedker.symm)⟩

end CategoryTheory.BigradedExactCouple
