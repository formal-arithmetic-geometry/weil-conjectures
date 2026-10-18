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
  have hleft : ∀ n : ℤ, ∃ a : ℤ, ∀ P : ℤ, P ≤ a → IsIso ((A n).ι P) := by
    intro n
    obtain ⟨a, b, ha, hb⟩ := hA n
    exact ⟨a, ha⟩
  have hzero : ∀ n : ℤ, ∃ b : ℤ, ∀ P : ℤ, b ≤ P → IsZero (X.D P (n - P)) := by
    intro n
    obtain ⟨a, b, ha, hb⟩ := hA n
    exact ⟨b, hb⟩
  intro p q
  let n := p + q
  let t : X.D p q ⟶ X.D p (n - p) := eqToHom (by dsimp [n]; congr 1; omega)
  let j := t ≫ (A n).ι p
  let g := X.initialG p q
  let a : X.D (p + 1) (n - (p + 1)) ⟶ X.D p q :=
    X.alphaDiagonal n p ≫ eqToHom (by dsimp [n]; congr 1; omega)
  have ha : a ≫ t = X.alphaDiagonal n p := by
    simp [a, t]
  have hg : kernelSubobject g = imageSubobject a := by
    have hh := initialG_kernel X n p
    have htransport : t ≫ X.initialG p (n - p) =
        g ≫ eqToHom (by dsimp [n]; congr 1; omega) := by
      dsimp [t, g, initialG]
      rw [← Category.assoc, ← eqToHom_naturality
        (fun pq : ℤ × ℤ ↦ X.g pq.1 pq.2)
        (show (p, q) = (p, n - p) by dsimp [n]; ext <;> omega)]
      simp only [Category.assoc, eqToHom_trans]
    have hker : kernelSubobject g = kernelSubobject (t ≫ X.initialG p (n - p)) := by
      have hh' := congrArg (fun f : X.D p q ⟶ X.E p (n - p) ↦ kernelSubobject f)
        htransport
      exact (hh'.trans (kernelSubobject_comp_mono g _)).symm
    rw [hker, ← pullback_kernel, hh]
    have heq : (Subobject.«exists» t).obj (imageSubobject a) =
        imageSubobject (X.alphaDiagonal n p) := by
      rw [Subobject.exists_obj_eq_imageSubobject,
        ← imageSubobject_comp_of_epi (factorThruImageSubobject a),
        imageSubobject_arrow_comp_assoc, ha]
    rw [← heq, Subobject.exists_iso_map, Subobject.pullback_map_self]
  have hZ := finiteCocone_limitCycles X L hreg hzero p q
  have hB := finiteCocone_limitBoundaries X A hleft L p q
  let z := (L.Z p q).factorThru g (g_factors_limitCycles X L p q)
  have hz : z ≫ (L.Z p q).arrow = g := Subobject.factorThru_arrow _ _ _
  have hepi : Epi z := epi_of_imageSubobject_comp_arrow_eq z (by rw [hz]; exact hZ.symm)
  have hpage : Epi (X.toPageInfinity L p q) := by
    dsimp [toPageInfinity]
    exact epi_comp z _
  have hgraded : Epi (X.toGradedPiece A p q) := by
    dsimp [toGradedPiece]
    infer_instance
  refine ⟨hpage, hgraded, ?_⟩
  have hpageker : kernelSubobject (X.toPageInfinity L p q) =
      kernelSubobject g ⊔ kernelSubobject j := by
    rw [toPageInfinity, quotient_kernel, Subobject.factorThru_arrow, hB]
    exact pullback_image g (kernelSubobject j)
  have hgradedker : kernelSubobject (X.toGradedPiece A p q) =
      kernelSubobject j ⊔ kernelSubobject g := by
    have hk := quotient_kernel (imageSubobject ((A n).ι (p + 1)))
      (imageSubobject ((A n).ι p)) (X.imageFiltration_antitone n (A n) (by omega))
      (t ≫ factorThruImageSubobject ((A n).ι p))
    have hk' : kernelSubobject (X.toGradedPiece A p q) =
        (Subobject.pullback j).obj (imageSubobject ((A n).ι (p + 1))) := by
      simpa only [toGradedPiece, imageFiltration, PBCDecreasingFiltration.gradedPiece,
        Category.assoc, imageSubobject_arrow_comp] using hk
    rw [hk']
    change (Subobject.pullback j).obj (imageSubobject ((A n).ι (p + 1))) = _
    have him : imageSubobject ((A n).ι (p + 1)) =
        (Subobject.«exists» j).obj (imageSubobject a) := by
      rw [Subobject.exists_obj_eq_imageSubobject,
        ← imageSubobject_comp_of_epi (factorThruImageSubobject a),
        imageSubobject_arrow_comp_assoc]
      dsimp [j]
      rw [← Category.assoc, ha, (A n).comm]
    rw [him, pullback_image, hg]
  exact hpageker.trans (by rw [sup_comm]; exact hgradedker.symm)

end CategoryTheory.BigradedExactCouple
