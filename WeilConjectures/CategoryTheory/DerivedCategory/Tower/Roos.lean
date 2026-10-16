/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Products
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The Roos sequence of a tower and derived limits of towers of K-injective complexes

Let `F : ℕᵒᵖ ⥤ C` be a tower in a preadditive category, with a limit cone `c` and a product
`∏ₙ Fₙ`, and let `t = towerShift` be the endomorphism of `∏ₙ Fₙ` with components
`∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. Then

* `lim F ⟶ ∏ₙ Fₙ` is a kernel of `1 - t` (`CategoryTheory.Limits.isLimitKernelForkTowerShift`);
* if every transition map `Fₙ₊₁ ⟶ Fₙ` is a split epimorphism, so is `1 - t`
  (`CategoryTheory.Limits.isSplitEpi_sub_towerShift`).

In an abelian category this is the *Roos sequence* `0 ⟶ lim F ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ 0`, short exact
when the transitions are split epimorphisms (`CategoryTheory.Limits.shortExact_towerShift`).

Applied degreewise to a tower `G` of cochain complexes, it gives the main result of this file,
`DerivedCategory.isHomotopyLimit_mapCone_Q`: if the complexes `Gₙ` are K-injective and the
transition maps are degreewise split epimorphisms (for instance if `G` comes from a complex of
injective towers), then the image in the derived category of the limit cone `lim G ⟶ Gₙ` is a
homotopy limit cone (`CategoryTheory.Pretriangulated.IsHomotopyLimit`): the short exact Roos
sequence of complexes gives a distinguished triangle
`Q (lim G) ⟶ Q (∏ Gₙ) ⟶ Q (∏ Gₙ) ⟶ Q (lim G)⟦1⟧`, and `Q (∏ Gₙ)` is a product in the derived
category because the `Gₙ` are K-injective. This is the computation of the derived limit by a
K-injective model (Stacks, Tag 070M).
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

namespace CategoryTheory.Limits

variable {C : Type*} [Category C] [Preadditive C] {F : ℕᵒᵖ ⥤ C}
  {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P)

@[reassoc (attr := simp)]
lemma lift_comp_sub_towerShift (c : Cone F) :
    Fan.IsLimit.lift hP (fun n ↦ c.π.app (op n)) ≫ (𝟙 _ - towerShift hP) = 0 := by
  simp [Preadditive.comp_sub]

/-- The maps `lim F ⟶ Fₙ` exhibit `lim F ⟶ ∏ₙ Fₙ` as a kernel of `1 - t`. -/
noncomputable def isLimitKernelForkTowerShift {c : Cone F} (hc : IsLimit c) :
    IsLimit (KernelFork.ofι _ (lift_comp_sub_towerShift hP c)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} g hg ↦ hc.lift
      { pt := W
        π := NatTrans.ofOpSequence (fun n ↦ g ≫ P.proj n) fun n ↦ by
          have := hg =≫ P.proj n
          simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
            Category.assoc, towerShift_proj, zero_comp, sub_eq_zero] at this
          simpa using this })
    (fun {W} g hg ↦ Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      simp only [Category.assoc, Fan.IsLimit.fac, IsLimit.fac]
      simp)
    (fun {W} g hg m hm ↦ hc.hom_ext fun n ↦ by
      obtain ⟨n⟩ := n
      rw [IsLimit.fac]
      simpa using hm =≫ P.proj n)

/-- The recursively defined components `yₙ : ∏ Fₙ ⟶ Fₙ` of a section of `1 - t`, given
sections `σₙ` of the transition maps: `y₀ = 0` and `yₙ₊₁ = (yₙ - prₙ) ≫ σₙ`. -/
noncomputable def towerShiftSectionAux (σ : ∀ n : ℕ, F.obj (op n) ⟶ F.obj (op (n + 1))) :
    ∀ n : ℕ, P.pt ⟶ F.obj (op n)
  | 0 => 0
  | n + 1 => (towerShiftSectionAux σ n - P.proj n) ≫ σ n

/-- If the transition maps of a tower are split epimorphisms, then `1 - t : ∏ Fₙ ⟶ ∏ Fₙ` is a
split epimorphism: given `y`, the equations `xₙ - t(xₙ₊₁) = yₙ` are solved recursively by
`x₀ = 0` and `xₙ₊₁ = σₙ (xₙ - yₙ)`. -/
lemma isSplitEpi_sub_towerShift (h : ∀ n : ℕ, IsSplitEpi (F.map (homOfLE n.le_succ).op)) :
    IsSplitEpi (𝟙 _ - towerShift hP) := by
  let σ (n : ℕ) := section_ (F.map (homOfLE n.le_succ).op)
  refine IsSplitEpi.mk' ⟨Fan.IsLimit.lift hP (towerShiftSectionAux (P := P) σ), ?_⟩
  refine Fan.IsLimit.hom_ext hP _ _ fun n ↦ ?_
  simp only [Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp, Category.assoc,
    towerShift_proj, Fan.IsLimit.fac, Fan.IsLimit.fac_assoc, Category.id_comp]
  simp [towerShiftSectionAux, σ, Preadditive.sub_comp]

/-- The Roos sequence `0 ⟶ lim F ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ ⟶ 0` of a tower in an abelian
category whose transition maps are split epimorphisms is short exact. -/
lemma shortExact_towerShift {A : Type*} [Category A] [Abelian A] {F : ℕᵒᵖ ⥤ A}
    {P : Fan fun n : ℕ ↦ F.obj (op n)} (hP : IsLimit P) {c : Cone F} (hc : IsLimit c)
    (h : Epi (𝟙 _ - towerShift hP)) :
    (ShortComplex.mk _ _ (lift_comp_sub_towerShift hP c)).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (isLimitKernelForkTowerShift hP hc)
  mono_f := by
    have := mono_of_isLimit_fork (isLimitKernelForkTowerShift hP hc)
    simpa using this
  epi_g := h

end CategoryTheory.Limits

namespace DerivedCategory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Abelian.HasKInjectiveResolutions A] [HasLimitsOfShape (Discrete ℕ) A]

omit [HasDerivedCategory A] [Abelian.HasKInjectiveResolutions A] in
/-- The degree `p` component of the transition endomorphism of a product of complexes is the
transition endomorphism of the product of the degree `p` components. -/
lemma towerShift_f {G : ℕᵒᵖ ⥤ CochainComplex A ℤ} {X : CochainComplex A ℤ}
    {π : ∀ n : ℕ, X ⟶ G.obj (op n)} (hP : IsLimit (Fan.mk X π)) (p : ℤ) :
    (towerShift hP).f p = towerShift (F := G ⋙ HomologicalComplex.eval A _ p)
      (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval A _ p) _ _ hP) :=
  Fan.IsLimit.hom_ext (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval A _ p) _ _ hP) _ _
    fun n ↦ by
      change (towerShift hP).f p ≫ (π n).f p = _ ≫ (π n).f p
      rw [← HomologicalComplex.comp_f]
      erw [towerShift_proj, towerShift_proj]
      rfl

/-- **Derived limits of towers of K-injective complexes.** Let `G` be a tower of K-injective
cochain complexes whose transition maps are degreewise split epimorphisms, and let `c` be a
limit cone of `G` (the degreewise limit `lim G`). Then the image of `c` in the derived category
is a homotopy limit cone: `Q (lim G) = R lim_n Q(Gₙ)`. The Milnor triangle is the image of the
short exact Roos sequence `0 ⟶ lim G ⟶ ∏ Gₙ ⟶ ∏ Gₙ ⟶ 0`, and the product of the K-injective
complexes `Gₙ` is a product in the derived category. -/
theorem isHomotopyLimit_mapCone_Q {G : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    [∀ n, (G.obj (op n)).IsKInjective]
    (hG : ∀ (n : ℕ) (p : ℤ), IsSplitEpi ((G.map (homOfLE n.le_succ).op).f p))
    {c : Cone G} (hc : IsLimit c) : IsHomotopyLimit (Q.mapCone c) := by
  let hP := productIsProduct fun n : ℕ ↦ G.obj (op n)
  let P := Fan.mk (∏ᶜ fun n : ℕ ↦ G.obj (op n)) (Pi.π _)
  have hepi : Epi (𝟙 P.pt - towerShift hP) := by
    refine HomologicalComplex.epi_of_epi_f _ fun p ↦ ?_
    have := isSplitEpi_sub_towerShift (F := G ⋙ HomologicalComplex.eval A _ p)
      (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval A _ p) _ _ hP) fun n ↦ hG n p
    rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, towerShift_f]
    exact @IsSplitEpi.epi _ _ _ _ _ this
  have hS := shortExact_towerShift hP hc hepi
  have hPD := isLimitFanQOfIsKInjective hP
  refine ⟨_, hPD, triangleOfSESδ hS, ?_⟩
  have h₁ : Fan.IsLimit.lift hPD (fun n ↦ (Q.mapCone c).π.app (op n)) =
      Q.map (Fan.IsLimit.lift hP fun n ↦ c.π.app (op n)) :=
    Fan.IsLimit.hom_ext hPD _ _ fun n ↦ by
      rw [Fan.IsLimit.fac]
      simp only [fan_mk_proj, Functor.mapCone_π_app, ← Functor.map_comp]
      congr 1
      exact (Fan.IsLimit.fac hP (fun n ↦ c.π.app (op n)) n).symm
  have h₂ : 𝟙 _ - towerShift (F := G ⋙ Q) hPD = Q.map (𝟙 P.pt - towerShift hP) := by
    rw [Functor.map_sub, CategoryTheory.Functor.map_id]
    congr 1
    refine Fan.IsLimit.hom_ext hPD _ _ fun n ↦ ?_
    rw [towerShift_proj]
    simp only [fan_mk_proj, Functor.comp_map, ← Functor.map_comp]
    congr 1
    exact (towerShift_proj hP n).symm
  rw [h₁, h₂]
  exact triangleOfSES_distinguished hS

end DerivedCategory
