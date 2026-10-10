/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Separating pairs descend to a finite stage

The affine criterion `AlgebraicGeometry.IsSeparatingPair` for separatedness descends along a
cofiltered limit of quasi-compact quasi-separated schemes with affine transition maps
(`AlgebraicGeometry.exists_isSeparatingPair_of_isLimit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section SeparatedDescent

/-!
### Separatedness descends to a finite stage

Stacks Project Tags 086Q and 01ZH.
-/

set_option backward.defeqAttrib.useBackward true

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [∀ i, CompactSpace (D.obj i)] in
include hc in
/-- (Implementation) If the preimage in the limit of a quasi-compact open of a stage is affine,
then so is its preimage at some later stage. -/
lemma exists_isAffineOpen_preimage {i₀ : I} {W : (D.obj i₀).Opens}
    (hWc : IsCompact (W : Set (D.obj i₀))) (hW : IsAffineOpen (c.π.app i₀ ⁻¹ᵁ W)) :
    ∃ j : Over i₀, IsAffineOpen (D.map j.hom ⁻¹ᵁ W) := by
  have (j : Over i₀) : CompactSpace ((opensDiagram D i₀ W).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage _ W.2 hWc)
  have (j : Over i₀) : QuasiSeparatedSpace ((opensDiagram D i₀ W).obj j) :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map _ ⁻¹ᵁ _).2).mp (.of_quasiSeparatedSpace _)
  have : IsAffine (opensCone D c i₀ W).pt := hW
  exact Scheme.exists_isAffine_of_isLimit _ _ (isLimitOpensCone D c hc i₀ W)

section SeparatingPair

variable (i₀ : I) {U V : (D.obj i₀).Opens}

set_option maxHeartbeats 1000000 in
-- descending the finitely many generators through the three systems of opens is a long
-- computation
omit [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] in
include hc in
lemma exists_isSeparatingPair_of_isLimit
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))
    (h : IsSeparatingPair c.pt (c.π.app i₀ ⁻¹ᵁ U) (c.π.app i₀ ⁻¹ᵁ V)) :
    ∃ j : Over i₀, ∀ {k : Over i₀} (_ : k ⟶ j),
      IsSeparatingPair (D.obj k.left) (D.map k.hom ⁻¹ᵁ U) (D.map k.hom ⁻¹ᵁ V) := by
  classical
  set E := opensDiagram D i₀ (U ⊓ V) with hE
  set A := opensDiagram D i₀ U with hA
  set B := opensDiagram D i₀ V with hB
  set cE := opensCone D c i₀ (U ⊓ V) with hcE
  set cA := opensCone D c i₀ U with hcA
  set cB := opensCone D c i₀ V with hcB
  have hlimE : IsLimit cE := isLimitOpensCone D c hc i₀ (U ⊓ V)
  have hlimA : IsLimit cA := isLimitOpensCone D c hc i₀ U
  have hlimB : IsLimit cB := isLimitOpensCone D c hc i₀ V
  have hEaff : ∀ j : Over i₀, IsAffine (E.obj j) := fun j ↦ hUV.preimage (D.map j.hom)
  have hAaff : ∀ j : Over i₀, IsAffine (A.obj j) := fun j ↦ hU.preimage (D.map j.hom)
  have hBaff : ∀ j : Over i₀, IsAffine (B.obj j) := fun j ↦ hV.preimage (D.map j.hom)
  have hleU : ∀ j : Over i₀,
      (D.map j.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j.left).Opens) ≤ D.map j.hom ⁻¹ᵁ U := by
    intro j x hx
    exact hx.1
  have hleV : ∀ j : Over i₀,
      (D.map j.hom ⁻¹ᵁ (U ⊓ V) : (D.obj j.left).Opens) ≤ D.map j.hom ⁻¹ᵁ V := by
    intro j x hx
    exact hx.2
  have hleUlim : (c.π.app i₀ ⁻¹ᵁ (U ⊓ V) : c.pt.Opens) ≤ c.π.app i₀ ⁻¹ᵁ U := by
    intro x hx
    exact hx.1
  have hleVlim : (c.π.app i₀ ⁻¹ᵁ (U ⊓ V) : c.pt.Opens) ≤ c.π.app i₀ ⁻¹ᵁ V := by
    intro x hx
    exact hx.2
  set a : ∀ j : Over i₀, E.obj j ⟶ A.obj j :=
    fun j ↦ (D.obj j.left).homOfLE (hleU j) with ha
  set b : ∀ j : Over i₀, E.obj j ⟶ B.obj j :=
    fun j ↦ (D.obj j.left).homOfLE (hleV j) with hb
  set aLim : cE.pt ⟶ cA.pt := c.pt.homOfLE hleUlim with haLim
  set bLim : cE.pt ⟶ cB.pt := c.pt.homOfLE hleVlim with hbLim
  set R : ∀ j : Over i₀, Subring Γ(E.obj j, ⊤) := fun j ↦
    Subring.closure (Set.range ⇑(a j).appTop.hom ∪ Set.range ⇑(b j).appTop.hom) with hR
  have hpreim : ∀ {j k : Over i₀} (g : k ⟶ j) (W : (D.obj i₀).Opens),
      D.map g.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ W) = D.map k.hom ⁻¹ᵁ W := by
    intro j k g W
    rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w g]
  have hpreimlim : ∀ (j : Over i₀) (W : (D.obj i₀).Opens),
      c.π.app j.left ⁻¹ᵁ (D.map j.hom ⁻¹ᵁ W) = c.π.app i₀ ⁻¹ᵁ W := by
    intro j W
    rw [← Scheme.Hom.comp_preimage, c.w]
  -- the comparison squares
  have sqA : ∀ {j k : Over i₀} (g : k ⟶ j), IsPullback (E.map g) (a k) (a j) (A.map g) := by
    intro j k g
    exact isPullback_resLE_homOfLE (D.map g.left) (hleU j) (hleU k) _ _
      (by rw [hpreim g (U ⊓ V)]; exact inf_le_right)
  have sqB : ∀ {j k : Over i₀} (g : k ⟶ j), IsPullback (E.map g) (b k) (b j) (B.map g) := by
    intro j k g
    exact isPullback_resLE_homOfLE (D.map g.left) (hleV j) (hleV k) _ _
      (by rw [hpreim g (U ⊓ V)]; exact inf_le_right)
  have sqAlim : ∀ j : Over i₀, IsPullback (cE.π.app j) aLim (a j) (cA.π.app j) := by
    intro j
    exact isPullback_resLE_homOfLE (c.π.app j.left) (hleU j) hleUlim _ _
      (by rw [hpreimlim j (U ⊓ V)]; exact inf_le_right)
  have sqBlim : ∀ j : Over i₀, IsPullback (cE.π.app j) bLim (b j) (cB.π.app j) := by
    intro j
    exact isPullback_resLE_homOfLE (c.π.app j.left) (hleV j) hleVlim _ _
      (by rw [hpreimlim j (U ⊓ V)]; exact inf_le_right)
  -- sections at a later stage are generated by those from the earlier stage and those from `U`
  have hgen : ∀ {j k : Over i₀} (g : k ⟶ j),
      Subring.closure (Set.range ⇑(E.map g).appTop.hom ∪ Set.range ⇑(a k).appTop.hom) = ⊤ := by
    intro j k g
    have := hEaff j
    have := hAaff j
    have := hAaff k
    exact CommRingCat.closure_range_union_range_eq_top_of_isPushout
      (isPushout_appTop_of_isPullback (sqA g))
  -- the transition maps respect the subrings `R`
  have hmapR : ∀ {j k : Over i₀} (g : k ⟶ j) (w : Γ(E.obj j, ⊤)), w ∈ R j →
      (E.map g).appTop.hom w ∈ R k := by
    intro j k g w hw
    have hle : R j ≤ Subring.comap (E.map g).appTop.hom (R k) := by
      simp only [hR, Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
      · refine Subring.subset_closure (Or.inl ⟨(A.map g).appTop.hom z, ?_⟩)
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          ← Scheme.Hom.comp_appTop, (sqA g).w]
      · refine Subring.subset_closure (Or.inr ⟨(B.map g).appTop.hom z, ?_⟩)
        rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          ← Scheme.Hom.comp_appTop, (sqB g).w]
    exact hle hw
  have hcone : ∀ {j k : Over i₀} (g : k ⟶ j) (w : Γ(E.obj j, ⊤)),
      (cE.π.app k).appTop.hom ((E.map g).appTop.hom w) = (cE.π.app j).appTop.hom w := by
    intro j k g w
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, cE.w g]
    rfl
  -- every section over the limit comes from a stage, inside the subring `R`
  have hdesc : ∀ z : Γ(cE.pt, ⊤), ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)),
      w ∈ R j ∧ (cE.π.app j).appTop.hom w = z := by
    have hmerge : ∀ z₁ z₂ : Γ(cE.pt, ⊤),
        (∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z₁) →
        (∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z₂) →
        ∃ (j : Over i₀) (w₁ : Γ(E.obj j, ⊤)) (w₂ : Γ(E.obj j, ⊤)), w₁ ∈ R j ∧ w₂ ∈ R j ∧
          (cE.π.app j).appTop.hom w₁ = z₁ ∧ (cE.π.app j).appTop.hom w₂ = z₂ := by
      rintro z₁ z₂ ⟨j₁, w₁, hw₁, rfl⟩ ⟨j₂, w₂, hw₂, rfl⟩
      obtain ⟨j₃, g₁, g₂, -⟩ := IsCofilteredOrEmpty.cone_objs j₁ j₂
      exact ⟨j₃, (E.map g₁).appTop.hom w₁, (E.map g₂).appTop.hom w₂,
        hmapR g₁ _ hw₁, hmapR g₂ _ hw₂, hcone g₁ w₁, hcone g₂ w₂⟩
    have hS : ∀ z : Γ(cE.pt, ⊤), z ∈ (Subring.closure
        (Set.range ⇑aLim.appTop.hom ∪ Set.range ⇑bLim.appTop.hom)) →
        ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧ (cE.π.app j).appTop.hom w = z := by
      intro z hz
      let S : Subring Γ(cE.pt, ⊤) :=
        { carrier := {z | ∃ (j : Over i₀) (w : Γ(E.obj j, ⊤)), w ∈ R j ∧
            (cE.π.app j).appTop.hom w = z}
          one_mem' := ⟨Over.mk (𝟙 i₀), 1, one_mem _, map_one _⟩
          zero_mem' := ⟨Over.mk (𝟙 i₀), 0, zero_mem _, map_zero _⟩
          add_mem' := by
            rintro z₁ z₂ h₁ h₂
            obtain ⟨j, w₁, w₂, hw₁, hw₂, e₁, e₂⟩ := hmerge z₁ z₂ h₁ h₂
            exact ⟨j, w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add, e₁, e₂]⟩
          mul_mem' := by
            rintro z₁ z₂ h₁ h₂
            obtain ⟨j, w₁, w₂, hw₁, hw₂, e₁, e₂⟩ := hmerge z₁ z₂ h₁ h₂
            exact ⟨j, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, e₁, e₂]⟩
          neg_mem' := by
            rintro z ⟨j, w, hw, rfl⟩
            exact ⟨j, -w, neg_mem hw, by rw [map_neg]⟩ }
      have hsub : Subring.closure
          (Set.range ⇑aLim.appTop.hom ∪ Set.range ⇑bLim.appTop.hom) ≤ S := by
        rw [Subring.closure_le]
        rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
        · obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit A cA hlimA x
          refine ⟨j, (a j).appTop.hom t, Subring.subset_closure (Or.inl ⟨t, rfl⟩), ?_⟩
          have h2 : (a j).appTop ≫ (cE.π.app j).appTop
              = (cA.π.app j).appTop ≫ aLim.appTop := by
            rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, (sqAlim j).w]
          rw [← ht]
          exact congrArg (fun φ : Γ(A.obj j, ⊤) ⟶ Γ(cE.pt, ⊤) => φ.hom t) h2
        · obtain ⟨j, t, ht⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit B cB hlimB x
          refine ⟨j, (b j).appTop.hom t, Subring.subset_closure (Or.inr ⟨t, rfl⟩), ?_⟩
          have h2 : (b j).appTop ≫ (cE.π.app j).appTop
              = (cB.π.app j).appTop ≫ bLim.appTop := by
            rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, (sqBlim j).w]
          rw [← ht]
          exact congrArg (fun φ : Γ(B.obj j, ⊤) ⟶ Γ(cE.pt, ⊤) => φ.hom t) h2
      exact hsub hz
    intro z
    exact hS z (h.ge (Subring.mem_top z))
  -- finitely many generators at the initial stage
  set j₀ : Over i₀ := Over.mk (𝟙 i₀) with hj₀
  have : IsAffine (E.obj j₀) := hEaff j₀
  have : IsAffine (A.obj j₀) := hAaff j₀
  have : LocallyOfFiniteType (a j₀) := by rw [ha]; infer_instance
  obtain ⟨s, hs⟩ := exists_finset_closure_range_appTop_union_eq_top (a j₀)
  -- every generator lies in `R` at a late enough stage
  have key : ∀ x : Γ(E.obj j₀, ⊤), ∃ (j : Over i₀) (g : j ⟶ j₀),
      (E.map g).appTop.hom x ∈ R j := by
    intro x
    obtain ⟨j₁, w, hw, hwz⟩ := hdesc ((cE.π.app j₀).appTop.hom x)
    obtain ⟨g₁⟩ : Nonempty (j₁ ⟶ j₀) := ⟨Over.homMk j₁.hom (Category.comp_id j₁.hom)⟩
    have h1 : (cE.π.app j₁).appTop.hom ((E.map g₁).appTop.hom x - w) = 0 := by
      rw [map_sub, hcone g₁ x, hwz, sub_self]
    have : IsAffine (E.obj j₁) := hEaff j₁
    obtain ⟨j₂, g₂, h2⟩ := exists_appTop_map_eq_zero_of_isLimit E cE hlimE
      ((E.map g₁).appTop.hom x - w) h1
    refine ⟨j₂, g₂ ≫ g₁, ?_⟩
    rw [map_sub, sub_eq_zero] at h2
    have h3 : (E.map (g₂ ≫ g₁)).appTop.hom x
        = (E.map g₂).appTop.hom ((E.map g₁).appTop.hom x) := by
      rw [E.map_comp, Scheme.Hom.comp_appTop]
      rfl
    rw [h3, h2]
    exact hmapR g₂ _ hw
  choose jj gg hjj using key
  obtain ⟨jstar, hjstar⟩ := IsCofiltered.inf_objs_exists (Finset.image jj s)
  refine ⟨jstar, ?_⟩
  have gstar : jstar ⟶ j₀ := Over.homMk jstar.hom (Category.comp_id jstar.hom)
  have hterm : ∀ {j : Over i₀} (m₁ m₂ : j ⟶ j₀), m₁ = m₂ := fun m₁ m₂ ↦
    Over.mkIdTerminal.hom_ext m₁ m₂
  have hRstar : R jstar = ⊤ := by
    rw [eq_top_iff, ← hgen gstar, Subring.closure_le]
    rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · have hz : z ∈ Subring.closure (Set.range ⇑(a j₀).appTop.hom ∪
          (s : Set Γ(E.obj j₀, ⊤))) := hs.ge (Subring.mem_top z)
      have hle : Subring.closure (Set.range ⇑(a j₀).appTop.hom ∪ (s : Set Γ(E.obj j₀, ⊤))) ≤
          Subring.comap (E.map gstar).appTop.hom (R jstar) := by
        rw [Subring.closure_le]
        rintro y (⟨t, rfl⟩ | hy)
        · exact hmapR gstar _ (Subring.subset_closure (Or.inl ⟨t, rfl⟩))
        · obtain ⟨m⟩ := hjstar (Finset.mem_image_of_mem jj hy)
          have h4 := hmapR m _ (hjj y)
          have h5 : (E.map gstar).appTop.hom y
              = (E.map m).appTop.hom ((E.map (gg y)).appTop.hom y) := by
            rw [hterm gstar (m ≫ gg y), E.map_comp, Scheme.Hom.comp_appTop]
            rfl
          change (E.map gstar).appTop.hom y ∈ R jstar
          rw [h5]
          exact h4
      exact hle hz
    · exact Subring.subset_closure (Or.inl ⟨z, rfl⟩)
  intro k gk
  change R k = ⊤
  rw [eq_top_iff, ← hgen gk, Subring.closure_le]
  rintro y (⟨z, rfl⟩ | ⟨z, rfl⟩)
  · exact hmapR gk z (hRstar.ge (Subring.mem_top z))
  · exact Subring.subset_closure (Or.inl ⟨z, rfl⟩)

end SeparatingPair

end SeparatedDescent

end AlgebraicGeometry
