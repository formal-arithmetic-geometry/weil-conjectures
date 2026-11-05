/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Data.Int.Interval
public import WeilConjectures.CategoryTheory.PBCFiltration

/-!
# The two filtrations of a first-quadrant total complex

Source: Stacks Project, Homological Algebra, Section 12.18, Tag 012Z, and the
blueprint's two filtrations and graded pieces (blueprint: def-sp-double-complex-total).

The bicomplex and total complex are Mathlib's `HomologicalComplex₂` and `total`.
First-quadrant vanishing is a hypothesis, not extra structure. Only the two finite
supremum filtrations are new definitions. The remaining clauses are theorem statements.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- First-quadrant vanishing implies existence of the diagonal coproducts.
Source: Stacks 12.18, following Tag 012Z (blueprint: def-sp-double-complex-total).
Proof: in degree n only indices 0 ≤ p ≤ n can be nonzero. Take their finite
coproduct, extending its cocone by the unique maps from the zero objects outside
that interval. The finite coproduct universal property gives the full diagonal colimit. -/
theorem hasTotal_of_firstQuadrant
    (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q)) :
    K.HasTotal (ComplexShape.up ℤ) := by
  classical
  intro n
  let D := {ij : ℤ × ℤ // ij.1 + ij.2 = n}
  let S := {ij : D // 0 ≤ ij.1.1 ∧ 0 ≤ ij.1.2}
  let g : S → ↥(Finset.Icc (0 : ℤ) n) := fun ij ↦
    ⟨ij.1.1.1, Finset.mem_Icc.mpr ⟨ij.2.1, by
      have := ij.1.2
      have := ij.2.2
      omega⟩⟩
  have hg : Function.Injective g := by
    intro i j h
    have hp : i.1.1.1 = j.1.1.1 := congrArg Subtype.val h
    have hi := i.1.2
    have hj := j.1.2
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext hp
    omega
  have : Finite S := Finite.of_injective g hg
  let X : D → C := fun ij ↦ (K.X ij.1.1).X ij.1.2
  let Y : S → C := fun ij ↦ X ij.1
  let c : Cofan X := Cofan.mk (∐ Y) (fun ij ↦
    if h : 0 ≤ ij.1.1 ∧ 0 ≤ ij.1.2 then Sigma.ι Y ⟨ij, h⟩ else 0)
  refine HasColimit.mk ⟨c, ?_⟩
  refine Cofan.IsColimit.mk c (fun t ↦ Sigma.desc (fun ij : S ↦ t.inj ij.1)) ?_ ?_
  · intro t ij
    dsimp [c]
    split_ifs with h
    · exact Sigma.ι_desc _ _
    · exact (hK ij.1.1 ij.1.2 (by omega)).eq_of_src _ _
  · intro t m hm
    apply Sigma.hom_ext (f := Y)
    intro ij
    have hi := hm ij.1
    simpa [c, ij.2, Sigma.ι_desc] using hi

variable [K.HasTotal (ComplexShape.up ℤ)]

/-- The finite supremum defining the first filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem firstFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))) := by
  intro p q hpq
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  exact ⟨hpq.trans hi.1, hi.2⟩

/-- Filtration by the first degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def firstFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) i (n - i) n))
  antitone_step := K.firstFiltration_antitone n

/-- The finite supremum defining the second filtration decreases with its index.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Proof: if p ≤ q, the interval [q,n] is contained in [p,n]. Every image in the
smaller supremum lies in the larger one; the finite supremum universal property
proves the inequality, including when either interval is empty. -/
theorem secondFiltration_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ (Finset.Icc p n).sup
      (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))) := by
  intro p q hpq
  apply Finset.sup_mono
  intro i hi
  simp only [Finset.mem_Icc] at hi ⊢
  exact ⟨hpq.trans hi.1, hi.2⟩

/-- Filtration by the second degree, as the finite sum of images of diagonal inclusions.
Source: blueprint filtration formula (blueprint: def-sp-double-complex-total).
Terms past n vanish for a first-quadrant bicomplex, so this finite supremum
is exactly the stated sum over indices at least p. -/
noncomputable def secondFiltration (n : ℤ) :
    PBCDecreasingFiltration ((K.total (ComplexShape.up ℤ)).X n) where
  step p := (Finset.Icc p n).sup
    (fun i ↦ imageSubobject (K.ιTotalOrZero (ComplexShape.up ℤ) (n - i) i n))
  antitone_step := K.secondFiltration_antitone n

/-- A morphism factors through any subobject containing its image. -/
private theorem factors_image (X Y : C) (f : X ⟶ Y) (S : Subobject Y)
    (h : imageSubobject f ≤ S) : S.Factors f := by
  apply Subobject.factors_of_le f h
  simpa using imageSubobject_factors_comp_self f (𝟙 X)

/-- Preservation of each generating image implies preservation of their finite supremum. -/
private theorem factors_finset_sup {I : Type*} (s : Finset I) {A : I → C}
    {X Y : C} (a : ∀ i, A i ⟶ X) (d : X ⟶ Y) (Q : Subobject Y)
    (h : ∀ i ∈ s, Q.Factors (a i ≫ d)) :
    Q.Factors ((s.sup (fun i ↦ imageSubobject (a i))).arrow ≫ d) := by
  let P := (Subobject.pullback d).obj Q
  have hs : s.sup (fun i ↦ imageSubobject (a i)) ≤ P := by
    apply Finset.sup_le
    intro i hi
    have hf := pullback_factors d Q (a i) (h i hi)
    exact imageSubobject_le (a i) (P.factorThru (a i) hf)
      (Subobject.factorThru_arrow _ _ _)
  apply (pullback_factors_iff d Q _).1
  exact Subobject.factors_of_le _ hs (Subobject.factors_self _)

/-- The canonical lifts of the generating maps jointly detect maps from their image supremum. -/
private theorem finite_sup_hom_ext {I : Type*} (s : Finset I) {A : I → C}
    {X Y : C} (a : ∀ i, A i ⟶ X)
    (g h : ((s.sup (fun i ↦ imageSubobject (a i)) : Subobject X) : C) ⟶ Y)
    (w : ∀ i, ∀ hi : i ∈ s,
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ g =
      (factorThruImageSubobject (a i) ≫ Subobject.ofLE _ _
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)) ≫ h) :
    g = h := by
  let S := s.sup (fun i ↦ imageSubobject (a i))
  let e := equalizer.ι g h ≫ S.arrow
  have hs : S ≤ Subobject.mk e := by
    apply Finset.sup_le
    intro i hi
    let l := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)
    apply imageSubobject_le_mk e (a i) (equalizer.lift l (w i hi))
    simp [e, l]
  let r := Subobject.ofLE S (Subobject.mk e) hs ≫ (Subobject.underlyingIso e).hom
  have hr : r ≫ equalizer.ι g h = 𝟙 _ := by
    apply (cancel_mono S.arrow).1
    rw [Category.assoc, Category.id_comp]
    change r ≫ e = S.arrow
    simp [r]
  have : IsSplitEpi (equalizer.ι g h) := IsSplitEpi.mk' ⟨r, hr⟩
  exact (cancel_epi (equalizer.ι g h)).1 (equalizer.condition g h)

/--
A projection onto one summand identifies the quotient by the remaining tail with that summand. -/
private theorem finite_sup_cokernel_iso {A : ℤ → C} {V : C}
    (a : ∀ i, A i ⟶ V) (p n : ℤ) (r : V ⟶ A p)
    (hr : a p ≫ r = 𝟙 _) (hri : ∀ i, i ≠ p → a i ≫ r = 0)
    (hz : n < p → IsZero (A p)) :
    (let S := (Finset.Icc p n).sup (fun i ↦ imageSubobject (a i))
    let T := (Finset.Icc (p + 1) n).sup (fun i ↦ imageSubobject (a i))
    let le : T ≤ S := Finset.sup_mono (by
      intro i hi
      simp only [Finset.mem_Icc] at hi ⊢
      omega)
    ∃ l : A p ⟶ (S : C), l ≫ S.arrow = a p ∧
      IsIso (l ≫ cokernel.π (Subobject.ofLE T S le))) := by
  dsimp only
  let S := (Finset.Icc p n).sup (fun i ↦ imageSubobject (a i))
  let T := (Finset.Icc (p + 1) n).sup (fun i ↦ imageSubobject (a i))
  have hTS : T ≤ S := Finset.sup_mono (by
    intro i hi
    simp only [Finset.mem_Icc] at hi ⊢
    omega)
  let f := Subobject.ofLE T S hTS
  have ha : S.Factors (a p) := by
    by_cases hpn : p ≤ n
    · apply factors_image
      exact Finset.le_sup (s := Finset.Icc p n)
        (f := fun i ↦ imageSubobject (a i)) (Finset.mem_Icc.mpr ⟨le_rfl, hpn⟩)
    · rw [(hz (by omega)).eq_zero_of_src (a p)]
      exact Subobject.factors_zero
  let l := S.factorThru (a p) ha
  have hl : l ≫ S.arrow = a p := Subobject.factorThru_arrow _ _ _
  have ht : T.arrow ≫ r = 0 := by
    apply (Subobject.bot_factors_iff_zero _).1
    apply factors_finset_sup (Finset.Icc (p + 1) n) a r ⊥
    intro i hi
    rw [hri i (by have := (Finset.mem_Icc.mp hi).1; omega)]
    exact Subobject.factors_zero
  have hf : f ≫ (S.arrow ≫ r) = 0 := by
    rw [← Category.assoc, Subobject.ofLE_arrow, ht]
  let b := cokernel.desc f (S.arrow ≫ r) hf
  have hb : cokernel.π f ≫ b = S.arrow ≫ r := cokernel.π_desc _ _ _
  have hab : (l ≫ cokernel.π f) ≫ b = 𝟙 _ := by
    rw [Category.assoc, hb, ← Category.assoc, hl, hr]
  have hba : b ≫ (l ≫ cokernel.π f) = 𝟙 _ := by
    apply (cancel_epi (cokernel.π f)).1
    rw [← Category.assoc, hb, Category.comp_id]
    apply finite_sup_hom_ext (Finset.Icc p n) a
    intro i hi
    let li := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ S
      (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hi)
    have hli : li ≫ S.arrow = a i := by simp [li]
    change li ≫ ((S.arrow ≫ r) ≫ l ≫ cokernel.π f) = li ≫ cokernel.π f
    by_cases hip : i = p
    · subst i
      have hil : li = l := (cancel_mono S.arrow).1 (hli.trans hl.symm)
      rw [hil]
      simp only [Category.assoc, reassoc_of% hl, reassoc_of% hr]
    · have hit : i ∈ Finset.Icc (p + 1) n := by
        have := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
      let ti := factorThruImageSubobject (a i) ≫ Subobject.ofLE _ T
        (Finset.le_sup (f := fun i ↦ imageSubobject (a i)) hit)
      have hilt : li = ti ≫ f := by
        apply (cancel_mono S.arrow).1
        simp [li, ti, f]
      simp only [Category.assoc, reassoc_of% hli, reassoc_of% (hri i hip),
        CategoryTheory.Limits.zero_comp]
      rw [hilt, Category.assoc, cokernel.condition, CategoryTheory.Limits.comp_zero]
  have hiso : IsIso (l ≫ cokernel.π f) :=
    (⟨l ≫ cokernel.π f, b, hab, hba⟩ : A p ≅ cokernel f).isIso_hom
  exact ⟨l, hl, hiso⟩

variable (hK : ∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((K.X p).X q))

include hK

end HomologicalComplex₂
