/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.RingedSiteCompleteElement
public import Mathlib.RingTheory.Ideal.Span
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.CategoryTheory.RingedSiteCompleteElementMul
import Sheaf.CategoryTheory.RingedSiteCompleteElementLocal
import Sheaf.CategoryTheory.RingedSiteLocalizationSumSequence
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Vanishing localizations form a sheaf of ideals

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(blueprint: lem-weil-pbc-ringed-derived-complete-elements-ideal).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

private theorem sectionLocalization_zero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) :
    IsZero (ringedSiteSectionLocalization R U 0) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply colimit.hom_ext
  intro n
  simp only [comp_zero]
  let t : SheafOfModules.unit (R.over U) ⟶ SheafOfModules.unit (R.over U) :=
    (SheafOfModules.unit (R.over U)).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk (fun V ↦ R.obj.map V.unop.hom.op 0)
        (fun {V W} a ↦ ringedSiteSectionLocalization_compatible R U 0 V W a))
  have ht : t = 0 := by
    apply (SheafOfModules.unit (R.over U)).unitHomEquiv.injective
    ext V
    simp [t, SheafOfModules.unitHomEquiv_apply_coe]
    rfl
  change colimit.ι (Functor.ofSequence (fun _ : ℕ ↦ t)) n = 0
  rw [← colimit.w _ (homOfLE (Nat.le_add_right n 1))]
  simp [ht]

open CategoryTheory.Pretriangulated.Opposite CategoryTheory.Pretriangulated in
private theorem completeElement_zero
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) :
    IsRingedSiteCompleteElement J R K U 0 := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over U)))
  let M := ringedSiteDerivedRestriction R₀ U K
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 M
  let := s
  have := hs
  exact (((Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj M).map_isZero
    (((DerivedCategory.singleFunctor _ 0).map_isZero
      (sectionLocalization_zero R₀ U)).op))

open CategoryTheory.Pretriangulated.Opposite CategoryTheory.Pretriangulated in
private theorem completeElement_add
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) (f g : R.obj.obj (op U))
    (hf : IsRingedSiteCompleteElement J R K U f)
    (hg : IsRingedSiteCompleteElement J R K U g) :
    IsRingedSiteCompleteElement J R K U (f + g) := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over U)))
  let M := ringedSiteDerivedRestriction R₀ U K
  let H := (Functor.curry.obj (derivedInternalHom (J.over U) (R.over U))).flip.obj M
  obtain ⟨s, hs⟩ := (ringedInternalHom_exact (J.over U) (R.over U)).2 M
  let := s
  have := hs
  let L := fun t : R.obj.obj (op U) ↦ ringedSiteSectionLocalization R₀ U t
  let Q := DerivedCategory.singleFunctor (SheafOfModules.{u}
    ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (R.over U))) 0
  let F := Q.op ⋙ H
  have h₁ : IsZero (F.obj (op (L (f * (f + g))))) := by
    change IsRingedSiteCompleteElement J R K U (f * (f + g))
    simpa only [mul_comm f] using ringedSite_complete_element_mul J R K U (f + g) f hf
  have h₂ : IsZero (F.obj (op (L (g * (f + g))))) := by
    change IsRingedSiteCompleteElement J R K U (g * (f + g))
    simpa only [mul_comm g] using ringedSite_complete_element_mul J R K U (f + g) g hg
  have h₃ : IsZero (F.obj (op (L (f * g * (f + g))))) := by
    change IsRingedSiteCompleteElement J R K U (f * g * (f + g))
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      ringedSite_complete_element_mul J R K U (g * (f + g)) f hf
  have hB : IsZero (F.obj (op (L (f * (f + g)) ⊞ L (g * (f + g))))) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← F.map_id]
    have he : 𝟙 (op (L (f * (f + g)) ⊞ L (g * (f + g)))) =
        (biprod.inl : L (f * (f + g)) ⟶ _).op ≫ biprod.fst.op +
          (biprod.inr : L (g * (f + g)) ⟶ _).op ≫ biprod.snd.op := by
      exact congrArg Quiver.Hom.op (biprod.total.symm)
    rw [he, F.map_add, F.map_comp, F.map_comp,
      h₁.eq_of_tgt (F.map biprod.inl.op) 0,
      h₂.eq_of_tgt (F.map biprod.inr.op) 0]
    simp
  obtain ⟨i, p, hip, hseq⟩ := ringedSite_localization_sum_sequence J R U f g
  let T := (Pretriangulated.triangleOpEquivalence _).functor.obj (op hseq.singleTriangle)
  have hT := H.map_distinguished T
    (Pretriangulated.op_distinguished _ hseq.singleTriangle_distinguished)
  exact Triangle.isZero₃_of_isZero₁₂ _ hT h₃ hB

/-- The sections whose localization has zero derived internal Hom into K form a sheaf
of ideals. The first clause identifies every ideal section with the actual Hom-vanishing
criterion. Ideals encode zero, addition, and multiplication by arbitrary sections. The
next clauses express restriction and descent for every covering sieve. The final clause
is the locally finite-generated ideal consequence, using local finite-span membership.

Source: Stacks Project, algebraization.tex, Tags 0998 and 0997
(blueprint: lem-weil-pbc-ringed-derived-complete-elements-ideal).

Proof:
1. The colimit defining localization at zero is zero: each colimit injection
   factors through the next transition, which is zero. Exactness of derived
   internal Hom in its first variable then gives completeness of zero.
2. The multiplicative stability theorem gives completeness of every multiple
   of a complete section.
3. Put h = f + g. The two-element localization sequence is short exact, with
   terms O[1/h], O[1/(fh)] ⊕ O[1/(gh)], and O[1/(fgh)]. Multiplicative stability
   makes the derived Hom of each localization in the last two terms vanish.
4. The degree-zero short exact sequence gives a distinguished triangle. Apply
   the contravariant triangulated derived internal Hom. Its first two terms
   are zero (the middle biproduct is handled by its identity decomposition),
   so the third is zero. Thus f + g is complete.
5. Construct the ideal with carrier exactly the complete-element predicate.
   The locality theorem supplies restriction (using the maximal sieve) and
   descent for every covering sieve.
6. For the locally generated ideal test, use Ideal.span_le on every member
   of the covering sieve, then apply descent. Empty lists of generators and
   empty covering sieves are included by the same argument.
-/
theorem ringedSite_complete_elements_ideal
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ I : ∀ U : C, Ideal (R.obj.obj (op U)),
      (∀ (U : C) (f : R.obj.obj (op U)),
        f ∈ I U ↔ IsRingedSiteCompleteElement J R K U f) ∧
      (∀ (U V : C) (a : V ⟶ U) (f : R.obj.obj (op U)),
        f ∈ I U → R.obj.map a.op f ∈ I V) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ f : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a → R.obj.map a.op f ∈ I V) → f ∈ I U) ∧
      (∀ (U : C) (S : Sieve U), S ∈ J U → ∀ x : R.obj.obj (op U),
        (∀ (V : C) (a : V ⟶ U), S a →
          ∃ (r : ℕ) (b : Fin r → R.obj.obj (op V)),
            (∀ i : Fin r, IsRingedSiteCompleteElement J R K V (b i)) ∧
            R.obj.map a.op x ∈ Ideal.span (Set.range b)) →
        IsRingedSiteCompleteElement J R K U x) := by
  let I : ∀ U : C, Ideal (R.obj.obj (op U)) := fun U ↦
    { carrier := {f | IsRingedSiteCompleteElement J R K U f}
      zero_mem' := completeElement_zero J R K U
      add_mem' := fun hf hg ↦ completeElement_add J R K U _ _ hf hg
      smul_mem' := fun a _ hf ↦ ringedSite_complete_element_mul J R K U a _ hf }
  refine ⟨I, fun _ _ ↦ Iff.rfl, ?_, ?_, ?_⟩
  · intro U V a f hf
    exact (ringedSite_complete_element_local J R K U ⊤ (J.top_mem U) f).mp hf
      V a (by trivial)
  · intro U S hS f hf
    exact (ringedSite_complete_element_local J R K U S hS f).mpr hf
  · intro U S hS x hx
    apply (ringedSite_complete_element_local J R K U S hS x).mpr
    intro V a ha
    obtain ⟨r, b, hb, hxb⟩ := hx V a ha
    have hspan : Ideal.span (Set.range b) ≤ I V := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact hb j
    exact hspan hxb

end CategoryTheory
