/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Data.Int.Interval
import Sheaf.Algebra.Homology.HomComplexProjections
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Finite diagonal support for a bounded Hom-complex.

Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-finite-support).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem finiteSupport_coproduct
    {A : Type*} [Category A] [Preadditive A] (M : ℤ → A)
    (T : A) (π : ∀ p, T ⟶ M p) (hπ : IsLimit (Fan.mk T π))
    (s : Finset ℤ) (hz : ∀ p, p ∉ s → IsZero (M p)) :
    ∃ ι : ∀ i : s, M i ⟶ T,
      Nonempty (IsColimit (Cofan.mk T ι)) ∧
      ∀ (i : s) (p : ℤ), ι i ≫ π p =
        if h : (i : ℤ) = p then eqToHom (congrArg M h) else 0 := by
  classical
  let ι (i : s) : M i ⟶ T := Fan.IsLimit.lift hπ
    (fun p ↦ if h : (i : ℤ) = p then eqToHom (congrArg M h) else 0)
  have hι (i : s) (p : ℤ) : ι i ≫ π p =
      if h : (i : ℤ) = p then eqToHom (congrArg M h) else 0 :=
    Fan.IsLimit.fac hπ _ p
  have ht : IsLimit (Fan.mk T (fun p : s ↦ π p)) := by
    let extend (c : Fan (fun p : s ↦ M p)) : Fan M :=
      Fan.mk c.pt (fun p ↦ if h : p ∈ s then c.proj ⟨p, h⟩ else 0)
    refine Fan.IsLimit.mk _ (fun c ↦ hπ.lift (extend c)) ?_ ?_
    · intro c p
      simpa [extend] using hπ.fac (extend c) ⟨p.val⟩
    · intro c m hm
      apply hπ.hom_ext
      intro p
      by_cases hp : p.as ∈ s
      · rw [hπ.fac]
        simpa [extend, hp] using hm ⟨p.as, hp⟩
      · exact (hz p.as hp).eq_of_tgt _ _
  let B : Limits.Bicone (fun i : s ↦ M i) :=
    { pt := T
      π := fun i ↦ π i
      ι := ι
      ι_π := by
        intro i j
        rw [hι]
        by_cases h : i = j
        · subst j
          simp
        · have hv : (i : ℤ) ≠ j := fun e ↦ h (Subtype.ext e)
          simp [h, hv] }
  exact ⟨ι, ⟨(isBilimitOfIsLimit B ht).isColimit⟩, hι⟩

set_option backward.isDefEq.respectTransparency true in
/-- Finite diagonals of the product Hom complex are also coproduct diagrams.
Source: Stacks Project, Cohomology on Sites, Tag 08JI.
(blueprint: lem-weil-pbc-ringed-site-bounded-free-rhom-finite-support).
Proof: take the existing Hom-complex product projections and differential formula.
Outside [a-n,b] either the source or target term is zero, so the internal Hom
factor is zero. Restrict the product universal property to this finite interval
by extending every test cone by zero. Lift the coordinate identity maps to get
inclusions. They and the restricted projections form a finite bicone whose cone
is limiting, hence whose cocone is colimiting in a preadditive category. The
lift equations give the asserted coordinate formula, also for an empty interval. -/
theorem ringedSite_boundedFree_rhom_finiteSupport
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    (P N : CochainComplex
      (ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a b : ℤ) (hP : ∀ i : ℤ, b < i → IsZero (P.X i))
    (hN : ∀ j : ℤ, j < a → IsZero (N.X j)) :
    ∃ π : ∀ (n p q : ℤ), p + n = q →
        ((homComplex (R := R) P N).X n ⟶
          SheafOfModules.homObj (R := R) (P.X p) (N.X q)),
      (∀ n : ℤ, Nonempty (IsLimit (Fan.mk ((homComplex (R := R) P N).X n)
        (fun p : ℤ ↦ π n p (p + n) rfl)))) ∧
      (∀ (n m p q q' p' : ℤ) (_hnm : n + 1 = m)
        (hpq : p + m = q) (hq' : p + n = q') (hp' : p' + n = q),
        (homComplex (R := R) P N).d n m ≫ π m p q hpq =
          π n p q' hq' ≫ SheafOfModules.homObjMap (R := R)
              (𝟙 (P.X p)) (N.d q' q) -
            n.negOnePow • (π n p' q hp' ≫
              SheafOfModules.homObjMap (R := R) (P.d p p') (𝟙 (N.X q)))) ∧
      (∀ (n : ℤ), ∃ ι : ∀ i : ↥(Finset.Icc (a - n) b),
          SheafOfModules.homObj (R := R) (P.X i) (N.X (i + n)) ⟶
            (homComplex (R := R) P N).X n,
        Nonempty (IsColimit (Cofan.mk ((homComplex (R := R) P N).X n) ι)) ∧
        ∀ (i : ↥(Finset.Icc (a - n) b)) (p : ℤ),
          ι i ≫ π n p (p + n) rfl =
            if h : (i : ℤ) = p then eqToHom (congrArg (fun k : ℤ ↦
              SheafOfModules.homObj (R := R) (P.X k) (N.X (k + n))) h)
            else 0) := by
  classical
  obtain ⟨π, hπ, hd, _⟩ := homComplex_projections_exists (R := R)
  refine ⟨π P N, hπ P N, hd P N, ?_⟩
  intro n
  let M : ℤ → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
    fun p ↦ SheafOfModules.homObj (R := R) (P.X p) (N.X (p + n))
  have hz (p : ℤ) (hp : p ∉ Finset.Icc (a - n) b) : IsZero (M p) := by
    have h : p < a - n ∨ b < p := by simpa only
      [Finset.mem_Icc, not_and_or, not_le] using hp
    rcases h with h | h
    · apply (IsZero.iff_id_eq_zero _).mpr
      change 𝟙 (SheafOfModules.homObj (R := R) (P.X p) (N.X (p + n))) = 0
      rw [← SheafOfModules.homObjMap_id (R := R) (M := P.X p) (N := N.X (p + n)),
        (hN (p + n) (by omega)).eq_of_tgt (𝟙 _) 0]
      apply SheafOfModules.hom_ext
      ext X φ : 3
      rfl
    · apply (IsZero.iff_id_eq_zero _).mpr
      change 𝟙 (SheafOfModules.homObj (R := R) (P.X p) (N.X (p + n))) = 0
      rw [← SheafOfModules.homObjMap_id (R := R) (M := P.X p) (N := N.X (p + n)),
        (hP p h).eq_of_src (𝟙 _) 0]
      apply SheafOfModules.hom_ext
      ext X φ : 3
      change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
        (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 _ : N.X (p + n) ⟶ _).val = 0
      ext W x
      change ((φ.app W).hom) (0) = 0
      exact map_zero _
  exact finiteSupport_coproduct M ((homComplex (R := R) P N).X n)
    (fun p ↦ π P N n p (p + n) rfl) (Classical.choice (hπ P N n)) _ hz

end CategoryTheory
