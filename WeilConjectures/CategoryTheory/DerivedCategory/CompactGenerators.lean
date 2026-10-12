/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.Triangulated.Brown.CompactObject
public import WeilConjectures.CategoryTheory.Triangulated.Brown.Representability
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Compact generators of derived categories

Let `C` be an abelian category with K-injective resolutions and coproducts, and let `P` be a
family of projective objects of `C` which are compact (morphisms into coproducts factor
through finite partial sums) and which detect zero objects. Then the objects `P i` placed in
degree `0` form a family of compact generators of the derived category `D(C)`:

* `P i[n]` is K-projective, so a morphism `P i[n] ⟶ Q(⨿ Kⱼ)` comes from a morphism of
  complexes, i.e. from a morphism `P i ⟶ ⨿ Kⱼⁿ` killed by the differential; by compactness of
  `P i` it factors through a finite partial sum, and the components are again killed by the
  differentials since coproducts of complexes are computed degreewise;
* morphisms `P i[-n] ⟶ Y` are morphisms `P i ⟶ Hⁿ(Y)`, so if they all vanish then all the
  cohomology objects of `Y` vanish, and `Y` is zero.

By Neeman's theorem, `D(C)` then has Brown representability.

## Main statements

- `DerivedCategory.isCompactObject_singleFunctor_obj`: a compact projective object placed in
  any degree is compact in `D(C)`.
- `DerivedCategory.isCompactGeneratingFamily_singleFunctor`: compact projective objects
  detecting zero objects form a family of compact generators of `D(C)`.
- `DerivedCategory.hasBrownRepresentability_of_projective`: under these assumptions, `D(C)`
  has Brown representability.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Abelian Pretriangulated Preadditive

namespace DerivedCategory

variable {C : Type u} [Category.{w} C] [Abelian C] [HasDerivedCategory.{w} C]
  [HasKInjectiveResolutions C] [HasCoproducts.{w} C]

/-- A compact projective object `P` of `C` placed in degree `n` is a compact object of the
derived category. -/
lemma isCompactObject_singleFunctor_obj (P : C) [Projective P] (hP : IsCompactObject P)
    (n : ℤ) : IsCompactObject ((singleFunctor C n).obj P) := by
  let L := (HomologicalComplex.single C (ComplexShape.up ℤ) n).obj P
  change IsCompactObject (Q.obj L)
  refine isCompactObject_of_exists_cofan fun J f ↦ ?_
  let K : J → CochainComplex C ℤ := fun j ↦ Q.objPreimage (f j)
  let e (j : J) : Q.obj (K j) ≅ f j := Q.objObjPreimageIso (f j)
  obtain ⟨s, ⟨hs⟩⟩ : ∃ s : Cofan K, Nonempty (IsColimit s) := ⟨_, ⟨coproductIsCoproduct K⟩⟩
  have hQ : IsColimit (Cofan.mk (Q.obj s.pt) fun j ↦ Q.map (s.inj j)) :=
    isColimitCofanMkObjOfIsColimit Q K s.inj (hs : IsColimit (Cofan.mk s.pt s.inj))
  let c : Cofan f := Cofan.mk (Q.obj s.pt) fun j ↦ (e j).inv ≫ Q.map (s.inj j)
  have hc : IsColimit c := Cofan.IsColimit.mk c
    (fun t ↦ Cofan.IsColimit.desc hQ fun j ↦ (e j).hom ≫ t.inj j)
    (fun t j ↦ by
      simp only [c, cofan_mk_inj, Category.assoc]
      rw [show Q.map (s.inj j) ≫ _ = _ from Cofan.IsColimit.fac hQ _ j, Iso.inv_hom_id_assoc])
    (fun t m hm ↦ Cofan.IsColimit.hom_ext hQ _ _ fun j ↦ by
      rw [show (Cofan.mk (Q.obj s.pt) fun j ↦ Q.map (s.inj j)).inj j ≫ _ = _ from
        Cofan.IsColimit.fac hQ _ j, ← hm j]
      simp [c])
  refine ⟨c, hc, fun φ ↦ ?_⟩
  have : CochainComplex.IsKProjective L := CochainComplex.isKProjective_singleFunctor_obj P n
  obtain ⟨g, rfl⟩ := CochainComplex.IsKProjective.exists_Q_map_eq L s.pt φ
  -- the degree `n` component of `g`
  have hs' (i : ℤ) : IsColimit (Cofan.mk (s.pt.X i) fun j ↦ (s.inj j).f i) :=
    isColimitCofanMkObjOfIsColimit (HomologicalComplex.eval C _ i) K s.inj
      (hs : IsColimit (Cofan.mk s.pt s.inj))
  let g' : P ⟶ s.pt.X n := (HomologicalComplex.singleObjXSelf _ n P).inv ≫ g.f n
  obtain ⟨t, ψ, hψ⟩ := hP _ _ (hs' n) g'
  classical
  let χ (j : J) : P ⟶ (K j).X n := if j ∈ t then ψ j else 0
  have hg' : g' = ∑ j ∈ t, χ j ≫ (s.inj j).f n := by
    rw [hψ]
    exact Finset.sum_congr rfl fun j hj ↦ by simp [χ, hj]
  -- the components are cycles
  have hχ (j : J) : χ j ≫ (K j).d n (n + 1) = 0 := by
    by_cases hj : j ∈ t
    · have h₀ : g' ≫ s.pt.d n (n + 1) = 0 := by
        simp only [g', Category.assoc, HomologicalComplex.Hom.comm]
        rw [(HomologicalComplex.isZero_single_obj_X _ n P (n + 1) (by omega)).eq_of_tgt
          (L.d n (n + 1)) 0, zero_comp, comp_zero]
      rw [hg', sum_comp] at h₀
      simp only [Category.assoc, HomologicalComplex.Hom.comm] at h₀
      exact Cofan.IsColimit.eq_zero_of_sum_eq_zero (hs' (n + 1)) t (fun j ↦ χ j ≫ (K j).d n _)
        (by simpa only [Category.assoc, cofan_mk_inj, Cofan.mk_pt] using h₀) hj
    · simp [χ, hj]
  let χ' (j : J) : L ⟶ K j := HomologicalComplex.mkHomFromSingle (χ j) (fun k hk ↦ by
    obtain rfl : n + 1 = k := hk
    exact hχ j)
  have hg : g = ∑ j ∈ t, χ' j ≫ s.inj j := by
    ext : 1
    have := (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map_sum (fun j ↦ χ' j ≫ s.inj j) t
    simp only [HomologicalComplex.eval_map] at this
    rw [this]
    simp only [HomologicalComplex.comp_f, χ', HomologicalComplex.mkHomFromSingle_f,
      Category.assoc, ← comp_sum, ← hg', g', Iso.hom_inv_id_assoc]
  refine ⟨t, fun j ↦ Q.map (χ' j) ≫ (e j).hom, ?_⟩
  rw [hg, Functor.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [c]

omit [HasKInjectiveResolutions C] [HasCoproducts.{w} C] in
/-- If a family of projective objects detects zero objects of `C`, then the family of these
objects placed in degree `0` detects zero objects of `D(C)`, up to shifts. -/
lemma isZero_of_forall_singleFunctor_shift_hom_eq_zero {ι : Type*} (P : ι → C)
    [∀ i, Projective (P i)] (hP : ∀ M : C, (∀ i (g : P i ⟶ M), g = 0) → IsZero M)
    (Y : DerivedCategory C)
    (hY : ∀ i (n : ℤ) (φ : ((singleFunctor C 0).obj (P i))⟦n⟧ ⟶ Y), φ = 0) : IsZero Y := by
  refine isZero_of_forall_isZero_homology Y fun n ↦ hP _ fun i g ↦ ?_
  have : Subsingleton ((singleFunctor C 0).obj (P i) ⟶ Y⟦n⟧) := by
    let e := ((shiftEquiv (DerivedCategory C) n).symm.toAdjunction.homEquiv
      ((singleFunctor C 0).obj (P i)) Y)
    refine ⟨fun a b ↦ e.symm.injective ?_⟩
    rw [hY i (-n) (e.symm a), hY i (-n) (e.symm b)]
  exact ((subsingleton_singleFunctor_hom_shift_iff_of_projective (P i) Y n).1 this).elim _ _

/-- A family of compact projective objects of `C` detecting zero objects, placed in degree `0`,
is a family of compact generators of `D(C)`. -/
theorem isCompactGeneratingFamily_singleFunctor {ι : Type w} (P : ι → C)
    [∀ i, Projective (P i)] (hPc : ∀ i, IsCompactObject (P i))
    (hP : ∀ M : C, (∀ i (g : P i ⟶ M), g = 0) → IsZero M) :
    IsCompactGeneratingFamily (fun i ↦ (singleFunctor C 0).obj (P i)) where
  isCompactObject i n := (isCompactObject_singleFunctor_obj (P i) (hPc i) (-n)).of_iso
    (((singleFunctors C).shiftIso n (-n) 0 (by omega)).app (P i)).symm
  isZero := isZero_of_forall_singleFunctor_shift_hom_eq_zero P hP

/-- **Brown representability** for the derived category of an abelian category with
K-injective resolutions and coproducts, generated by a family of compact projective objects:
every additive cohomological functor `D(C)ᵒᵖ ⥤ Ab` sending coproducts to products is
representable. -/
theorem hasBrownRepresentability_of_projective {ι : Type w} (P : ι → C)
    [∀ i, Projective (P i)] (hPc : ∀ i, IsCompactObject (P i))
    (hP : ∀ M : C, (∀ i (g : P i ⟶ M), g = 0) → IsZero M) :
    HasBrownRepresentability (DerivedCategory C) :=
  (isCompactGeneratingFamily_singleFunctor P hPc hP).hasBrownRepresentability

end DerivedCategory
