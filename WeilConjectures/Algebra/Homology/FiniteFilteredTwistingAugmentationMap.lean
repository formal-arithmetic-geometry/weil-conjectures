/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.FiniteFilteredTwistingAugmentationData

/-! # Realizing an augmentation on a finite twisting totalization

Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, mapping-cylinder
assembly of successive filtered flat resolutions.
(blueprint: lem-trf-finite-filtered-twisting-augmentation-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
attribute [local instance] hasSheafifyEssentiallySmallSite
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}} {a b : ℤ}

set_option maxHeartbeats 800000 in
-- Summand and cokernel comparisons involve dependent finite indices.
/-- The component equations give an actual filtered chain map on any totalization, with
its specified maps on graded quotients. No flatness or quasi-isomorphism is assumed here.
Source: latest blueprint, sk-i-additivity.proof.md, Filtered operations, successive
mapping cylinders; the augmentation part of step 1 of lem-trf-finite-filtered-flat-model.
Proof: in total coordinates take the finite sum of the components followed by the inclusions
of the target filtration steps. On each summand, the chain-map identity is exactly the
augmentation equation and the defining differential equation of the totalization. For the tail
of weight r take the same sum with every component factored through F^r M. The target inclusion
is monic, so cancelling it proves the tail chain-map equation. These maps define the filtered
morphism. On grade p cancel the canonical cokernel epi. In tail coordinates the summand p gives
its specified grade map, whereas each summand q>p factors through F^(p+1) M and is killed by
the quotient projection. This proves the displayed graded equality without choosing a
splitting of the target or assuming that the augmentation components are chain maps.
(blueprint: lem-trf-finite-filtered-twisting-augmentation-map). -/
theorem exists_finiteFiltered_twistingAugmentationMap
    (D : FiniteTwistingFamily R a b)
    (M : FilteredObject (CochainComplex (ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ))
    (A : FiniteFilteredTwistingAugmentation D M) (T : FiniteTwistingTotalization D) :
    ∃ f : (⟨T.P, T.F⟩ : FilteredObject (CochainComplex (ringedSiteModules.{w}
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)) ⟶ M,
      (∀ (p : ↥(Finset.Icc a b)) (n : ℤ),
        biproduct.ι (fun q : ↥(Finset.Icc a b) ↦ (D.G q).X n) p ≫
          (T.coordinates n).inv ≫ f.hom.f n =
            A.component p n ≫ (M.filtration.F p.val).arrow.f n) ∧
      (∀ p : ↥(Finset.Icc a b),
        (T.gradedIso p).hom ≫ A.grade p = FilteredObject.gradedMapSteps f p.val) := by
  classical
  let B := ringedSiteModules.{w}
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
  have hi (r s n : ℤ) (h : r ≤ s) :
      (Subobject.ofLE (M.filtration.F s) (M.filtration.F r)
          (M.filtration.antitone h)).f n ≫ (M.filtration.F r).arrow.f n =
        (M.filtration.F s).arrow.f n := by
    rw [← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
  let v (n : ℤ) : T.P.X n ⟶ M.obj.X n :=
    (T.coordinates n).hom ≫ biproduct.desc (fun p ↦
      A.component p n ≫ (M.filtration.F p.val).arrow.f n)
  have hv (p : ↥(Finset.Icc a b)) (n : ℤ) :
      biproduct.ι (fun q ↦ (D.G q).X n) p ≫ (T.coordinates n).inv ≫ v n =
        A.component p n ≫ (M.filtration.F p.val).arrow.f n := by
    simp [v]
  have hc (n : ℤ) : T.P.d n (n + 1) ≫ v (n + 1) = v n ≫ M.obj.d n (n + 1) := by
    apply (cancel_epi (T.coordinates n).inv).1
    apply biproduct.hom_ext'
    intro p
    calc
      _ = (biproduct.ι (fun q ↦ (D.G q).X n) p ≫
          (T.coordinates n).inv ≫ T.P.d n (n + 1)) ≫ v (n + 1) := by
        simp only [Category.assoc]
      _ = ((D.G p).d n (n + 1) ≫
          biproduct.ι (fun q ↦ (D.G q).X (n + 1)) p ≫ (T.coordinates (n + 1)).inv +
          ∑ q : {q : ↥(Finset.Icc a b) // p.val < q.val},
            D.τ p q.val q.property n ≫ biproduct.ι (fun t ↦ (D.G t).X (n + 1)) q.val ≫
              (T.coordinates (n + 1)).inv) ≫ v (n + 1) := by rw [T.differential]
      _ = (A.component p n ≫
          (M.filtration.F p.val : CochainComplex B ℤ).d n (n + 1)) ≫
            (M.filtration.F p.val).arrow.f (n + 1) := by
        rw [A.comm]
        simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc,
          hv, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
      _ = A.component p n ≫ (M.filtration.F p.val).arrow.f n ≫
          M.obj.d n (n + 1) := by
        rw [Category.assoc, HomologicalComplex.Hom.comm]
      _ = _ := by
        simpa only [Category.assoc] using
          (congrArg (fun k ↦ k ≫ M.obj.d n (n + 1)) (hv p n)).symm
  let f₀ : T.P ⟶ M.obj :=
    { f := v
      comm' := fun i j h ↦ by
        have hj : i + 1 = j := h
        subst j
        exact (hc i).symm }
  let u (r n : ℤ) : (T.F.F r : CochainComplex B ℤ).X n ⟶
      (M.filtration.F r : CochainComplex B ℤ).X n :=
    (T.tailCoordinates r n).hom ≫ biproduct.desc (fun p ↦ A.component p.val n ≫
      (Subobject.ofLE (M.filtration.F p.val.val) (M.filtration.F r)
        (M.filtration.antitone p.property)).f n)
  have hu (r n : ℤ) : u r n ≫ (M.filtration.F r).arrow.f n =
      (T.F.F r).arrow.f n ≫ f₀.f n := by
    apply (cancel_epi (T.tailCoordinates r n).inv).1
    rw [← Category.assoc (T.tailCoordinates r n).inv ((T.F.F r).arrow.f n),
      T.tailInclusion]
    apply biproduct.hom_ext'
    intro p
    simp [u, f₀, Category.assoc, hv, ← HomologicalComplex.comp_f, Subobject.ofLE_arrow]
  let l (r : ℤ) : (T.F.F r : CochainComplex B ℤ) ⟶
      (M.filtration.F r : CochainComplex B ℤ) :=
    { f := u r
      comm' := fun i j _ ↦ by
        symm
        apply (cancel_mono ((M.filtration.F r).arrow.f j)).1
        calc
          _ = (T.F.F r : CochainComplex B ℤ).d i j ≫
              (T.F.F r).arrow.f j ≫ f₀.f j := by rw [Category.assoc, hu]
          _ = (T.F.F r).arrow.f i ≫ T.P.d i j ≫ f₀.f j := by
            rw [HomologicalComplex.Hom.comm_assoc]
          _ = (T.F.F r).arrow.f i ≫ f₀.f i ≫ M.obj.d i j := by
            rw [f₀.comm]
          _ = u r i ≫ (M.filtration.F r).arrow.f i ≫ M.obj.d i j := by
            simpa only [Category.assoc] using
              (congrArg (fun k ↦ k ≫ M.obj.d i j) (hu r i)).symm
          _ = _ := by
            simp only [Category.assoc, HomologicalComplex.Hom.comm] }
  let f : (⟨T.P, T.F⟩ : FilteredObject (CochainComplex B ℤ)) ⟶ M :=
    ⟨f₀, fun r ↦ ⟨l r, by apply HomologicalComplex.hom_ext; intro n; exact hu r n⟩⟩
  refine ⟨f, hv, ?_⟩
  intro p
  have hl (r : ℤ) : FilteredObject.restrictionSteps f r = l r := by
    apply (cancel_mono (M.filtration.F r).arrow).1
    change Classical.choose (f.preserves r) ≫ _ = _
    rw [Classical.choose_spec (f.preserves r)]
    exact (show l r ≫ (M.filtration.F r).arrow = (T.F.F r).arrow ≫ f₀ by
      apply HomologicalComplex.hom_ext
      intro n
      exact hu r n).symm
  let π := T.F.complexQuotientπ p.val (p.val + 1) (by omega)
  let π' := M.filtration.complexQuotientπ p.val (p.val + 1) (by omega)
  have hgr := Classical.choose_spec (FilteredObject.exists_gradedMap_steps _ _ f p.val)
  change π ≫ FilteredObject.gradedMapSteps f p.val =
    FilteredObject.restrictionSteps f p.val ≫ π' at hgr
  have : Epi π := by dsimp [π, DecreasingFiltration.complexQuotientπ]; infer_instance
  apply (cancel_epi π).1
  rw [hgr, hl]
  apply HomologicalComplex.hom_ext
  intro n
  change π.f n ≫ (T.gradedIso p).hom.f n ≫ (A.grade p).f n = u p.val n ≫ π'.f n
  rw [← Category.assoc, T.gradedProjection]
  apply (cancel_epi (T.tailCoordinates p.val n).inv).1
  apply biproduct.hom_ext'
  intro q
  simp only [Category.assoc]
  rw [← Category.assoc (T.tailCoordinates p.val n).inv ((T.F.step p.val).arrow.f n),
    T.tailInclusion]
  simp only [biproduct.ι_desc_assoc, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [u, Iso.inv_hom_id_assoc, biproduct.ι_desc_assoc, Category.assoc]
  rcases q with ⟨q, hq⟩
  by_cases hqp : q = p
  · subst q
    simp only [biproduct.ι_π_self_assoc]
    rw [A.grade_f]
    congr 1
    simp only [Subobject.ofLE_refl, HomologicalComplex.id_f, Category.id_comp]
    rfl
  · rw [biproduct.ι_π_ne_assoc _ hqp, zero_comp]
    have hlt : p.val + 1 ≤ q.val := by
      have hne : q.val ≠ p.val := fun h ↦ hqp (Subtype.ext h)
      omega
    let i := Subobject.ofLE (M.filtration.F q.val) (M.filtration.F (p.val + 1))
      (M.filtration.antitone hlt)
    let j := Subobject.ofLE (M.filtration.F (p.val + 1)) (M.filtration.F p.val)
      (M.filtration.F_succ_le p.val)
    have hij : (Subobject.ofLE (M.filtration.F q.val) (M.filtration.F p.val)
        (M.filtration.antitone hq)).f n = i.f n ≫ j.f n := by
      exact (congrArg (fun k :
        (M.filtration.F q.val : CochainComplex B ℤ) ⟶
          (M.filtration.F p.val : CochainComplex B ℤ) ↦ k.f n)
        (Subobject.ofLE_comp_ofLE (M.filtration.F q.val)
          (M.filtration.F (p.val + 1)) (M.filtration.F p.val)
          (M.filtration.antitone hlt) (M.filtration.F_succ_le p.val))).symm
    rw [hij]
    simp only [Category.assoc]
    have hz : j.f n ≫ π'.f n = 0 := by
      have hh : j ≫ π' = 0 := cokernel.condition j
      exact congrArg (fun k : (M.filtration.F (p.val + 1) : CochainComplex B ℤ) ⟶
        M.filtration.gradedPiece p.val ↦ k.f n) hh
    simp only [hz, comp_zero]

end CochainComplex
