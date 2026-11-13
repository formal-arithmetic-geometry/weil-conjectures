/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.StrictPerfectTensorRelativeTorBound
import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Finite relative Tor dimension of a perfect tensor

## References

* Stacks Project, Tags 0DJQ, 08CI and 08CG.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem isZero_of_local_sections
    {X : Scheme.{u}}
    (A : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (M : SheafOfModules.{u} A) (U : X → X.Opens)
    (hcover : ∀ x : X, x ∈ U x)
    (hzero : ∀ (x : X) (V : X.Opens), V ≤ U x →
      IsZero ((SheafOfModules.evaluation A (Opposite.op V)).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero M).mpr
  ext W s
  change s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.val.presheaf, M.isSheaf⟩
    (fun x ↦ W.unop ⊓ U x) W.unop (fun _ ↦ homOfLE inf_le_left) ?_ s 0 ?_
  · intro x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx, hcover x⟩
  · intro x
    have : Subsingleton (M.val.obj (Opposite.op (W.unop ⊓ U x))) :=
      ModuleCat.isZero_iff_subsingleton.mp (hzero x (W.unop ⊓ U x) inf_le_right)
    exact @Subsingleton.elim (M.val.obj (Opposite.op (W.unop ⊓ U x))) this _ _

/-- A perfect tensor with a bounded relatively flat complex has finite relative Tor
dimension on a quasi-compact scheme. No coherence or proper support is needed.
(Stacks, Tags 0DJQ, 08CI, 08CG) -/
theorem perfect_tensor_hasFiniteTorDimensionOver
    {X S : Scheme.{u}} [CompactSpace X] (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    HasFiniteTorDimensionOver f (E ⊗ DerivedCategory.Q.obj G) := by
  classical
  let T := E ⊗ DerivedCategory.Q.obj G
  let K := DerivedCategory.Q.objPreimage T
  let eK : DerivedCategory.Q.obj K ≅ T := DerivedCategory.Q.objObjPreimageIso T
  let R := TopCat.Sheaf.inverseImageRing f.base S.sheaf
  let A := (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R
  let Kbase := ((SheafOfModules.restrictScalars
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).map
        (Modules.tensorPullbackRingMap f))).mapHomologicalComplex (.up ℤ)).obj K
  obtain ⟨P, q, hP, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := R) Kbase
  obtain ⟨c, d, hGb⟩ := hGb
  choose U hx L hL eL using hE
  choose a b hLb using fun x ↦ (hL x).1
  have hlocal (x : X) (F : SheafOfModules.{u} A) (i : ℤ)
      (hi : i < a x + c ∨ b x + d < i) (V : X.Opens) (hV : V ≤ U x) :
      IsZero ((SheafOfModules.evaluation A (Opposite.op V)).obj
        ((CochainComplex.mapBifunctor P
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory R))).homology i)) :=
    strictPerfect_tensor_relativeTor_bound f E G K eK (U x) (L x) (hL x)
      (eL x).some (a x) (b x) c d (hLb x) hGb hGflat P hP q hq F i hi V hV
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let lower := insert 0 (s.image (fun x ↦ a x + c))
  let upper := insert 0 (s.image (fun x ↦ b x + d))
  have hlow : lower.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hupp : upper.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let lo := lower.min' hlow
  let hi := upper.max' hupp
  have hlo : lo ≤ 0 := lower.min'_le 0 (Finset.mem_insert_self _ _)
  have hhi : 0 ≤ hi := upper.le_max' 0 (Finset.mem_insert_self _ _)
  refine ⟨K, ⟨eK⟩, P, hP, q, hq, lo, hi, hlo.trans hhi, ?_⟩
  intro F i hout
  have hselected (x : X) : ∃ y ∈ s, x ∈ U y := by
    have h := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at h
    exact h
  choose y hy hxy using hselected
  apply isZero_of_local_sections A _ (fun x ↦ U (y x)) hxy
  intro x V hV
  apply hlocal (y x) F i ?_ V hV
  have hla : lo ≤ a (y x) + c := lower.min'_le _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hy x)))
  have hbu : b (y x) + d ≤ hi := upper.le_max' _
    (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (hy x)))
  rcases hout with hout | hout
  · exact Or.inl (hout.trans_le hla)
  · exact Or.inr (hbu.trans_lt hout)

end AlgebraicGeometry.Scheme
