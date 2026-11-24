/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.Algebra.Homology.RhomGlobalSections
import WeilConjectures.AlgebraicGeometry.PerfectHypercohomologyGap
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparison
import WeilConjectures.AlgebraicGeometry.PerfectRHomTensorComparisonDual
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.QuasiCompactFiniteTorDimension
import WeilConjectures.AlgebraicGeometry.OpenDerivedLocalizationAdjunction
import WeilConjectures.AlgebraicGeometry.OpenDerivedCategorySmall
import WeilConjectures.AlgebraicGeometry.DerivedTensorQCohClosure
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.AlgebraicGeometry.UniformInverseAffineSectionsBound
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Mathlib.AlgebraicGeometry.Limits

/-! # Vanishing of maps from a perfect complex across a cohomology gap

## References

* Stacks Project, Derived Categories of Schemes, Lemma 36.13.5(1), Tag 09M4.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sections_equiv (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    (SheafOfModules.unit (moduleRings X.toRingedSpace) ⟶ M) ≃+
      (RingedSpace.openModuleSections X.toRingedSpace ⊤).obj M where
  toEquiv := M.unitHomEquiv.trans
    { toFun := fun s ↦ s.val (Opposite.op ⊤)
      invFun := fun x ↦ M.val.sectionsMk
        (fun U ↦ M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op x)
        (fun U V f ↦ by
          rw [← PresheafOfModules.map_comp_apply]
          rfl)
      left_inv := fun s ↦ by
        apply PresheafOfModules.sections_ext
        intro U
        exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
      right_inv := fun x ↦ by
        change M.val.map (𝟙 (Opposite.op ⊤)) x = x
        simp }
  map_add' f g := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def sections_iso (X : Scheme.{u}) :
    preadditiveCoyoneda.obj (Opposite.op (SheafOfModules.unit (moduleRings X.toRingedSpace))) ≅
      RingedSpace.openModuleSections X.toRingedSpace ⊤ :=
  NatIso.ofComponents (fun M ↦ (sections_equiv X M).toAddCommGrpIso) (by
    intro M N f
    ext g
    rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Zeroth hypercohomology on a qcqs scheme vanishes across a uniform cohomology gap
(Stacks, Tag 09M4). -/
private theorem exists_qcoh_zerothHypercohomology_gap (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ N : ℕ, ∀ E : schemeDerivedCategory X,
      schemeDerivedQCohProperty X E →
      (∀ j : ℤ, -(N : ℤ) ≤ j → j ≤ 0 → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj E)) →
      IsZero ((ringedSiteZerothHypercohomology
        (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf).obj E) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian _
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  let S := RingedSpace.openModuleSections X.toRingedSpace ⊤
  obtain ⟨N, hpos, hN⟩ := exists_uniform_inverse_affine_sections_bound
    (terminal.from X)
  have hNS : ∀ (M : C), M.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
      IsZero ((S.rightDerived p).obj M) := by
    intro M hM p hp
    simpa only [Scheme.Hom.preimage_top] using hN ⊤ (isAffineOpen_top _) M hM p hp
  have : PreservesLimitsOfShape (Discrete ℕ) S := by
    dsimp [S, RingedSpace.openModuleSections]
    infer_instance
  refine ⟨N, ?_⟩
  intro E hE hgap
  let t := DerivedCategory.TStructure.t (C := C)
  let A := (t.truncLT (-(N : ℤ))).obj E
  let B := (t.truncGE (-(N : ℤ))).obj E
  let P := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hzero : IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : P.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  have hA : schemeDerivedQCohProperty X A := by
    have hle := DerivedCategory.homologyProperty_truncLE hE (-(N : ℤ) - 1)
    exact (DerivedCategory.homologyProperty P).prop_of_iso
      ((t.truncLEIsoTruncLT (-(N : ℤ) - 1) (-(N : ℤ)) (by omega)).app E) hle
  have hzA : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      (S.rightDerivedFunctor.obj A)) := by
    apply isZero_homology_rightDerivedFunctor_of_cohomological_bound
      X S N hNS (-(N : ℤ) - 1) A hA
      (fun i hi ↦ DerivedCategory.isZero_of_isLE A (-(N : ℤ) - 1) i hi) 0
    omega
  have hB : B.IsGE 1 := by
    apply (DerivedCategory.isGE_iff B 1).2
    intro i hi
    by_cases hni : i < -(N : ℤ)
    · exact DerivedCategory.isZero_of_isGE B (-(N : ℤ)) i hni
    · have : IsIso ((DerivedCategory.homologyFunctor C i).map
          ((t.truncGEπ (-(N : ℤ))).app E)) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app E (-(N : ℤ)) i (by omega)
      exact (hgap i (by omega) (by omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor C i).map
          ((t.truncGEπ (-(N : ℤ))).app E))).symm
  let Bplus : DerivedCategory.Plus C := ⟨B, ⟨1, hB⟩⟩
  have : Bplus.IsGE 1 := (Bplus.isGE_ι_obj_iff 1).1 hB
  have hzB : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      (S.rightDerivedFunctor.obj B)) := by
    have hz := S.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE Bplus 1
      (q := 0) (by omega)
    exact hz.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      (S.rightDerivedFunctorPlusCompatibility.app Bplus)).symm
  let T := S.rightDerivedFunctor.mapTriangle.obj ((t.triangleLTGE (-(N : ℤ))).obj E)
  have hT : T ∈ Pretriangulated.distinguishedTriangles :=
    S.rightDerivedFunctor.map_distinguished _ (t.triangleLTGE_distinguished (-(N : ℤ)) E)
  have hzE : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      (S.rightDerivedFunctor.obj E)) :=
    (DerivedCategory.HomologySequence.exact₂ T hT 0).isZero_X₂
      (hzA.eq_of_src _ _) (hzB.eq_of_tgt _ _)
  exact hzE.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
    ((Functor.rightDerivedFunctorNatIso (sections_iso X)).app E))

private theorem tensor_homology_isZero_of_gap (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (P L : schemeDerivedCategory X) (j : ℤ)
    (h : schemeDerivedTensorComplexCohomologyVanishes X P L j) :
    IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
        (MonoidalCategoryStruct.tensorObj P L)) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨A, B, hA, ⟨eA⟩, ⟨eB⟩, hz⟩ := h
  obtain ⟨e⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj A)
    ((Functor.const (Discrete PUnit.{1})).obj B) (fun _ ↦ hA)
  let eTensor : MonoidalCategoryStruct.tensorObj P L ≅ DerivedCategory.Q.obj
      (CochainComplex.mapBifunctor A B (MonoidalCategory.curriedTensor _)) :=
    (MonoidalCategory.tensorIso eA eB).symm ≪≫ (e.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ j).mapIso eTensor ≪≫
    (DerivedCategory.homologyFunctorFactors _ j).app _)

/-- On a quasi-compact and quasi-separated scheme, a perfect complex admits a finite
cohomology gap such that every object with quasi-coherent cohomology vanishing in that gap
receives only the zero morphism from it (Stacks, Tag 09M4). -/
theorem exists_subsingleton_hom_of_isPerfect (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X) (hK : IsPerfect X K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ L : schemeDerivedCategory X,
      schemeDerivedQCohProperty X L →
      (∀ i : ℤ, a ≤ i → i ≤ b →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj L)) →
      Subsingleton (K ⟶ L) := by
  classical
  have hOpen (U : X.Opens) : Nonempty (HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))) := by
    exact nonempty_openHasDerivedCategory X U
  let (U : X.Opens) : HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    Classical.choice (hOpen U)
  obtain ⟨adj, s, adj', hadj, hs, he, hadj'⟩ := scheme_derivedInternalHom_adjunction X
  let Kq : schemeDerivedQCohCategory X := ⟨K, schemeDerivedQCohProperty_of_isPerfect X K hK⟩
  obtain ⟨D, hD, hperfect⟩ := exists_perfect_rhom_dual X Kq hK
  obtain ⟨lo, hi, hlohi, htor⟩ := hasFiniteTorDimension_of_locallyFinite X D.obj
    (perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension X D.obj hperfect).2
  obtain ⟨N, hN⟩ := exists_qcoh_zerothHypercohomology_gap X
  refine ⟨-hi - (N : ℤ), -lo, by omega, ?_⟩
  intro L hL hgap
  let Lq : schemeDerivedQCohCategory X := ⟨L, hL⟩
  have hvan (j : ℤ) (hj : -(N : ℤ) ≤ j) (hj' : j ≤ 0) :
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj
          (MonoidalCategoryStruct.tensorObj D.obj L)) := by
    apply tensor_homology_isZero_of_gap X D.obj L j
    apply perfect_hypercohomology_gap X D.obj L hperfect lo hi htor hL j
    intro q hq hq'
    exact hgap q (by omega) (by omega)
  have hzero := hN (MonoidalCategoryStruct.tensorObj D.obj L)
    (canonical_derivedTensor_preserve_QCoh X D.obj L D.property hL) hvan
  obtain ⟨D', hD', ev, hev, hp, comparison, hcomp, hc, rest⟩ :=
    perfect_rhom_tensor_comparison X Kq Lq hK adj hadj adj' hadj'
  have : IsIso (comparison Lq) := hc
  let eD : D.obj ≅ D'.obj := eqToIso (hD.trans hD'.symm)
  let H := ringedSiteZerothHypercohomology (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf
  have hz : IsZero (H.obj ((derivedInternalHom
      (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf).obj
        (Opposite.op K, L))) :=
    hzero.of_iso (H.mapIso (s D.obj L ≪≫
      MonoidalCategory.tensorIso (Iso.refl L) eD ≪≫ asIso (comparison Lq))).symm
  obtain ⟨e, _⟩ := rhom_global_sections
    (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf
  let : Subsingleton (H.obj ((derivedInternalHom
      (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf).obj
        (Opposite.op K, L))) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  exact (e (Opposite.op K, L)).symm.toEquiv.injective.subsingleton

end AlgebraicGeometry.Scheme
