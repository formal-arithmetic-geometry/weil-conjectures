/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.Factorizations.CM5a
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # The bottom derived unit on a lower-truncated complex

## References

* Stacks Project, Tags 05TC, 015A, 05TH and 05TI
-/

@[expose] public section

universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Localization identifies good lower truncation with t-structure lower truncation,
with the canonical projection fixed (Stacks, Tag 015A). -/
private theorem lowerTruncationLocalization
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (I : CochainComplex C ℤ) (n : ℤ) :
    ∃ e : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj (I.truncGE n)) ≅
        (DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I),
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
          (I.πTruncGE n)) ≫ e.hom =
        (DerivedCategory.quotientCompQhIso C).hom.app I ≫
          (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let p := DerivedCategory.Q.map (I.πTruncGE n)
  let b := t.descTruncGE p n
  have hb : (t.truncGEπ n).app (DerivedCategory.Q.obj I) ≫ b = p :=
    t.π_descTruncGE p n
  have hi : IsIso b := by
    rw [DerivedCategory.isIso_iff]
    intro i
    let H := DerivedCategory.homologyFunctor C i
    by_cases h : n ≤ i
    · have : IsIso (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I))) :=
        DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app _ n i h
      have : QuasiIsoAt (I.πTruncGE n) i :=
        I.quasiIsoAt_πTruncGE n i h
      have hp : IsIso (H.map p) := by
        change IsIso ((DerivedCategory.Q ⋙ H).map (I.πTruncGE n))
        rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C i)]
        change IsIso (HomologicalComplex.homologyMap (I.πTruncGE n) i)
        infer_instance
      have : IsIso (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I)) ≫
          H.map b) := by
        rw [← H.map_comp, hb]
        exact hp
      exact IsIso.of_isIso_comp_left
        (H.map ((t.truncGEπ n).app (DerivedCategory.Q.obj I))) (H.map b)
    · have h' : i < n := by omega
      exact isIso_of_source_target_iso_zero (H.map b)
        (DerivedCategory.isZero_of_isGE _ n i h').isoZero
        (DerivedCategory.isZero_of_isGE _ n i h').isoZero
  let a := (DerivedCategory.quotientCompQhIso C).app (I.truncGE n) ≪≫ (asIso b).symm
  refine ⟨a, ?_⟩
  dsimp only [a, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc]
  erw [(DerivedCategory.quotientCompQhIso C).hom.naturality (I.πTruncGE n)]
  change ((DerivedCategory.quotientCompQhIso C).hom.app I ≫ p) ≫ inv b = _
  rw [← hb]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl


private theorem preservesBottomHomology
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    F.PreservesLeftHomologyOf (K.sc n) := by
  refine ⟨fun h ↦ ?_⟩
  have hf : (K.sc n).f = 0 := by
    change K.d ((ComplexShape.up ℤ).prev n) n = 0
    exact (K.isZero_of_isStrictlyGE n _ (by simp)).eq_of_src _ _
  have hf' : h.f' = 0 := by
    rw [← cancel_mono h.i, ShortComplex.LeftHomologyData.f'_i, zero_comp]
    exact hf
  exact { g := inferInstance, f' := preservesCokernel_zero' F _ hf' }

set_option backward.isDefEq.respectTransparency false in
/-- The actual right-derived unit is invertible on bottom cohomology of a
complex that is strictly zero in lower degrees (Stacks, Tags 05TC, 05TH, 05TI and 015A). -/
private theorem isIsoBottomUnit
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))) := by
  let P := HomotopyCategory.quotient C (.up ℤ)
  let M := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor D n
  obtain ⟨L, i, hi, hL, hn⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  let := hi
  let := hn
  let (j : ℤ) : Injective (L.X j) := hL j
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L n
  let := preservesBottomHomology F K n
  let := preservesBottomHomology F L n
  let φ := (HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map i
  have hmap : IsIso (HomologicalComplex.homologyMap (M.map i) n) := by
    have hnat := ShortComplex.mapHomologyIso_hom_naturality φ F
    have hφ : IsIso (ShortComplex.homologyMap φ) :=
      inferInstanceAs (IsIso (HomologicalComplex.homologyMap i n))
    have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map φ) ≫
        ((L.sc n).mapHomologyIso F).hom) := by
      rw [hnat]
      infer_instance
    exact IsIso.of_isIso_comp_right
      (ShortComplex.homologyMap (F.mapShortComplex.map φ)) ((L.sc n).mapHomologyIso F).hom
  have hQ : IsIso (DerivedCategory.Qh.map (P.map i)) := by
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
      (P.map i) (by simpa [P, HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff] using hi)
  have hFM : IsIso (H.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map (P.map i)))) := by
    rw [Functor.mapHomotopyCategory_map]
    erw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh D n)]
    erw [NatIso.isIso_map_iff (HomotopyCategory.homologyFunctorFactors D (.up ℤ) n)]
    exact hmap
  have hnat := F.rightDerivedFunctorUnit.naturality (P.map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso (H.map (F.rightDerivedFunctorUnit.app (P.obj K)) ≫
      H.map (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (P.map i)))) := by
    rw [← H.map_comp, ← hnat, H.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (F.rightDerivedFunctorUnit.app (P.obj K)))
    (H.map (F.rightDerivedFunctor.map (DerivedCategory.Qh.map (P.map i))))


set_option backward.isDefEq.respectTransparency false in
/-- The derived edge map factors through the underived lower truncation, and
its bottom-degree comparison there is invertible. This concerns the derived
unit and localization only; it contains no cycle-class or homology quotient map
(Stacks, Tags 05TC, 015A, 05TH and 05TI). -/
theorem derived_lower_truncation_unit_bridge
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let H := DerivedCategory.homologyFunctor D n
    let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh D n).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
    let U := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)
    let q := F.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso C).hom.app I ≫
        (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))
    ∃ d : ((F.mapHomologicalComplex (.up ℤ)).obj (I.truncGE n)).homology n ≅
        H.obj (F.rightDerivedFunctor.obj
          ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I))),
      e.hom ≫ H.map U ≫ H.map q =
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (.up ℤ)).map (I.πTruncGE n)) n ≫ d.hom := by
  dsimp only
  let P := HomotopyCategory.quotient C (.up ℤ)
  let PD := HomotopyCategory.quotient D (.up ℤ)
  let M := F.mapHomologicalComplex (.up ℤ)
  let H := DerivedCategory.homologyFunctor D n
  let K := I.truncGE n
  let f := I.πTruncGE n
  obtain ⟨a, ha⟩ := lowerTruncationLocalization I n
  have hu := isIsoBottomUnit F K n
  let eK := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app
      (M.obj K)).symm ≪≫
    ((DerivedCategory.homologyFunctorFactorsh D n).app (PD.obj (M.obj K))).symm
  refine ⟨eK ≪≫ asIso (H.map (F.rightDerivedFunctorUnit.app (P.obj K))) ≪≫
    H.mapIso (F.rightDerivedFunctor.mapIso a), ?_⟩
  have hn := F.rightDerivedFunctorUnit.naturality (P.map f)
  dsimp only [Functor.comp_map] at hn
  have he :
      (((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app
          (M.obj I)).symm ≪≫
        ((DerivedCategory.homologyFunctorFactorsh D n).app (PD.obj (M.obj I))).symm).hom ≫
        H.map (DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map (P.map f))) =
      HomologicalComplex.homologyMap (M.map f) n ≫ eK.hom := by
    rw [Functor.mapHomotopyCategory_map]
    dsimp only [Iso.trans_hom, Iso.symm_hom, eK]
    simp only [Category.assoc]
    erw [← (DerivedCategory.homologyFunctorFactorsh D n).inv.naturality
      (PD.map (M.map f))]
    erw [← (HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).inv.naturality_assoc
      (M.map f)]
    rfl
  simp only [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, Category.assoc]
  rw [← ha, F.rightDerivedFunctor.map_comp, H.map_comp]
  rw [← H.map_comp_assoc, ← hn, H.map_comp]
  simp only [Iso.trans_hom, Iso.symm_hom] at he
  simp only [Category.assoc, Iso.symm_hom]
  rw [reassoc_of% he]

end AlgebraicGeometry
