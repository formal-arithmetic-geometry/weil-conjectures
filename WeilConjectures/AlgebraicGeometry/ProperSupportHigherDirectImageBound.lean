/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import all WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # Eventual vanishing for a coherent module with proper support

## References

* [Stacks, Tag 08E2], [Stacks, Tag 0CYS], [Stacks, Tag 01XJ]
-/

@[expose] public section

universe u wX

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Higher direct images of one coherent module with proper support eventually vanish.
(Stacks, Tag 08E2) -/
theorem moduleHigherDirectImage_eventually_isZero
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hM : RingedSpace.IsCoherent X.toRingedSpace M)
    (hsupport : Scheme.Modules.HasSupportProperOver f M) :
    ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
      IsZero (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨hqc, hft⟩ := (Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X M).mp hM
  have := hqc
  have := hft
  obtain ⟨Z, i, hi, hg, _, G, hGqc, _, ⟨eM⟩⟩ :=
    (Modules.module_support_proper_over_base f M).2.1.mp hsupport
  have := hi
  have := hg
  have := hGqc
  let AZ := SheafOfModules.{u} (moduleRings Z.toRingedSpace)
  let AX := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let AS := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let : HasDerivedCategory AZ := HasDerivedCategory.standard AZ
  let : HasDerivedCategory AX := HasDerivedCategory.standard AX
  let : HasDerivedCategory AS := HasDerivedCategory.standard AS
  let EG := (DerivedCategory.singleFunctor AZ 0).obj G
  let EI := (schemeDerivedDirectImage i).obj EG
  have hEG : schemeDerivedQCohProperty Z EG := AlgebraicGeometry.qc_single G hGqc
  have hEI (j : ℤ) (hj : j ≠ 0) : IsZero ((DerivedCategory.homologyFunctor AX j).obj EI) := by
    obtain ⟨⟨ej⟩, _⟩ := schemeHigherDirectImage_of_affine i EG hEG j
    have hz : IsZero ((DerivedCategory.homologyFunctor AZ j).obj EG) := by
      rcases lt_or_gt_of_ne hj with hj | hj
      · exact DerivedCategory.isZero_of_isGE EG 0 j hj
      · exact DerivedCategory.isZero_of_isLE EG 0 j hj
    exact ((RingedSpace.moduleDirectImage i.toLRSHom.toShHom).map_isZero hz).of_iso ej
  have : EI.IsGE 0 := (DerivedCategory.isGE_iff EI 0).2 (fun j hj ↦ hEI j (by omega))
  have : EI.IsLE 0 := (DerivedCategory.isLE_iff EI 0).2 (fun j hj ↦ hEI j (by omega))
  obtain ⟨V, ⟨eV⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE EI 0
  obtain ⟨⟨eI⟩, _⟩ := schemeHigherDirectImage_of_affine i EG hEG 0
  let e₀ := (DerivedCategory.homologyFunctor AX 0).mapIso eV ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AX 0).app V
  let e₁ := eI ≪≫ (RingedSpace.moduleDirectImage i.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso AZ 0).app G)
  let eVM : V ≅ M := e₀.symm ≪≫ e₁ ≪≫ eM.symm
  let eIM := eV ≪≫ (DerivedCategory.singleFunctor AX 0).mapIso eVM
  obtain ⟨ecomp⟩ := derivedDirectImageComposition i f
  let eout := ecomp.app EG ≪≫ (schemeDerivedDirectImage f).mapIso eIM
  obtain ⟨N, hpos, hN⟩ := (exists_schemeDerivedDirectImage_uniform_truncation_bound (i ≫ f)).1
  refine ⟨N.toNat, ?_⟩
  intro p hp
  have hz := hN ⟨EG, hEG⟩
    (fun j hj ↦ DerivedCategory.isZero_of_isLE EG 0 j hj) p (by omega)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let eR := ((DerivedCategory.homologyFunctor AS p).mapIso eout) ≪≫
    F.homologyRightDerivedFunctorObjSingleFunctorIso M p
  exact hz.of_iso eR.symm

end AlgebraicGeometry.Scheme
