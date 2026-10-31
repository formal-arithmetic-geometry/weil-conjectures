/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncodingSupplement
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.WeakSerreCoproductClosure
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
public import Mathlib.Order.CompletePartialOrder

/-! # Filtered constructible presentations of the finite discrete weak Serre hull -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

private theorem ordinary_constructible_iff (A : Type u) [CommRing A]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A))) :
    ordinaryConstructible A T M ↔ IsConstructible (ULift.{u + 1} A) M := by
  classical
  rw [ordinaryConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  apply exists_congr
  intro S
  apply forall_congr'
  intro a
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨ULift.{u + 1} C.I₀, fun i ↦ C.X i.down, fun i ↦ C.f i.down,
      by
        convert C.mem₀ using 1
        exact le_antisymm (fun _ _ ⟨i⟩ ↦ ⟨i.down⟩)
          (fun _ _ ⟨i⟩ ↦ ⟨(ULift.up i : ULift.{u + 1} C.I₀)⟩),
      fun i ↦ hC i.down⟩
  · rintro ⟨I, W, g, hg, h⟩
    let C : Scheme.Cover.{u + 1} Scheme.proetalePrecoverage (S.domain a) :=
      ⟨⟨I, W, g⟩, hg⟩
    have : Precoverage.Small.{u} Scheme.proetalePrecoverage :=
      inferInstanceAs (Precoverage.Small.{u} (Scheme.propQCPrecoverage @WeaklyEtale))
    exact ⟨C.restrictIndexOfSmall.{u}, fun i ↦
      h (Precoverage.ZeroHypercover.Small.restrictFun.{u} C i)⟩

set_option synthInstance.maxSize 4096 in
/-- The weak Serre coproduct hull with finite discrete coefficients has filtered
constructible presentations, without a Noetherian hypothesis.
Source: Stacks Tags 03SA(3), 099Y; exact fully faithful étale comparison.
(blueprint: lem-sfb-finite-discrete-serre-ind-constructible).
Proof: the essential image of the étale comparison contains the constructible
modules and is closed under kernels, cokernels, extensions and coproducts. Thus
hull membership supplies an étale antecedent. Present that antecedent as a filtered
colimit of constructible étale modules. Exact coefficient encoding and comparison
preserve this colimit and its constructible stages. Transport the cocone along its
comparison and encoding isomorphisms to obtain the claimed ambient presentation. -/
theorem finiteDiscrete_serre_is_indConstructible
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Internal A X)
    (hM : ObjectProperty.weakSerreCoproductClosure.{u + 1}
      (IsConstantModelConstructible (coefficient A) X) M) :
    ObjectProperty.ind.{u + 1} (IsConstantModelConstructible (coefficient A) X) M := by
  classical
  let e := (encoding_exists A X).some
  let E := e.ordinary.trans e.fixed
  let L := comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X
  let P := IsConstantModelConstructible (coefficient A) X
  let Q := (etaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).inverseImage E.functor
  have hgen : P ≤ Q := by
    intro N hN
    obtain ⟨F, _, ⟨i⟩⟩ := exists_isConstructibleSheaf_iso_comparisonUpperStar_obj
      (ULift.{u + 1} A)
      ((ordinary_constructible_iff A X _).mp ((constructible_comparison A X e N).mp hN))
    exact ⟨F, ⟨i⟩⟩
  have hQ : Q M := hM Q hgen inferInstance inferInstance inferInstance inferInstance
    (fun _ ↦ inferInstance)
  obtain ⟨F, ⟨i⟩⟩ := hQ
  obtain ⟨I, hI, hfiltered, D, hD, ι, ⟨hc⟩⟩ :=
    Scheme.exists_filtered_colimit_constructible F
  let := hI
  let := hfiltered
  let T := L ⋙ E.inverse
  let j : T.obj F ≅ M := E.inverse.mapIso i ≪≫ E.unitIso.symm.app M
  refine ⟨I, hI, hfiltered,
    ⟨D ⋙ T, (T.mapCocone (Cocone.mk F ι)).ι ≫
      (Functor.const I).map j.hom, ?_⟩, ?_⟩
  · exact (isColimitOfPreserves T hc).ofIsoColimit (Cocone.ext j)
  · intro a
    have : Scheme.IsConstructibleSheaf (D.obj a) :=
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hD a)
    apply (constructible_comparison A X e _).mpr
    apply (ordinary_constructible_iff A X _).mpr
    exact isConstructible_of_iso (E.counitIso.app (L.obj (D.obj a))).symm
      (isConstructible_comparisonUpperStar_obj (D.obj a))

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
