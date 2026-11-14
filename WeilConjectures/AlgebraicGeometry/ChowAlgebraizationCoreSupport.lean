/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-! # Proper support of the compactification algebraization candidate

## References

* Stacks Project, Tag 088E
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Restricting a compactification algebraization whose support avoids the boundary
has proper support (Stacks, Tag 088E). -/
private theorem compactificationRestriction_support
    {S P Y : Scheme.{u}} [IsLocallyNoetherian P]
    (p : P ⟶ S) [IsProper p] (j : Y ⟶ P) [IsOpenImmersion j]
    (F' : CoherentModules P) (F : CoherentModules Y)
    (eF : (Scheme.Modules.tensorPullback j).obj F'.obj ≅ F.obj)
    (hSupport : {x : P | ¬ Subsingleton (F'.obj.presheaf.stalk x)} ⊆ Set.range j) :
    Scheme.Modules.HasSupportProperOver (j ≫ p) F.obj := by
  classical
  have hft := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    P F'.obj).mp F'.property
  have : F'.obj.IsQuasicoherent := hft.1
  have : F'.obj.IsFiniteType := hft.2
  have hs := Scheme.Modules.finiteType_module_support_pullback F'.obj
  let C : TopologicalSpace.Closeds P := ⟨_, hs.1⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have hi : Set.range i = (C : Set P) := by
    simp [i]
  have hir : Set.range i ⊆ Set.range j := hi.le.trans hSupport
  let a := IsOpenImmersion.lift j i hir
  have ha : a ≫ j = i := IsOpenImmersion.lift_fac j i hir
  have : IsClosedImmersion (a ≫ j) := by rw [ha]; infer_instance
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a j
  have har : Set.range a = j ⁻¹' (C : Set P) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      rw [← hi]
      exact ⟨x, (congrArg (fun k ↦ k x) ha).symm⟩
    · intro hy
      obtain ⟨x, hx⟩ := hi.symm ▸ hy
      refine ⟨x, j.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun k ↦ k x) ha).trans hx
  have hPull : {y : Y | ¬ Subsingleton
      (((Scheme.Modules.tensorPullback j).obj F'.obj).presheaf.stalk y)} =
      j ⁻¹' (C : Set P) := (hs.2.2 Y j).2
  have hIso : {y : Y | ¬ Subsingleton (F.obj.presheaf.stalk y)} =
      {y : Y | ¬ Subsingleton
        (((Scheme.Modules.tensorPullback j).obj F'.obj).presheaf.stalk y)} := by
    ext y
    let e := (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapIso eF
    exact not_congr e.toLinearEquiv.toEquiv.subsingleton_congr.symm
  let D : TopologicalSpace.Closeds Y :=
    ⟨Set.range a, a.isClosedEmbedding.isClosed_range⟩
  refine ⟨D, ?_, ?_⟩
  · exact har.trans (hPull.symm.trans hIso.symm)
  · apply (Scheme.closed_subset_proper_over_base_properties (j ≫ p) D).1.mpr
    refine ⟨_, a, inferInstance, rfl, ?_⟩
    rw [← Category.assoc, ha]
    infer_instance

private theorem closed_subset_avoids_boundary
    (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (p : P ⟶ Spec (.of A)) [IsProper p]
    (C : Set P) (hC : IsClosed C) (U : Set P) (hU : IsOpen U)
    (hCU : C ∩ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ U) : C ⊆ U := by
  intro x hx
  by_contra hxU
  let B := C \ U
  have hB : IsClosed B := hC.inter hU.isClosed_compl
  have himage : IsClosed (p '' B) := p.isClosedMap B hB
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (p '' B)).mp himage
  have hpB : p x ∈ PrimeSpectrum.zeroLocus (J : Set A) :=
    hJ ▸ Set.mem_image_of_mem p ⟨hx, hxU⟩
  have hJproper : J ≠ ⊤ := by
    intro ht
    have hjle : J ≤ (p x).asIdeal := hpB
    exact (p x).isPrime.ne_top (top_le_iff.mp (ht ▸ hjle))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJproper
  let m : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hmJ : m ∈ PrimeSpectrum.zeroLocus (J : Set A) := hJM
  have hmB : m ∈ p '' B := hJ.symm ▸ hmJ
  have hIM : I ≤ M := (IsAdicComplete.le_jacobson_bot I).trans
    (sInf_le (show M ∈ {K : Ideal A | ⊥ ≤ K ∧ K.IsMaximal} from ⟨bot_le, hM⟩))
  obtain ⟨y, hy, hpy⟩ := hmB
  have hyV : y ∈ p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    change I ≤ (p y).asIdeal
    rw [hpy]
    exact hIM
  exact hy.2 (hCU ⟨hy.1, hyV⟩)

/-- Proper support for the algebraization constructed on a proper compactification
(Stacks, Tag 088E). -/
theorem chow_algebraization_candidate_support
    (A : Type u) [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {P Y : Scheme.{u}} [IsLocallyNoetherian P]
    (p : P ⟶ Spec (.of A)) [IsProper p] (j : Y ⟶ P) [IsOpenImmersion j]
    (F' : CoherentModules P) (F : CoherentModules Y)
    (eF : (Scheme.Modules.tensorPullback j).obj F'.obj ≅ F.obj)
    (hSupport : {x : P | ¬ Subsingleton (F'.obj.presheaf.stalk x)} ∩
      p ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆ Set.range j) :
    Scheme.Modules.HasSupportProperOver (j ≫ p) F.obj := by
  have hft := (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType
    P F'.obj).mp F'.property
  have : F'.obj.IsQuasicoherent := hft.1
  have : F'.obj.IsFiniteType := hft.2
  have hs := (Scheme.Modules.finiteType_module_support_pullback F'.obj).1
  have hSupport' := closed_subset_avoids_boundary A I p _ hs _
    j.isOpenEmbedding.isOpen_range hSupport
  exact compactificationRestriction_support p j F' F eF hSupport'

end AlgebraicGeometry
