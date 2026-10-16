/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex
import all Sheaf.Algebra.Homology.UpperTruncationStepSES

/-! # Left exact functors and good upper truncation

Source: Stacks Project, Homology, Tags 0118 and 012K.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v u' v'
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- The canonical comparison between applying an additive functor to a good upper
truncation and truncating its application. It is an isomorphism for a left exact functor.
Source: Stacks Project, Homology, Tags 0118 and 012K.
(blueprint: def-sp-map-good-upper-truncation).

Construction. The mapped truncated complex is zero above q, so its own truncation
inclusion is invertible. Compose its inverse with truncation of the mapped inclusion.
The compatibility equation is naturality of the truncation inclusion. To prove the
left exact comparison invertible, evaluate it below q (both inclusions are invertible),
at q (both inclusions are kernels, and the functor preserves kernels), and above q
(both objects are zero). -/
noncomputable def mapTruncLEComparison (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (q : ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.truncLE q) ⟶
      CochainComplex.truncLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q :=
  inv (CochainComplex.ιTruncLE
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K.truncLE q)) q) ≫
    CochainComplex.truncLEMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (K.ιTruncLE q)) q

/-- The comparison commutes with the inclusion into the full mapped complex. -/
theorem mapTruncLEComparison_ι (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) (q : ℤ) :
    mapTruncLEComparison F K q ≫ CochainComplex.ιTruncLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (K.ιTruncLE q) := by
  dsimp only [mapTruncLEComparison]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality]
  simp

private theorem inclusion_kernel (K : CochainComplex C ℤ) (q : ℤ) :
    ∃ h : (K.ιTruncLE q).f q ≫ K.d q (q + 1) = 0,
      Nonempty (IsLimit (KernelFork.ofι ((K.ιTruncLE q).f q) h)) := by
  have h : (K.ιTruncLE q).f q ≫ K.d q (q + 1) = 0 := by
    rw [← CochainComplex.truncLEXIsoCycles_comp_iCycles]
    simp
  exact ⟨h, ⟨IsKernel.isoKernel _ _ (K.cyclesIsKernel q (q + 1) (by simp))
    (K.truncLEXIsoCycles q) (CochainComplex.truncLEXIsoCycles_comp_iCycles K q)⟩⟩

instance mapTruncLEComparison_isIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex C ℤ) (q : ℤ) : IsIso (mapTruncLEComparison F K q) := by
  suffices h : ∀ p, IsIso ((mapTruncLEComparison F K q).f p) from
    @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ h
  intro p
  have hc := congrArg (fun f ↦ f.f p) (mapTruncLEComparison_ι F K q)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at hc
  rcases lt_trichotomy p q with hp | hp | hp
  · have : IsIso ((K.ιTruncLE q).f p) := isIso_ιTruncLE_f K q p hp
    have : IsIso ((CochainComplex.ιTruncLE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).f p) :=
      isIso_ιTruncLE_f _ q p hp
    have : IsIso ((mapTruncLEComparison F K q).f p ≫ (CochainComplex.ιTruncLE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).f p) := by
      rw [hc]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((CochainComplex.ιTruncLE
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).f p)
  · subst p
    obtain ⟨hz, ⟨hk⟩⟩ := inclusion_kernel K q
    obtain ⟨hz', ⟨hk'⟩⟩ := inclusion_kernel
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q
    let h := (KernelFork.ofι ((K.ιTruncLE q).f q) hz).mapIsLimit hk F
    let e := h.conePointUniqueUpToIso hk'
    have : Mono ((CochainComplex.ιTruncLE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).f q) :=
      Fork.IsLimit.mono hk'
    have he : e.hom = (mapTruncLEComparison F K q).f q := by
      apply (cancel_mono ((CochainComplex.ιTruncLE
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) q).f q)).1
      rw [hc]
      exact h.conePointUniqueUpToIso_hom_comp hk' WalkingParallelPair.zero
    rw [← he]
    infer_instance
  · exact IsZero.isIso
      (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE (K.truncLE q) q p hp))
      (CochainComplex.isZero_of_isStrictlyLE _ q p hp) _
end CochainComplex
