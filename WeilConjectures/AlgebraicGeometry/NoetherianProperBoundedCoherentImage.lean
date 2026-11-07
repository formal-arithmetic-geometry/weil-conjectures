/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtension


public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Coherent

import all WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FinitePresentationIntegralFiltration
import WeilConjectures.AlgebraicGeometry.IntegralIdealProperCohomology
import WeilConjectures.AlgebraicGeometry.CohomologyFiniteExtensionExtension
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import Mathlib.Data.Int.Interval
import all WeilConjectures.AlgebraicGeometry.DerivedDirectImageBoundedBelowQCoh
import all WeilConjectures.CategoryTheory.HalfPlaneWeakConvergence

/-! # Bounded coherent direct image in the Noetherian proper case

Source: Stacks Project, Tag 08E2, specialized to a proper morphism; Tag 02O5.
(blueprint: lem-pc-noetherian-proper-bounded-coherent-image).
-/

@[expose] public section
set_option autoImplicit false
universe u wY wT
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme


namespace Modules

/-- Integral-ideal devissage gives finite cohomology over an affine base (Tag 02O6). -/
private theorem finite_sections_proper {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj ℱ, ⊤) := by
  classical
  have : IsLocallyNoetherian T := isLocallyNoetherian_of_isOpenImmersion T.isoSpec.hom
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  let R := Γ(T, ⊤)
  let P (M : X.Modules) : Prop := ∀ n : ℕ,
    letI : Module R (M.H n) := Module.compHom _ f.appTop.hom
    Module.Finite R (M.H n)
  have hzero (M : X.Modules) (hM : IsZero M) : P M := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    have hz (x : M.H n) : x = 0 := by
      have h := congrArg (fun φ ↦ H.map φ n x) (hM.eq_of_src (𝟙 M) 0)
      simpa only [H.map_id_apply, H.map_zero_apply] using h
    have : Subsingleton (M.H n) := ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
    infer_instance
  have hiso {M N : X.Modules} (e : M ≅ N) (hM : P M) : P N := by
    intro n
    let : Module R (M.H n) := Module.compHom _ f.appTop.hom
    let : Module R (N.H n) := Module.compHom _ f.appTop.hom
    let eR : M.H n ≃ₗ[R] N.H n :=
      { H.mapLinearEquiv e n with
        map_smul' := fun a x ↦ (H.mapLinearEquiv e n).map_smul (f.appTop a) x }
    have := hM n
    exact Module.Finite.equiv eR
  obtain ⟨m, c, hc, hbot, htop, hpieces⟩ :=
    exists_finitePresentation_integral_filtration X ℱ
  have hpc : ∀ j : Fin (m + 1), P (c j : X.Modules) := by
    intro j
    induction j using Fin.induction with
    | zero =>
      apply hzero
      exact (Subobject.isoOfEq _ _ hbot ≪≫ Subobject.botCoeIsoZero).isZero_iff.mpr
        (isZero_zero X.Modules)
    | succ j ih =>
      let a := Subobject.ofLE (c j.castSucc) (c j.succ) (hc j.castSucc_le_succ)
      let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel a }
      obtain ⟨Z, i, hi, hZ, I, ⟨e⟩⟩ := hpieces j
      have := hi
      have := hZ
      have hI : P ((pushforward i).obj I.toModules) := by
        intro n
        exact finite_H_pushforward_integral_ideal f Z i I n
      have hQ : P (cokernel a) := hiso e.symm hI
      intro n
      exact finite_H_of_shortExact_extension R f.appTop.hom S hS n (ih n) (hQ n)
  have hF : P ℱ := hiso
    (Subobject.isoOfEq _ _ htop ≪≫ asIso (⊤ : Subobject ℱ).arrow) (hpc _)
  let : Module R (ℱ.H q) := Module.compHom _ f.appTop.hom
  have := hF q
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let eR : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₗ[R] ℱ.H q :=
    { e.toAddMonoidHom with map_smul' := fun a x ↦ e.map_smulₛₗ a x }
  exact Module.Finite.equiv (LinearEquiv.ofBijective eR he).symm


/-- Higher direct images of a finitely presented quasi-coherent module have finite
global sections over a Noetherian affine base under a proper morphism.
Source: Stacks Project, Tag 02O6, by integral-ideal devissage. -/
theorem finite_sections_proper_on_affine {X T : Scheme.{u}} (f : X ⟶ T) [IsProper f]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsFinitePresentation]
    [IsAffine T] [IsNoetherianRing Γ(T, ⊤)] [F.IsQuasicoherent] (q : ℕ) :
    Module.Finite Γ(T, ⊤) Γ((higherDirectImage f q).obj F, ⊤) :=
  finite_sections_proper f F q


end Modules


end AlgebraicGeometry.Scheme
