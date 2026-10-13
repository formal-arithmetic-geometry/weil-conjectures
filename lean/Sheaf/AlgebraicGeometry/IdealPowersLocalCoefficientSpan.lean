/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient
import Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Local coefficient expressions for ideal powers

Source: Stacks Project, Tag 02O8, the finite-type assertion in its proof.
-/

@[expose] public section

set_option autoImplicit false
universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Affine core of the local coefficient span argument.  On an affine open `W`,
the ideal-power product section is in the coefficient span of the given affine
generators.  This is the algebraic expansion step in Stacks Tag 02O8.
(blueprint: lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core)
The proof expands the ideal-module product using the extended-ideal formula,
inducts on the recursive ideal power, and rewrites each module factor using
the spanning hypothesis. -/
theorem idealPowersLocalCoefficientSpan_affine {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (r : ℕ) (u : Fin r → Γ(F, U))
    (hu : Submodule.span Γ(X, U) (Set.range u) = ⊤)
    (m : ℕ) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U)
    (t : (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.obj
      (op W)) :
    ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
        W).hom t ∈
      Submodule.span Γ(X, W)
        {z | ∃ (i : Fin r) (a : A), a ∈ I ^ m ∧
          z = (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            f.appLE ⊤ W le_top).hom a) •
              F.val.map (homOfLE hWU).op (u i)} := by
  sorry

theorem idealPowersLocalCoefficientSpan {A : Type v} [CommRing A]
    {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A))
    (I : Ideal A) (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (r : ℕ) (u : Fin r → Γ(F, U))
    (hu : Submodule.span Γ(X, U) (Set.range u) = ⊤)
    (m : ℕ) (V : X.Opens) (hVU : V ≤ U)
    (t : (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.obj
      (op V)) (y : X) (hyV : y ∈ V) :
    ∃ (W : X.Opens) (hWV : W ≤ V), y ∈ W ∧
      ((Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F).app
        W).hom
        ((Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.map
          (homOfLE hWV).op t) ∈
      Submodule.span Γ(X, W)
        {z | ∃ (i : Fin r) (a : A), a ∈ I ^ m ∧
          z = (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
            f.appLE ⊤ W le_top).hom a) •
              F.val.map (homOfLE (hWV.trans hVU)).op (u i)} := by
  classical
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (a := y) hyV V.2
  let tW := (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι m).2 F).val.map
    (homOfLE hWV).op t
  have hcore := idealPowersLocalCoefficientSpan_affine f I J hJ F U hU r u hu m W hW
    (hWV.trans hVU) tW
  refine ⟨W, hWV, hyW, ?_⟩
  dsimp [tW] at hcore
  convert hcore using 1
  · congr 2
  · rfl


end AlgebraicGeometry
