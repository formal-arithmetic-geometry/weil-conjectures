/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated


import WeilConjectures.AlgebraicGeometry.QCohAcyclicDerivedSectionsTruncationIso
import WeilConjectures.AlgebraicGeometry.DerivedSectionsLeftExactBottom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Topology.RingedSpaceModuleEnoughInjectives

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- On the full category of affine opens of `Y`, derived section cohomology of an
object with quasi-coherent cohomology agrees with sections of its cohomology sheaf
(Stacks, Tags 08D4 and 08D5). -/
theorem qcoh_acyclic_derived_sections_comparison_sections {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) :
    Nonempty
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedSectionPresheaf f i ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj ≅
        (schemeDerivedQCohProperty X).ι ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i ⋙
          RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
          SheafOfModules.forget (moduleRings Y.toRingedSpace) ⋙
          PresheafOfModules.pushforward₀
            (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
            (moduleRings Y.toRingedSpace).obj) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj
  let S := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    SheafOfModules.forget (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard D
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : S.Additive := by dsimp [S]; infer_instance
  have : PreservesFiniteLimits S := by
    let T := PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj
    have : PreservesFiniteLimits (S ⋙ T) := by
      change PreservesFiniteLimits
        ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
          PresheafOfModules.toPresheaf (moduleRings X.toRingedSpace).obj) ⋙
          (Functor.whiskeringLeft _ _ _).obj (TopologicalSpace.Opens.map f.base).op)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves S T
  let P := PresheafOfModules.pushforward₀
    (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
    (moduleRings Y.toRingedSpace).obj
  let ι := (schemeDerivedQCohProperty X).ι
  let H := DerivedCategory.homologyFunctor D i
  let τ := Functor.whiskerLeft ι
    (Functor.whiskerRight (Functor.whiskerRight (Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncGEπ i) S.rightDerivedFunctor) H) P)
  have (E : schemeDerivedQCohCategory X) : IsIso (τ.app E) :=
    qcoh_acyclic_derived_sections_truncation_isIso f hacyc i E
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  obtain ⟨e⟩ := S.rightDerivedFunctor_truncated_bottom i
  exact ⟨asIso τ ≪≫ Functor.isoWhiskerLeft ι (Functor.isoWhiskerRight e P)⟩

end AlgebraicGeometry
