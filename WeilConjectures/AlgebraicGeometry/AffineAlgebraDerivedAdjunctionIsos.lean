/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionIsos
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedUnitHomologyFactorization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedCounitHomologyFactorization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraDerivedAdjunctionQCoh
import WeilConjectures.AlgebraicGeometry.AffineDerivedCohomology
import WeilConjectures.AlgebraicGeometry.AffineModuleCorrespondence
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedAdjunctionGeneral

/-! # Unit and counit of the affine algebra derived adjunction

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- The ambient derived adjunction has invertible unit and counit at objects with
quasi-coherent cohomology; it need not be an equivalence on the entire derived categories.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof. -/
theorem affine_algebra_derived_adjunction_isos
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (L : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) ⥤
      schemeDerivedCategory X)
    (adj : L ⊣ RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f)) :
    (∀ M : DerivedCategory (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))),
      directImageAlgebraDerivedQCohProperty f M → IsIso (adj.unit.app M)) ∧
    (∀ K : schemeDerivedCategory X, schemeDerivedQCohProperty X K →
      IsIso (adj.counit.app K)) := by
  let g := toDirectImageAlgebraSpace f
  let φ : moduleRings (directImageAlgebraSpace f) ⟶
      ((TopologicalSpace.Opens.map g.hom.base).sheafPushforwardContinuous RingCat.{v}
        (Opens.grothendieckTopology (directImageAlgebraSpace f))
        (Opens.grothendieckTopology X.toRingedSpace)).obj
        (moduleRings X.toRingedSpace) :=
    ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩
  let adj₀ := SheafOfModules.PullbackConstruction.adjunction.{v} φ
  have : Presheaf.IsLocallyInjective
      (Opens.grothendieckTopology X.toRingedSpace)
      (𝟙 (moduleRings X.toRingedSpace).obj) := by infer_instance
  have : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology X.toRingedSpace)
      (𝟙 (moduleRings X.toRingedSpace).obj) := by infer_instance
  let P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace) :=
    SheafOfModules.forget (moduleRings (directImageAlgebraSpace f)) ⋙
    PresheafOfModules.pullback.{v} φ.hom ⋙
    PresheafOfModules.sheafification (R := moduleRings X.toRingedSpace)
      (𝟙 (moduleRings X.toRingedSpace).obj)
  obtain ⟨hexact, hunit, hcounit⟩ := affine_algebra_module_adjunction_isos f P adj₀
  let := hexact
  constructor
  · intro M hM
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    obtain ⟨e, he⟩ :=
      affine_algebra_derived_unit_homology_factorization f P adj₀ L adj M hM n
    have := hunit _ (hM n)
    have : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f))) n).map
        (adj.unit.app M) ≫ e.hom) := by
      rw [he]
      infer_instance
    exact IsIso.of_isIso_comp_right _ e.hom
  · intro K hK
    apply (DerivedCategory.isIso_iff _ _).2
    intro n
    obtain ⟨e, he⟩ :=
      affine_algebra_derived_counit_homology_factorization f P adj₀ L adj K hK n
    have := hcounit _ (hK n)
    rw [he]
    infer_instance

end AlgebraicGeometry
