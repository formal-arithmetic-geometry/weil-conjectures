/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.StructureSheafCohomologyPullback

import WeilConjectures.AlgebraicGeometry.Structure.StructureDerivedImageCohomologyEquivalences
import WeilConjectures.AlgebraicGeometry.Structure.StructureDerivedImageCohomologyCompatibility

/-! # Naturality of affine-base sections of a structure-module direct image

Source: Stacks Project, Tags 01XK, 01FB and 03FD.
(blueprint: new-structure-derived-image-cohomology-naturality)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 1600000 in
-- Composing the module and abelian comparisons requires large category transports.
/-- The affine-base Leray comparison for structure modules respects a map of total spaces.
Source: Stacks Project, Tag 01XK, lemma-quasi-coherence-higher-direct-images-application;
Tag 01FB, remark-explain-arrow; Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: new-structure-derived-image-cohomology-naturality)

Proof: By `structure_derived_image_module_naturality`, the affine Leray edges (invertible
by quasi-coherence of higher direct images and affine acyclicity) give one additive
equivalence `em` from sections of degree-one cohomology of `Rq_* O_X` to module cohomology
`H^1(X, O_X)`, and for every index an equivalence `emi` carrying `H(b i)` to the module
h-map of the structure map of `j i`. By `structure_module_abelian_comparison`, the fixed
injective-resolution comparison `ea` identifies structure-module cohomology with abelian
sheaf cohomology and carries the module h-map of every scheme morphism to
`structureSheafCohomologyPullback`. Take `e = em.trans (ea X)` and
`ei = emi.trans (ea (Xi i))`; applying the two squares in turn gives the equation. The
source equivalence does not depend on the index, so the empty family needs nothing more. -/
theorem structure_derived_image_cohomology_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q]
    {n : ℕ} (Xi : Fin n → Scheme.{v}) (qi : ∀ i, Xi i ⟶ T)
    [∀ i, IsProper (qi i)] (j : ∀ i, Xi i ⟶ X) (hj : ∀ i, j i ≫ q = qi i) :
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)
    let Ai := fun i ↦ (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (Xi i).toRingedSpace)) 0).obj
        (SheafOfModules.unit (Xi i).ringCatSheaf)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
      SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)
    let b := fun i ↦ relativeMVUnit (j i) q A ≫
      (schemeDerivedDirectImage (j i ≫ q)).map
        (Modules.canonicalSinglePullbackMap (j i) (SheafOfModules.unit X.ringCatSheaf) ≫
          (DerivedCategory.singleFunctor _ 0).map (Modules.pullbackObjUnitIso (j i)).hom) ≫
      eqToHom (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj (Ai i)) (hj i))
    ∃ e : H.obj ((schemeDerivedDirectImage q).obj A) ≃+
        Sheaf.H (structureSheafAb X) 1,
      ∀ i, ∃ ei : H.obj ((schemeDerivedDirectImage (qi i)).obj (Ai i)) ≃+
          Sheaf.H (structureSheafAb (Xi i)) 1,
        ∀ z, ei (H.map (b i) z) = structureSheafCohomologyPullback (j i) 1 (e z) := by
  classical
  dsimp only
  obtain ⟨em, hem⟩ := structure_derived_image_module_naturality q Xi qi j hj
  obtain ⟨ea, hea⟩ := structure_module_abelian_comparison
  refine ⟨em.trans (ea X), ?_⟩
  intro i
  obtain ⟨emi, hemi⟩ := hem i
  refine ⟨emi.trans (ea (Xi i)), ?_⟩
  intro z
  change ea (Xi i) (emi _) = _
  rw [hemi]
  exact hea (j i) (em z)

end AlgebraicGeometry.Scheme
