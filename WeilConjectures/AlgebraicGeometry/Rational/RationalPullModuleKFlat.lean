/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import WeilConjectures.Algebra.Homology.AlgebraicInverseImageKFlat
import WeilConjectures.AlgebraicGeometry.ProEtaleEnoughPoints
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # K-flatness of ordinary rational ringed pullback

The inverse image of module sheaves followed by scalar extension along any coefficient map
preserves K-flat complexes, without flatness of the terms.

## Implementation details

The inverse image is the algebraic inverse image on pro-étale topoi, which preserves
K-flatness by the stalk criterion on a conservative family of points; both scalar extensions
preserve K-flatness for every coefficient map.

## References

* Stacks Project, Cohomology on Sites, Tags 0DEN and 0DEP.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Scalar extension along any coefficient map preserves K-flat complexes. -/
theorem pbcExtend_isKFlat {X : Scheme.{u}} {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (P : CochainComplex (pbcModules X R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := S)
      (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  exact SheafOfModules.changeOfRings_isKFlat_independentCoefficients φ P (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose hP

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Inverse image of modules followed by scalar extension along any coefficient map preserves
K-flat complexes. -/
theorem proEtaleRingModulePullback_extend_isKFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    {S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ⟶ S)
    (P : CochainComplex (pbcModules Y R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology Y) (R := R) P) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology X) (R := S)
      (((proEtaleRingModulePullback f R ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
        (Iso.refl _) ⋙ pbcExtend c).mapHomologicalComplex (.up ℤ)).obj P) := by
  classical
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u, u + 1, u + 1, u + 2, u + 1} _ _
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u,
      u + 1, u + 1, u + 2, u + 1} _
  let RI : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
    (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
  let geom : GeometricMorphism
      (Sheaf (ProEt.topology X) (Type (u + 1)))
      (Sheaf (ProEt.topology Y) (Type (u + 1))) :=
    { inverse := proEtaleSheafInverseImage f (Type (u + 1))
      direct := proEtaleSheafDirectImage f (Type (u + 1))
      adj := proEtaleSheafAdjunction f (Type (u + 1))
      leftExact := (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1 }
  let I := SheafOfModules.inverseImageOfUniverses (normalizedAlgebraicLift f R)
  let : Limits.PreservesFiniteLimits (proEtaleModuleInverseImage f R) :=
    proEtaleModuleInverseImage_preservesFiniteLimits f R
  have : (proEtaleModuleInverseImage f R).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : I.modules.Additive := inferInstanceAs (proEtaleModuleInverseImage f R).Additive
  obtain ⟨ι, p, hp⟩ := proEtale_enoughPoints.{u, u} X
  let s : ∀ i, RingedSitePoint RI (p i) :=
    fun i ↦ Classical.choice (RingedSitePoint.nonempty _ (p i))
  have hcons : JointlyReflectIsomorphisms (fun i ↦ (p i).inverse) := by
    constructor
    intro M N a _
    exact hp a (fun i ↦ (isIso_iff_bijective ((p i).inverse.map a)).1 inferInstance)
  have hI := SheafOfModules.AlgebraicInverseImageOfUniverses.isKFlat_of_points
    (ProEt.topology Y) (ProEt.topology X) geom I ι p s hcons P hP
  let F := proEtaleRingExtension f R RI (Iso.refl _)
  let : Limits.PreservesFiniteLimits F :=
    proEtaleRingExtension_preservesFiniteLimits f R RI (Iso.refl _)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have hF := SheafOfModules.changeOfRings_isKFlat_independentCoefficients (Iso.refl RI).hom
    ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) F
    (fun _ ↦ rfl) (fun g ↦ by
      change F.map g = 𝟙 _ ≫ SheafOfModules.changeOfRingsHom (Iso.refl RI).hom _ g ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      rfl) hI
  have hG := SheafOfModules.changeOfRings_isKFlat_independentCoefficients c
    ((F.mapHomologicalComplex (.up ℤ)).obj ((I.modules.mapHomologicalComplex (.up ℤ)).obj P))
    (pbcExtend c) (pbcExtensionExistence c).choose_spec.choose
    (pbcExtensionExistence c).choose_spec.choose_spec.choose hF
  exact hG

end AlgebraicGeometry.Scheme
