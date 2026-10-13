/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Sheaf.AlgebraicGeometry.MixedGlobalExtension
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineKFlatPullbackChartComparison

/-! # Invertibility of the mixed affine comparison on K-flat models

Source: Stacks Project, Tags 08DW(2), 06Z0, 08HY and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-kflat-comparison-isIso).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical affine comparison is invertible on K-flat module models.
Source: Stacks Project, perfect.tex, Tags 06Z0 and 08DW(2);
cohomology.tex, Tags 08HY and 0D5T; duality.tex, Tag 0AA8.
(blueprint: lem-sc-mixed-affine-sections-kflat-comparison-isIso).

Proof: Identify the affine schemes with spectra of their global rings. Use the given
K-flat module complex P and its termwise tilde, restricted through the spectrum chart of S.
The tilde/pullback comparison identifies its pullback with extension of scalars.
Taking derived sections of this comparison gives an isomorphism. On complexes its
adjunct is sections of the pullback unit, followed by the identity-on-sections
comparison for direct image. Deriving that equality identifies the latter comparison
with the normalized Leray isomorphism, using its right-derived-unit equation.
Uniqueness of the left adjoint to scalar restriction identifies the source functor
with mixedGlobalExtension, preserving the unit. Hence the canonical adjunct displayed
below is precisely this isomorphism's hom and is invertible. The two derived
localizations can be taken in independent universes. For P=0 or an empty affine
scheme this is the unique morphism between zero objects and remains invertible. -/
theorem mixedAffineSections_kFlat_comparison_isIso
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) (P : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Γ(S, ⊤)) (.up ℤ)).kFlat P) :
    let Q := DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (SheafOfModules.{u} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace) ⥤
            SheafOfModules.{u} (moduleRings S.toRingedSpace))
            (Scheme.Modules.restrictFunctor S.toSpecΓ))
          (by change (Scheme.Modules.restrictFunctor S.toSpecΓ).PreservesZeroMorphisms
              infer_instance) (.up ℤ)).obj
            ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
              (@id (ModuleCat.{u} Γ(S, ⊤) ⥤
                SheafOfModules.{u} (moduleRings (Spec Γ(S, ⊤)).toRingedSpace))
                (tilde.functor Γ(S, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj P))
    IsIso (((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
      ((schemeDerivedGlobalSections S).map ((schemeHomPullbackAdjunction g).unit.app Q) ≫
        (mixedGlobalSectionsDirectImageIso g).hom.app ((derivedPullback g).obj Q))) := by sorry

end AlgebraicGeometry
