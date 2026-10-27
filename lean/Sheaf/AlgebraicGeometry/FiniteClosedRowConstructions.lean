/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NX and NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Shared finite closed-row constructions

Source: Stacks Project, proetale.tex, Tag 09AH, and homology.tex, Tag 0133;
the displayed signed closed-row construction and diagonal total convention.
(blueprint: def-sfb-finite-closed-row-constructions).

These are the existing constructions relocated from the cover theorem's module,
with the same names and data. Neither the cover theorem nor its comparison is imported.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry

/-- The actual closed restriction endofunctor, inverse image followed by direct image.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedRestriction {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :=
  proEtaleModuleInverseImage i A ⋙ proEtaleRingedDirectImage i A

/-- Zero preservation inherited from the actual inverse-image/direct-image adjunction.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
instance finiteClosedRestriction_zero {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :
    (finiteClosedRestriction i A).PreservesZeroMorphisms :=
  letI := (ProEtaleClosedProjection.adjunction i A).isLeftAdjoint
  letI := (ProEtaleClosedProjection.adjunction i A).isRightAdjoint
  inferInstanceAs ((proEtaleModuleInverseImage i A ⋙ proEtaleRingedDirectImage i
    A).PreservesZeroMorphisms)

/-- The actual adjunction unit, normalized by the existing sectionwise construction.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedUnit {X Z : Scheme.{u}} (i : Z ⟶ X) (A : Sheaf (ProEt.topology X) CommRingCat.{u +
  1}) :
    𝟭 (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ⟶ finiteClosedRestriction i A :=
  (ProEtaleClosedProjection.adjunction i A).unit

/-- Scheme-theoretic intersection: the finite product in the category of schemes over X.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedIntersection {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X)
    (s : Finset (Fin m)) : Over X :=
  ∏ᶜ fun a : s ↦ W a.1

/-- Degree p terms, indexed by strictly increasing (p+1)-tuples. Finite products are biproducts.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedTerms {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1})
    (p : ℕ) : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ ringedSiteModules.{u + 1}
      (proEtaleModuleCoefficients A) :=
  ∏ᶜ fun t : Fin (p + 1) ↪o Fin m ↦
    finiteClosedRestriction (finiteClosedIntersection W (Finset.univ.image t)).hom A

/-- Projection from a row term onto its indicated intersection factor.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedTermProjection {X : Scheme.{u}} {m : ℕ} (W : Fin m → Over X)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (p : ℕ)
    (t : Fin (p + 1) ↪o Fin m) : finiteClosedTerms W A p ⟶
      finiteClosedRestriction (finiteClosedIntersection W (Finset.univ.image t)).hom A :=
  Pi.π _ t

/-- Signed sum of face restrictions, with the sign of the deleted position.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedDifferential {X : Scheme.{u}} {m : ℕ}
    (W : Fin m → Over X) (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (r : ∀ s t : Finset (Fin m),
      finiteClosedRestriction (finiteClosedIntersection W s).hom A ⟶
        finiteClosedRestriction (finiteClosedIntersection W t).hom A)
    (p : ℕ) : finiteClosedTerms W A p ⟶ finiteClosedTerms W A (p + 1) :=
  Pi.lift fun t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (Pi.π _ ((Fin.succAboveOrderEmb j).trans t) ≫
      r (Finset.univ.image ((Fin.succAboveOrderEmb j).trans t)) (Finset.univ.image t))

/-- The total exists by the existing coproducts of module sheaves.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
instance finiteClosedAllTotal {X : Scheme.{u}} (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (K : HomologicalComplex₂ (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) :
    K.HasTotal (ComplexShape.up ℤ) := fun _ ↦ inferInstance

/-- Apply the additive row functor termwise and put horizontal degree first.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedDouble {X : Scheme.{u}} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (R : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ CochainComplex
      (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) [R.Additive] :=
  R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.flipFunctor (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A))
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The ordinary direct-sum total, with differential d_horizontal + (-1)^p d_vertical.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedTotal {X : Scheme.{u}} {A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (R : ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A) ⥤ CochainComplex
      (ringedSiteModules.{u + 1} (proEtaleModuleCoefficients A)) ℤ) [R.Additive] :=
  finiteClosedDouble R ⋙ HomologicalComplex₂.totalFunctor (ringedSiteModules.{u + 1}
    (proEtaleModuleCoefficients A))
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Inverse image preserves zero maps, as a left adjoint between module categories.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
instance finiteClosedInverseZero {X Y : Scheme.{u}} (g : Y ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :
    (proEtaleModuleInverseImage g A).PreservesZeroMorphisms :=
  letI := (ProEtaleClosedProjection.adjunction g A).isLeftAdjoint
  inferInstanceAs ((proEtaleModuleInverseImage g A).PreservesZeroMorphisms)

/-- The recorded module inverse image applied termwise, with inverse-image coefficients.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedPullbackComplex {X Y : Scheme.{u}} (g : Y ⟶ X) (A : Sheaf (ProEt.topology X)
  CommRingCat.{u + 1}) :=
  (proEtaleModuleInverseImage g A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordered closed family after scheme-theoretic base change.
Source: Stacks Project, Tag 09AH; finite-cover construction in the DAG proof.
(blueprint: def-sfb-finite-closed-row-constructions). -/
def finiteClosedPullbackFamily {X Y : Scheme.{u}} {m : ℕ}
    (W : Fin m → Over X) (g : Y ⟶ X) : Fin m → Over Y :=
  fun a ↦ Over.mk (pullback.fst g (W a).hom)

end AlgebraicGeometry
