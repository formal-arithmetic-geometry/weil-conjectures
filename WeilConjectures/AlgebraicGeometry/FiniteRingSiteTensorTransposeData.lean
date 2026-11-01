/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
/-!
# Finite-ring transport of projection maps and integration transposes

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-smooth-purity/
sk-thm-smooth-purity-general-ring.proof.md, Proof (3), and
lem-pur-finite-ring-site-tensor-transpose, assertions 1--3
(blueprint: def-pur-finite-ring-site-tensor-transport-data).

All categories below are ordinary unbounded categories with constant finite coefficients.
The pro-etale closure is the recorded closure transported by the finite-discrete ring
identification. The auxiliary abbreviations expose the specified functors and canonical maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u uA v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Exact, termwise site inverse image. Source: blueprint, assertion 1
(blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingSitePull (B : Type) [CommRing B] [Finite B] (T : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} B)) T).mapDerivedCategory

/-- Ordinary etale compact supports for the fixed compactification.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingEtaleShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- Ordinary pro-etale compact supports before restriction to the localizing closure.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingProShriek (B : Type) [CommRing B] {X Y : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) c

/-- The canonical pro-etale projection-map component, with abstract coefficients.
Source: blueprint assertion 2 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
@[irreducible] def finiteRingProPF
    (A : Type uA) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriekOfCompactification A c).obj M ⊗ K ⟶
      (rightDerivedLowerShriekOfCompactification A c).obj
        (M ⊗ (upperStar A f).leftDerivedFunctor.obj K) :=
  ((projectionMapOfCompactification A c).app M).app K

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

/-- Restriction of a functor to the indicated full subcategories.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingRestriction
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (h : ∀ N, P N → Q (F.obj N)) :=
  Q.lift (P.ι ⋙ F) (fun N ↦ h N.obj N.property)

/-- Restriction of the codomain of the exact site comparison to its image.
Source: blueprint assertion 1 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
abbrev finiteRingImageLift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (E : C ⥤ D) (P : ObjectProperty D) (h : ∀ M, P (E.obj M)) :=
  P.lift E h

/-- The composite tensor and pullback comparison, retaining its specified two factors.
Source: blueprint proof step 5 (blueprint: lem-pur-finite-ring-site-tensor-transpose). -/
def finiteRingTensorPullbackComparison
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D]
    {C' : Type u₃} [Category.{v₃} C'] [MonoidalCategory C']
    {D' : Type u₄} [Category.{v₄} D']
    (E : C ⥤ C') (P : D ⥤ C) (P' : D' ⥤ C') (E' : D ⥤ D')
    (tensor : ∀ M N, E.obj (M ⊗ N) ≅ E.obj M ⊗ E.obj N)
    (pullback : ∀ K, E.obj (P.obj K) ≅ P'.obj (E'.obj K))
    (M : C) (K : D) :
    E.obj (M ⊗ P.obj K) ≅ E.obj M ⊗ P'.obj (E'.obj K) :=
  tensor M (P.obj K) ≪≫ tensorIso (Iso.refl _) (pullback K)

end AlgebraicGeometry.ProEtale
