/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover

/-!
# The section invariant in finite comparison coordinates

Source: blueprint main-20261015, def-pur-section-invariant, displayed definition
(blueprint: def-pur-section-invariant).

The object is the actual derived pullback of the transported dualizing object.
The explicit comparison below identifies its canonical etale presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The actual section invariant, using the canonical unit-normalized exceptional image.
Source: blueprint def-pur-section-invariant (blueprint: def-pur-section-invariant). -/
def comparedSectionInvariant (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :=
  (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) s).leftDerivedFunctor.obj
    (ProEtale.finiteComparedDualizing P g)

/-- The canonical comparison identifying the actual derived pullback with its etale model.
Source: blueprint section invariant and its specified coefficient comparison
(blueprint: def-pur-section-invariant). -/
def comparedSectionPresentation (P : PurityFiniteSetting.{u}) {V B : Scheme.{u}}
    (g : V ⟶ B) [HasCompactification g] (s : B ⟶ V) :
    P.comparedSectionInvariant g s ≅
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
        (Etale.sectionInvariant P.Coefficient g s) :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
    (ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} P.Coefficient) s).app _ ≪≫
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} P.Coefficient) s).app _).symm

/-- The section object and a two-sided inverse lie in the stated finite-Tor category.
Source: blueprint def-pur-section-invariant, invertibility paragraph
(blueprint: def-pur-section-invariant).
Proof: cover the smooth source by its finitely many dimension loci. Cohomological
smoothness gives the invertible dualizing complex on each locus. Finite gluing gives
its two-sided inverse globally. Pull both inverse identities along the closed section;
monoidal pullback preserves the unit, tensor, constructibility and finite Tor amplitude.
The section identity gives uniform bounds, also for the empty scheme. -/
theorem comparedSectionInvariant_invertible (P : PurityFiniteSetting.{u})
    {V B : Scheme.{u}} (g : V ⟶ B) [HasCompactification g] [Smooth g]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} P.Coefficient) B (P.comparedSectionInvariant g s) ∧
    ∃ Q : DerivedCategory
        (Sheaf (Scheme.ProEt.topology B) (ModuleCat.{u + 1} P.Coefficient)),
      ProEtale.DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} P.Coefficient) B Q ∧
      Nonempty (P.comparedSectionInvariant g s ⊗ Q ≅ 𝟙_ _) ∧
      Nonempty (Q ⊗ P.comparedSectionInvariant g s ≅ 𝟙_ _) := by
  sorry

end WeilConjectures.PurityFiniteSetting
