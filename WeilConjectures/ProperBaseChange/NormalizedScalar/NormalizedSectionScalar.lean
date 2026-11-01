/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.NormalizedScalar.NormalizedCoefficientModel
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarNormalizationExistence
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses

/-! # Section normalization for the given integral-to-field coefficient map -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.NormalizedScalar

/-- The standard derived localization of the section-module category, in its site universe.
Source: Grothendieck abelian categories have their standard derived category.
(blueprint: lem-weil-pbc-normalized-section-scalar). -/
@[instance_reducible] def sectionDerived
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] (T : Scheme.{u}) :
    HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules A T) :=
  @HasDerivedCategory.ofIsGrothendieckAbelian _ _ _
    (SheafOfModules.isGrothendieckAbelianOfUniverses.{u + 1, u, u + 1, 0}
      (Scheme.ProEt.topology T) _)

/-- The existing section-normalization predicate for the actual condensed inclusion.
Source: normalized internal/section tensor comparison.
(blueprint: lem-weil-pbc-normalized-section-scalar). -/
def SectionData (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] (T : Scheme.{u}) : Prop :=
  letI := fun X : Scheme.{u} ↦
    sectionDerived (Profinite.continuousCoefficientRingObj (integers l E)) X
  letI := fun X : Scheme.{u} ↦ sectionDerived (Profinite.continuousCoefficientRingObj E) X
  ∃ s : QuotientChange.SectionScalarComparison (scalarMap (l := l) (E := E)) T,
    QuotientChange.SectionScalarNormalized (scalarMap (l := l) (E := E)) T s

/-- The actual coefficient map has the section comparison with identity restriction
and the specified balanced tensor-generator normalization.
Source: normalized section scalar adjunction and derived normalization.
(blueprint: lem-weil-pbc-normalized-section-scalar).
Proof: supply the standard derived categories of the section-module categories,
then apply the existing normalization theorem to the actual condensed inclusion.
This preserves its restriction, tensor-generator, and K-flat-computation equations. -/
theorem section_normalized (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] (T : Scheme.{u}) : SectionData l E T := by
  let (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      [MonObj A] [IsCommMonObj A] (X : Scheme.{u}) :
      HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules A X) := sectionDerived A X
  exact QuotientChange.internal_section_scalar_normalization_exists
    (scalarMap (l := l) (E := E)) T

end WeilConjectures.NormalizedScalar
