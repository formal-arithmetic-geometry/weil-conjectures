/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Compact.CompactSupportRepresentativeIndependence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-! # The existing compact-support realization predicate

The predicate is unchanged; its own module prevents repeated checking of its large
choice telescope while compiling the finite-action constructions.
(blueprint: def-weil-compact-support-finite-realization-predicate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence unrestrictedIntegralReductionExistence
  constantSheaf
  sfIntegralCompactSupportValue
  Padic.coefficientExtensionIdeal

section FiniteAction
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- A realization of compact support with condensed coefficients is a natural
isomorphism to `Rp_* j_!` for the specified compactification. This definition applies
in particular to discrete finite rings and to the condensed rings `O_E`, `E` and
`Qbar_ell`. The ambient categories are categories of modules over `Λ_X = p_X^* Λ`.
Compactification independence is asserted separately on the appropriate subcategories.

Source: blueprint latest, part-six-operations/sec-six-functors/sec-n-change/
sk-prop-qlbar-two-colimit/det-def-sf-operations.md, clause (iv)
(blueprint: def-weil-compact-support-finite-realization-predicate). -/
def SfCompactSupportFiniteRealizationSpec
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (F : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (ProEtale.condensedRingObj Λ X)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (ProEtale.condensedRingObj Λ Y))) :
    Prop :=
  Nonempty (F ≅ ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification Λ c)

end FiniteAction
end WeilConjectures
