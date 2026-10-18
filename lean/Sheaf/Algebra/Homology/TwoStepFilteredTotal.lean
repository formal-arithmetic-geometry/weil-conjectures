/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived

/-!
# Forgetting a two-step filtration

Source: Stacks Project, Tag 03TB; Weil blueprint, trace formal laws, clause (2)
(blueprint: def-trf-two-step-filtered-total).
-/

@[expose] public section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Forget the inclusion `K' ↪ K` and localize its total complex `K`.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total). -/
noncomputable def twoStepTotalComplex :
    TwoStepModuleComplex R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  ObjectProperty.ι _ ⋙ Arrow.rightFunc ⋙ DerivedCategory.Q

/-- Filtered homotopies are ordinary homotopies on total complexes.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total).
Proof: take the total chain homotopy in the definition of the filtered homotopy;
ordinary derived localization identifies its endpoint maps. -/
theorem twoStepTotal_homotopy (K L : TwoStepModuleComplex R) (f g : K ⟶ L)
    (h : twoStepModuleHomotopyRel R f g) :
    (twoStepTotalComplex R).map f = (twoStepTotalComplex R).map g := by
  sorry

/-- Forgetting filtration descended through the filtered chain-homotopy quotient.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total). -/
noncomputable def twoStepTotalHomotopy :
    TwoStepModuleHomotopy R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  CategoryTheory.Quotient.lift (twoStepModuleHomotopyRel R)
    (twoStepTotalComplex R) (twoStepTotal_homotopy R)

/-- A quasi-isomorphism on the subcomplex and quotient is one on the total complex.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total).
Proof: choose a chain representative of the filtered quasi-isomorphism. The two
short exact sequences subcomplex--total--quotient give long exact cohomology sequences.
The five lemma makes its total cohomology maps invertible in every degree. Thus its
image under ordinary derived localization is invertible; descend to homotopy classes. -/
theorem twoStepTotal_inverts :
    (twoStepModuleQuasiIso R).IsInvertedBy (twoStepTotalHomotopy R) := by
  sorry

/-- The canonical total-object functor on the two-step filtered derived category.
It is the localization lift of forgetting the filtration, so its chain normalization
is fixed, with no arbitrary functor or comparison chosen.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total). -/
noncomputable def twoStepTotal :
    TwoStepModuleDerived R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.Construction.lift (twoStepTotalHomotopy R) (twoStepTotal_inverts R)

end CochainComplex
