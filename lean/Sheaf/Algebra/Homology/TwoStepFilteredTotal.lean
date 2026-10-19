/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived

import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

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
  exact DerivedCategory.Q_map_eq_of_homotopy (ModuleCat R) h.choose

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
  intro K L q hq
  obtain ⟨f, rfl, hf⟩ := hq
  change IsIso (DerivedCategory.Q.map f.hom.right)
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2
  have hK : Mono K.as.obj.hom := K.as.property
  have hL : Mono L.as.obj.hom := L.as.property
  let S : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk K.as.obj.hom (cokernel.π _) (cokernel.condition _)
  let T : ShortComplex (CochainComplex (ModuleCat R) ℤ) :=
    ShortComplex.mk L.as.obj.hom (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_cokernel K.as.obj.hom }
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_cokernel L.as.obj.hom }
  let φ : S ⟶ T :=
    { τ₁ := f.hom.left
      τ₂ := f.hom.right
      τ₃ := (coker _).map f.hom
      comm₁₂ := f.hom.w
      comm₂₃ := (coker.π (C := CochainComplex (ModuleCat R) ℤ)).naturality f.hom }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₂ φ hS hT
    (hf true) (hf false)

/-- The canonical total-object functor on the two-step filtered derived category.
It is the localization lift of forgetting the filtration, so its chain normalization
is fixed, with no arbitrary functor or comparison chosen.
Source: Stacks, Tag 03TB (blueprint: def-trf-two-step-filtered-total). -/
noncomputable def twoStepTotal :
    TwoStepModuleDerived R ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Localization.Construction.lift (twoStepTotalHomotopy R) (twoStepTotal_inverts R)

end CochainComplex

