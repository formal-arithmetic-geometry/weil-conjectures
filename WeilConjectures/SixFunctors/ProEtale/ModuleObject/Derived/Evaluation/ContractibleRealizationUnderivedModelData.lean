/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.TerminalScalarRealization
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationKFlatData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationBraidedData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationSectionsAdjunctionData

/-! Underived data for the terminal scalar realization.

The concrete functor is constructed in TerminalScalarRealization. This statement
records its braided structure, K-flat invariance and terminal sections adjunction;
additivity and flat preservation are proved separately.
The three conjuncts are proved in the modules ContractibleRealizationKFlatData,
ContractibleRealizationBraidedData and ContractibleRealizationSectionsAdjunctionData.
(blueprint: lem-zl-contractible-realization-underived-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

set_option linter.unusedVariables false in
/-- The concrete terminal scalar realization is strong braided, left adjoint to sections,
and preserves quasi-isomorphisms between K-flat complexes.

Source: Hemo--Richarz--Scholbach, Section 3, equations (3.1)--(3.2), Remark 3.2;
Stacks Project, Tags 03D3 and 06YT.
(blueprint: lem-zl-contractible-realization-underived-model-underived-data).

Proof: the three conjuncts are the separate structural statements
`contractible_realization_kflat_data` (cone criterion and sectionwise change of rings),
`contractible_realization_braided_data` (balanced tensor comparison descended through
sheafification) and `contractible_realization_sections_adjunction_data` (constant module
and scalar extension Hom bijections at the terminal object); their witnesses are
packaged into the existential. -/
theorem contractible_realization_underived_data
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U) :
    ∃ (hflat : (terminalScalarRealization J O U hU).PreservesKFlatQuasiIso)
      (hbraid : (terminalScalarRealization J O U hU).Braided),
      Nonempty (terminalScalarRealization J O U hU ⊣ sections J O U) := by
  obtain ⟨hflat⟩ := contractible_realization_kflat_data J O U hU
  obtain ⟨hbraid⟩ := contractible_realization_braided_data J O U hU
  exact ⟨hflat, hbraid, contractible_realization_sections_adjunction_data J O U hU⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
