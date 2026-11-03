/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModelData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationDerivedComparison

/-! An ordinary module model for scalar realization.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
(blueprint: lem-zl-contractible-realization-underived-model).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

set_option linter.unusedVariables false in
/-- An ordinary scalar-extension/constant-module left adjoint whose total left derivative
is the fixed realization functor.  No exactness assumption on sections is required.

Source: Hemo--Richarz--Scholbach, Section 3, Remark 3.2; Stacks 03D3 and 06YY.
(blueprint: lem-zl-contractible-realization-underived-model).

Proof: put L(M) equal to the internal module associated with the sheafification of
V ↦ O(V) tensor_A M, with restrictions induced by those of O and by U's terminal maps.
Tensor adjunction and sheafification adjunction identify maps L(M) → N with A-linear
maps M → N(U), naturally in both arguments. This proves the ordinary adjunction.
Addition of maps is preserved sectionwise. Give L its strong symmetric structure by
the balanced map (a tensor x) tensor (b tensor y) ↦ ab tensor (x tensor y), with inverse
inserting 1; tensor associativity, unit and symmetry are checked on these generators.
If M is flat over A, tensoring with L(M) identifies with sheafification of tensoring
section modules with M, hence is exact. Thus L preserves flat objects. An acyclic K-flat A-complex
remains acyclic
after tensoring with each O(V), so L preserves quasi-isomorphisms between K-flat complexes.
For a flat-term K-flat A-resolution P, exact constant sheafification carries P to a
flat-term K-flat constant-coefficient complex: the tensor identity is checked on
constant generators and descends by exact sheafification. The fixed extension model's
counit is therefore invertible there, and identifies F(Q(P)) with Q(L(P)). These
comparisons are natural in resolutions and their maps. The universal left-derived
property yields the claimed natural isomorphism, including its comparison with Q.
The section-module equivalence is exact and commutes with localization. -/
theorem realization_underived_model
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    : ∃ (L : ModuleCat.{u + 1} (A J O U) ⥤ Mod (Sheaf J Ab.{u + 1}) O)
      (hadd : L.Additive),
      letI := hadd
      ∃ (hflat : L.PreservesKFlatQuasiIso) (hpres : L.PreservesFlat)
        (hbraid : L.Braided),
        letI := hflat
        Nonempty (L ⊣ sections J O U) ∧
          Nonempty (L.leftDerivedFunctor ≅ F J O U hU) := by
  let L := terminalScalarRealization J O U hU
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u} J O
  let R := ringSheaf J O
  let E := SheafOfModules.flatScalarRealization J (scalarMap J O U hU)
  have hadd : L.Additive := inferInstance
  have hpres : L.PreservesFlat := by
    constructor
    intro M hM
    apply (InternalAbelianSheafModule.flat_iff_sectionModule J O (L.obj M)).mpr
    have hf := SheafOfModules.flatScalarRealization_flat J (scalarMap J O U hU) M
      ((ModuleCat.flat_iff_flat M).mp hM)
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.symmetricCategory R
    let t := SheafOfModules.siteSheafTensorRightIso R (e.functor.obj (L.obj M)) ≪≫
      (MonoidalCategory.curriedTensor _).flip.mapIso (e.counitIso.app (E.obj M)) ≪≫
      (SheafOfModules.siteSheafTensorRightIso R (E.obj M)).symm
    exact (exactFunctor _ _).prop_of_iso t.symm hf
  obtain ⟨hflat, hbraid, hadj⟩ := contractible_realization_underived_data J O U hU
  let := hflat
  refine ⟨L, hadd, hflat, hpres, hbraid, hadj, ?_⟩
  exact contractible_realization_derived_comparison J O U hU L hadj

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
