/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedLisseEvaluationModel
public import WeilConjectures.CategoryTheory.ZetaWeil.ContractibleDerivedSectionsTensor

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationUnderivedModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleRealizationOrdinaryUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Evaluation.ContractibleSectionsMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # The contractible scalar realization adjunction

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing.Evaluation

/-- Exact monoidal sections give the scalar realization adjunction with invertible unit.

Source: Hemo--Richarz--Scholbach, Lemma 4.1(1), equations (3.1)--(3.2), Remark 3.2;
Stacks Project Tags 06YY and 06XN
(blueprint: lem-zl-contractible-realization-adjunction).

Proof: use the sectionwise/internal module equivalence to transport the exact,
cocontinuous evaluation in `heval` to actual internal module sections. Constant
realization followed by coefficient extension is left adjoint to these sections:
the adjunction sends a map to its value on constant generators, and its inverse
extends a linear map from sections by the coefficient action. This is the global
sections specialization of the ringed-topos module adjunction. The unit on a free
module is the identity after evaluating the coefficient ring. Coproduct preservation
and a free presentation extend its invertibility to every module, since sections
are exact and extension preserves cokernels. Derive this adjunction on flat-term
K-flat resolutions. Constant realization is exact, the fixed extension model has
its universal K-flat comparison, and exact sections compute their own right derived
functor. In each degree the preceding unit is invertible, so its localized chain
isomorphism is the derived unit. Uniqueness of derived adjunctions identifies this
with the unit for the fixed F and G. Derived tensor pullback supplies F's strong
symmetric monoidal structure. Transport the normalized monoidal sections data in
`heval` along the internal/sectionwise module equivalence and the unique localization
comparisons to obtain a monoidal structure on the fixed G. The localization sizes
need not agree: both comparisons commute with the common cochain localization, so
its universal property transports the tensor, unit, and coherence identities. -/
theorem contractible_realization_adjunction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) [(J.W (A := Ab.{u + 1})).IsMonoidal]
    (O : Sheaf J Ab.{u + 1}) [MonObj O] [IsCommMonObj O]
    (U : C) (hU : IsTerminal U)
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ringSheaf J O)))]
    (heval : ContractibleDerivedSectionsTensor.{u + 1, u, 0} J (ringSheaf J O) (op U)) :
    ∃ adj : F J O U hU ⊣ G J O U,
      IsIso adj.unit ∧ strongSymmetric J O U hU ∧ Nonempty (G J O U).Monoidal := by
  obtain ⟨L, hadd, hflat, hpres, hbraid, ⟨adj₀⟩, ⟨eL⟩⟩ := realization_underived_model J O U hU
  let := hadd
  let := hflat
  let := hpres
  let : L.IsLeftAdjoint := ⟨_, ⟨adj₀⟩⟩
  let adj : F J O U hU ⊣ G J O U := adj₀.derivedAdjunction.ofNatIsoLeft eL
  have hsym : strongSymmetric J O U hU := by
    let := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} (A J O U))
    let := DerivedCategory.braidedCategory' (Mod (Sheaf J Ab.{u + 1}) O)
    let := hbraid
    let b := L.leftDerivedFunctorBraided (fun X Y ↦ by
      simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ,
        Category.comp_id])
    let := b
    let : L.leftDerivedFunctor.Monoidal := b.toMonoidal
    let := Functor.Monoidal.transport eL
    let : NatTrans.IsMonoidal eL.hom :=
      Functor.Monoidal.natTransIsMonoidal_of_transport eL
    exact ⟨{ braided := (Functor.LaxBraided.ofNatIso eL).braided }⟩
  obtain ⟨hlim, hfin, hrest⟩ := heval
  let := hlim
  let := hfin
  have hlim' : PreservesFiniteLimits (sections J O U) := by
    unfold sections
    infer_instance
  have hfin' : PreservesFiniteColimits (sections J O U) := by
    unfold sections
    infer_instance
  let := hlim'
  let := hfin'
  have hcol : PreservesColimitsOfSize.{u + 1, u + 1} (sections J O U) := by
    let := hrest.1
    unfold sections
    infer_instance
  have hu : IsIso adj₀.unit :=
    contractible_realization_ordinary_unit J O U hU hcol L adj₀
  let := hu
  have hhu : IsIso (adj₀.mapHomotopyCategory (.up ℤ)).unit := by
    apply (adj₀.mapHomotopyCategory (.up ℤ)).isIso_unit_of_iso
    exact Functor.mapHomotopyCategoryCompIso (asIso adj₀.unit).symm (.up ℤ) ≪≫
      Functor.mapHomotopyCategoryIdIso _ _
  let := hhu
  have hdu : IsIso adj₀.derivedAdjunction.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    obtain ⟨P, hP, ⟨eP⟩⟩ := L.exists_kFlatKFlatMap_iso X
    rw [← NatTrans.isIso_app_iff_of_iso _ eP]
    have := L.isIso_leftDerivedFunctorCounit_app_of_kFlat' P hP.1
    have hfac := (adj₀.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso _ (.up ℤ)) L.leftDerivedFunctorCounit
      (sections J O U).rightDerivedFunctorUnit P
    have hi : IsIso (adj₀.derivedAdjunction.unit.app (DerivedCategory.Qh.obj P) ≫
        (sections J O U).rightDerivedFunctor.map
          (L.leftDerivedFunctorCounit.app P)) := by
      change IsIso (((adj₀.mapHomotopyCategory (.up ℤ)).derivedη
        (HomotopyCategory.quasiIso _ (.up ℤ)) L.leftDerivedFunctorCounit
        (sections J O U).rightDerivedFunctorUnit).app _ ≫ _)
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      ((sections J O U).rightDerivedFunctor.map (L.leftDerivedFunctorCounit.app P))
  let := hdu
  have hunit : IsIso adj.unit := by
    dsimp only [adj]
    rw [Adjunction.ofNatIsoLeft_unit]
    infer_instance
  obtain ⟨m⟩ := contractible_sections_monoidal J O U ⟨hlim, hfin, hrest⟩ hlim' hfin'
  let := m
  have hm : Nonempty (G J O U).Monoidal := by
    exact ⟨Functor.Monoidal.transport
      (sections J O U).rightDerivedFunctorIsoMapDerivedCategory.symm⟩
  exact ⟨adj, hunit, hsym, hm⟩

end AlgebraicGeometry.ProEtale.CondensedRing.Evaluation
