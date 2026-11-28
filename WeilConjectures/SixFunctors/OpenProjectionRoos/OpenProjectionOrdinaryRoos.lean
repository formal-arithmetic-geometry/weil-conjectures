/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosExtensionComparison
import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosRestrictionUnit
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosProducts
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionOrdinaryComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProductsOfUniverses
import all WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus

/-! # Transport of the ordinary open tensor and signed Roos comparisons

## Implementation details

The Roos comparisons come from countable product preservation (open extension by zero preserves
products on the pro-étale site). The open units are invertible because the open is subterminal.
Restriction preserves good complexes since tensoring with a restriction is the restriction of
tensoring with an extension. The ordinary comparison is `ordinaryProjection_exists`.

## References

* Stacks Project, Tags 09BP, 03DI, 0GL1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private theorem openObject_mono :
    Mono (terminal.from (IntegralOpenReduction.openObject j)) := by
  have hU : ∀ V : X.ProEt, Subsingleton (V ⟶ IntegralOpenReduction.openObject j) := by
    intro V
    constructor
    intro f g
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).mp
    exact (MorphismProperty.Over.w f).trans (MorphismProperty.Over.w g).symm
  exact ⟨fun {V} f g _ ↦ (hU V).elim f g⟩

private theorem localizedUnit_isIso :
    IsIso (SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1}
      (completedIntegralCommRingSheafUnrestricted l E X)
      (IntegralOpenReduction.openObject j)).unit := by
  have := openObject_mono j
  exact SheafOfModules.SubterminalLocal.adj_unit_isIso.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)

/-- The unit of the ordinary open extension-restriction adjunction is an isomorphism. -/
theorem ordinaryAdjunction_unit_isIso :
    IsIso (IntegralOpenReduction.ordinaryAdjunction l E j o).unit := by
  have := localizedUnit_isIso l E j
  let a := SheafOfModules.localizedSystemAdjunction.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  have h := (o.integral.fullyFaithfulFunctor).comp a.fullyFaithfulLOfIsIsoUnit
  have : (IntegralOpenReduction.extension l E j o).Full := h.full
  have : (IntegralOpenReduction.extension l E j o).Faithful := h.faithful
  exact (IntegralOpenReduction.ordinaryAdjunction l E j o).unit_isIso_of_L_fully_faithful

/-- The unit of the derived open extension-restriction adjunction is an isomorphism. -/
theorem openAdjunction_unit_isIso
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)] :
    IsIso (IntegralOpenReduction.openAdjunction l E j o).unit := by
  have hu := ordinaryAdjunction_unit_isIso l E j o
  let adj := IntegralOpenReduction.ordinaryAdjunction l E j o
  let a := IntegralOpenReduction.openAdjunction l E j o
  have hQ (P : CochainComplex (scalarReductionSource l E U) ℤ) :
      IsIso (a.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) := by
      have hn : ∀ n : ℤ,
          IsIso (((adj.mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
        fun n ↦ (NatTrans.isIso_iff_isIso_app _).mp hu (P.X n)
      exact HomologicalComplex.Hom.isIso_of_components _
    have he : a.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          (IntegralOpenReduction.restriction l E j o).mapDerivedCategoryFactors.inv.app _ ≫
            (IntegralOpenReduction.restriction l E j o).mapDerivedCategory.map
              ((IntegralOpenReduction.extension l E j o).mapDerivedCategoryFactors.inv.app P) := by
      simp only [a, IntegralOpenReduction.openAdjunction,
        SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction,
        Adjunction.mapExactDerivedCategory, Adjunction.localization_unit_app]
      rfl
    rw [he]
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  exact (NatTrans.isIso_app_iff_of_iso a.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
    (hQ (DerivedCategory.Q.objPreimage M))

/-- Ordinary open extension preserves countable products. -/
theorem extension_preservesCountableProducts [QuasiCompact j] :
    PreservesLimitsOfShape (Discrete ℕ) (IntegralOpenReduction.extension l E j o) := by
  let L := SheafOfModules.localizedSystemExtension.{u + 1, u, u + 1}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  have : IsOpenImmersion (IntegralOpenReduction.openObject j).hom :=
    inferInstanceAs (IsOpenImmersion j)
  have : QuasiCompact (IntegralOpenReduction.openObject j).hom :=
    inferInstanceAs (QuasiCompact j)
  have (M : ℕ → _) : PreservesLimit (Discrete.functor M) L := by
    have := Scheme.proEtaleRingedExtensionByZero_products_of_universes.{u, u + 1}
      (IntegralOpenReduction.openObject j)
      (completedIntegralCommRingSheafUnrestricted l E X) M
    exact PreservesProduct.of_iso_comparison L M
  have : PreservesLimitsOfShape (Discrete ℕ) L := preservesLimitsOfShape_of_discrete L
  change PreservesLimitsOfShape (Discrete ℕ) (o.integral.functor ⋙ L)
  infer_instance

/-- Ordinary open restriction preserves countable products. -/
theorem restriction_preservesCountableProducts :
    PreservesLimitsOfShape (Discrete ℕ) (IntegralOpenReduction.restriction l E j o) := by
  have := (IntegralOpenReduction.ordinaryAdjunction l E j o).rightAdjoint_preservesLimits.{0, 0}
  infer_instance

/-- Open restriction preserves flatness of module sheaves: tensoring with a restriction is
restriction of tensoring with an extension, by the ordinary projection isomorphism. -/
theorem restriction_isFlatOnSite
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (t : OpenSemilinearTensor.TotalComparison l E j o) (M : scalarReductionSource l E X)
    (hM : SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E X) M) :
    SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (R := completedIntegralCommRingSheafUnrestricted l E U)
      ((IntegralOpenReduction.restriction l E j o).obj M) := by
  let RX := completedIntegralCommRingSheafUnrestricted l E X
  let RU := completedIntegralCommRingSheafUnrestricted l E U
  let ext := IntegralOpenReduction.extension l E j o
  let res := IntegralOpenReduction.restriction l E j o
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RU
  let := SheafOfModules.monoidalCategory RX
  let := SheafOfModules.monoidalCategory RU
  have := ordinaryAdjunction_unit_isIso l E j o
  have hX : exactFunctor _ _ (MonoidalCategory.tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (SheafOfModules.siteSheafTensorRightIso RX M) hM
  have : PreservesFiniteLimits (MonoidalCategory.tensorRight M) :=
    ((exactFunctor_iff _).1 hX).1
  have : PreservesFiniteColimits (MonoidalCategory.tensorRight M) :=
    ((exactFunctor_iff _).1 hX).2
  let η : ext ⋙ MonoidalCategory.tensorRight M ≅
      MonoidalCategory.tensorRight (res.obj M) ⋙ ext :=
    NatIso.ofComponents (fun N ↦ t.ordinary N M) (by
      intro N N' f
      have h := t.ordinary_naturality f (𝟙 M)
      simp only [SemilinearSections.ordinaryTensorHom, CategoryTheory.Functor.map_id,
        MonoidalCategory.tensorHom_id] at h
      exact h)
  let e : MonoidalCategory.tensorRight (res.obj M) ≅
      (ext ⋙ MonoidalCategory.tensorRight M) ⋙ res :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (asIso (IntegralOpenReduction.ordinaryAdjunction l E j o).unit) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight η.symm res
  have hU : exactFunctor _ _ (MonoidalCategory.tensorRight (res.obj M)) :=
    (exactFunctor _ _).prop_of_iso e.symm ((exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩)
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso RU (res.obj M)).symm hU

/-- Open restriction preserves K-flatness: the total tensor with a restriction is detected
after extension, where it becomes the total tensor with an extension. -/
theorem restriction_isKFlat
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (t : OpenSemilinearTensor.TotalComparison l E j o)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E U)
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P) := by
  let ext := IntegralOpenReduction.extension l E j o
  have := ordinaryAdjunction_unit_isIso l E j o
  have : ext.Faithful :=
    (IntegralOpenReduction.ordinaryAdjunction l E j o).fullyFaithfulLOfIsIsoUnit.faithful
  unfold CochainComplex.IsKFlatIndependentCoefficients at hP ⊢
  intro F hF
  have hextF : ((ext.mapHomologicalComplex (.up ℤ)).obj F).Acyclic := fun n ↦ (hF n).map ext
  have h1 := hP _ hextF
  have h2 : ((ext.mapHomologicalComplex (.up ℤ)).obj ((OpenSemilinearTensor.total l E U).obj
      (F, (OpenSemilinearTensor.restrictionComplex l E j o).obj P))).Acyclic :=
    fun n ↦ (h1 n).of_iso (t.chain F P)
  intro n
  exact ((((OpenSemilinearTensor.total l E U).obj
    (F, (OpenSemilinearTensor.restrictionComplex l E j o).obj P)).sc n).exact_map_iff_of_faithful
      ext).mp (h2 n)

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

/-- Open restriction preserves complexes that are K-flat with flat terms. -/
theorem restrictionComplex_good
    [PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (t : OpenSemilinearTensor.TotalComparison l E j o)
    (P : CochainComplex (scalarReductionSource l E X) ℤ)
    (hP : integralOperationsGoodComplex l E X P) :
    integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P) := by
  exact ⟨restriction_isKFlat l E j o t P hP.1,
    fun i ↦ restriction_isFlatOnSite l E j o t (P.X i) (hP.2 i)⟩

/-- Ordinary descent and signed Roos comparison in the global coefficient presentation:
there are Roos comparisons for open extension and restriction, the module and derived
open units are isomorphisms, restriction preserves good complexes, and there is an ordinary
open tensor comparison satisfying the ordinary representative equation. -/
theorem openProjectionOrdinaryRoos
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    :
    ∃ (_extension : RoosComparison (IntegralOpenReduction.extension l E j o)),
    ∃ (_restriction : RoosComparison (IntegralOpenReduction.restriction l E j o)),
    ∃ (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o),
    ∃ (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit),
    ∃ (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o),
    ∃ (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit),
    ∃ (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P)),
    ∃ (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o),
    OrdinaryRepresentative l E j o SX SU AX AU st m c q flat extendGood restrictGood ordinary := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of D.k))
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U ↘ Spec (.of D.k))
  have : IsNoetherian U := {}
  have : QuasiCompact j :=
    @quasiCompact_of_noetherianSpace_source U X (IsNoetherian.noetherianSpace (X := U)) j
  have := extension_preservesCountableProducts l E j o
  have := restriction_preservesCountableProducts l E j o
  have := ordinaryAdjunction_unit_isIso l E j o
  have := openAdjunction_unit_isIso l E j o
  have restrictGood := restrictionComplex_good l E j o m.totalComparison
  obtain ⟨ordinary, h⟩ := ordinaryProjection_exists l E j o SX SU AX AU st m c q flat
    extendGood restrictGood
  exact ⟨RoosComparison.ofPreservesProducts _, RoosComparison.ofPreservesProducts _,
    asIso (IntegralOpenReduction.ordinaryAdjunction l E j o).unit, rfl,
    asIso (IntegralOpenReduction.openAdjunction l E j o).unit, rfl, restrictGood, ordinary, h⟩

end WeilConjectures.OpenProjectionRoos
