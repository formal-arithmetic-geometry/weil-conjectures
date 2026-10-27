# WeilConjectures.IntegralFiniteExtension comparison models

## Reason

The proof of u_existsUnique needs a finite-transition coherence theorem stated in its own
module. That theorem uses quotient, finiteU and DualizingDatum but must not import
u_existsUnique, which would create a cycle. Move the unchanged prerequisite declarations
into CoefIntegralFiniteExtensionModels and publicly re-export them from the original module.
The two already proved completeness results and dualizingDatum_nonempty move with their
private proof helpers. No construction, theorem signature, visibility, or non-proof body changes.
The original four public imports remain transitively public through the models module.
No adopted WeilConjectures source module is edited.

## Old

The following declarations were in Sheaf.SixFunctors.CoefIntegralFiniteExtension:

```lean
def tensorModel {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (a : IntegralHom.TensorPresentation.{u, u} X R) : ProEtaleTensorModel X R

def homMap {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S) (a : IntegralHom.TensorPresentation.{u, u} X R) (b : IntegralHom.TensorPresentation.{u, u} X S) (K M : IntegralHom.Derived.{u, u} X R) : (pbcDerivedExtend φ).obj ((IntegralHom.hom.{u, u} X R).obj (op K, M)) ⟶ (IntegralHom.hom.{u, u} X S).obj (op ((pbcDerivedExtend φ).obj K), (pbcDerivedExtend φ).obj M)

theorem completion_isIso (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) : IsIso ((completedScalarComparison l E L ι X).app K)

def completion (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) : (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K ≅ (integralScalarExtensionOfUniverses l E L ι X).obj K

def quotient (n : ℕ) (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) : (scalarReductionDerivedExtension l L X n).obj ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅ (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj ((scalarReductionDerivedExtension l E X n).obj K)

def v (a : IntegralHom.TensorPresentation.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)) (b : IntegralHom.TensorPresentation.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)) (K M : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) : (integralScalarExtensionOfUniverses l E L ι X).obj ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ⟶ (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).obj (op ((integralScalarExtensionOfUniverses l E L ι X).obj K), (integralScalarExtensionOfUniverses l E L ι X).obj M)

def finiteRealizationRestriction (n : ℕ) : finiteDualizingRealization l L X n ⋙ pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n) ≅ Sheaf.derivedRestrictScalars X.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) ⋙ finiteDualizingRealization l E X n

def finiteEtaleU (n : ℕ) : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) X).obj (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l L D X n

def finiteU (n : ℕ) : (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l L D X n

structure DualizingDatum (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]

theorem dualizingDatum_nonempty (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F] : Nonempty (DualizingDatum l X D hl F)

theorem extension_complete (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) : IsSfDerivedComplete l L X ((integralScalarExtensionOfUniverses l E L ι X).obj K)
```

The exact original definition and structure blocks (including the coherence fields) are:

```lean
/-- The existing tensor presentation restricted to flat-term K-flat representatives.
Source: blueprint order 2494, tensor calculation
(blueprint: lem-coef-integral-finite-extension). -/
def tensorModel {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : IntegralHom.TensorPresentation.{u, u} X R) : ProEtaleTensorModel X R where
  tensor := a.tensor
  representative := Functor.isoWhiskerLeft
    (((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
      (fun P ↦ P.property.1)).prod
      ((IntegralHom.flat.{u, u} X R).lift (proEtaleFlatRepresentatives X R).ι
        (fun P ↦ P.property.1))) a.representative

/-- The actual evaluation transpose for an arbitrary change of coefficient sheaves.
Source: blueprint order 2494, internal-Hom comparison
(blueprint: lem-coef-integral-finite-extension). -/
def homMap {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (a : IntegralHom.TensorPresentation.{u, u} X R)
    (b : IntegralHom.TensorPresentation.{u, u} X S)
    (K M : IntegralHom.Derived.{u, u} X R) :
    (pbcDerivedExtend φ).obj ((IntegralHom.hom.{u, u} X R).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X S).obj
        (op ((pbcDerivedExtend φ).obj K), (pbcDerivedExtend φ).obj M) :=
  (b.adjunction ((pbcDerivedExtend φ).obj K)).homEquiv _ _
    ((PurCompactSupport.scalarTensor φ (tensorModel X a) (tensorModel X b)).inv.app
        (K, (IntegralHom.hom.{u, u} X R).obj (op K, M)) ≫
      (pbcDerivedExtend φ).map ((a.adjunction K).counit.app M))

/-- Completeness in the intrinsic category makes the specified completion map invertible.
Source: blueprint order 2494, first paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: compare the intrinsic Roos completeness unit with the unrestricted one on a
flat-term K-flat resolution. Both have quotient components x ↦ 1 tensor x and zero
shifted coordinate. The finite-free completed-scalar comparison applies to this
same unit; hence its localized map is invertible. -/
theorem completion_isIso (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    IsIso ((completedScalarComparison l E L ι X).app K) := by
  exact ((finiteFreeCompletedScalarComparison l E L ι X).2.1 K
    ((complete_iff_unrestricted l E X K).mp hK)).1

/-- The fixed completion comparison on a complete input.
Source: blueprint order 2494 (blueprint: lem-coef-integral-finite-extension). -/
def completion (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (pbcDerivedExtend (completedCoefficientMap l E L ι X)).obj K ≅
      (integralScalarExtensionOfUniverses l E L ι X).obj K :=
  letI := completion_isIso l E L ι X K hK
  asIso ((completedScalarComparison l E L ι X).app K)

/-- The canonical tensor/restriction identification of a finite reduction of T.
Source: blueprint order 2494, displayed quotient identification
(blueprint: lem-coef-integral-finite-extension). -/
def quotient (n : ℕ) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l L X n).obj
        ((integralScalarExtensionOfUniverses l E L ι X).obj K) ≅
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        ((scalarReductionDerivedExtension l E X n).obj K) :=
  (scalarReductionDerivedExtension l L X n).mapIso (completion l E L ι X K hK).symm ≪≫
    (PurCompactSupport.finiteReductionIso l L X n).symm.app _ ≪≫
    (PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
      (integralScalarQuotientSheafMap l E L ι X n)
      (completedIntegralCommRingProjectionUnrestricted l E X n)
      (completedIntegralCommRingProjectionUnrestricted l L X n)
      ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n)).app K ≪≫
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).mapIso
      ((PurCompactSupport.finiteReductionIso l E X n).app K)

/-- The canonical v: scalar-extended evaluation, transported through completion.
Source: blueprint order 2494, fourth paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def v (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    (integralScalarExtensionOfUniverses l E L ι X).obj
        ((IntegralHom.hom.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ⟶
      (IntegralHom.hom.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l L X)).obj
        (op ((integralScalarExtensionOfUniverses l E L ι X).obj K),
          (integralScalarExtensionOfUniverses l E L ι X).obj M) :=
  (completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)).inv ≫
    homMap X (completedCoefficientMap l E L ι X) a b K M ≫
    (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
      (Prod.mkHom (completion l E L ι X K hK).inv.op
        (completion l E L ι X M hM).hom)

/-- Cross-field restriction commutes with the prescribed comparison-site realization.
Source: blueprint order 2494, finite counit comparisons
(blueprint: lem-coef-integral-finite-extension). -/
def finiteRealizationRestriction (n : ℕ) :
    finiteDualizingRealization l L X n ⋙
        pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n) ≅
      Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) ⋙
        finiteDualizingRealization l E X n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteDualizingGenericDerivedRestriction X
      (integralScalarQuotientMap l E L ι n)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcDerivedComparisonRestrict X
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))) _ ≪≫
    Functor.associator _ _ _

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- The finite cross-field dualizing map is the exceptional-adjunction transpose of
inverse compact-support comparison followed by extension of the counit and the unit.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteEtaleU (n : ℕ) :
    (Etale.scalarExtension
      (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)) X).obj
        (finiteDualizingEtaleTerm l E D X n) ⟶ finiteDualizingEtaleTerm l L D X n :=
  (finiteDualizingEtaleAdjunction l L D X n).homEquiv _ _
    (Etale.ExceptionalCoefficients.comparisonInverse
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (finiteDualizingCompactification D X) (finiteDualizingEtaleTerm l E D X n) ≫
      (Etale.scalarExtension
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).map (finiteDualizingEtaleCounit l E D X n) ≫
      (Etale.ExceptionalCoefficients.unitIso
        (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n))
        (Spec (.of D.k))).hom)

/-- Intrinsic finite u, transported by the scalar-unit-normalized realization square.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
def finiteU (n : ℕ) :
    (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).obj
        (integralDualizingFiniteTerm l E D X n) ⟶ integralDualizingFiniteTerm l L D X n :=
  ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E L ι X n)).homEquiv
    _ _).symm
      ((finiteDualizingOrigin l E D X n).inv ≫
        (finiteDualizingRealization l E X n).map
          ((Adjunction.ofIsRightAdjoint
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (RingHom.ulift.{u + 1, u + 1} (integralScalarQuotientMap l E L ι n)))).homEquiv
                _ _ (finiteEtaleU l E L ι X D n)) ≫
        (finiteRealizationRestriction l E L ι X n).inv.app
          (finiteDualizingEtaleTerm l L D X n) ≫
        (pbcDerivedRestrict (integralScalarQuotientSheafMap l E L ι X n)).map
          (finiteDualizingOrigin l L D X n).hom)

/-- A presentation of the integral dualizing object with its coherent finite counits.
Coherence is essential: unrelated finite isomorphisms are not dualizing reduction data.
These are the reduction data provided by prop-coef-integral-dualizing.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension). -/
structure DualizingDatum (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] where
  omega : sfIntegralConstructibleCategory l F X
  reduction : ∀ n : ℕ,
    (scalarReductionDerivedExtension l F X n).obj omega.obj ≅
      integralDualizingFiniteTerm l F D X n
  coherent : ∀ {m n : ℕ} (h : n ≤ m),
    normalizedDVRReductionTransition l F X D hl h omega.obj ≫
        (normalizedDVRRes l F X h).map (reduction n).hom =
      (reduction m).hom ≫ integralDualizingExceptionalTransition l F D X hl h

/-- The coherent presentations required here exist, with the actual finite counits.
Source: blueprint order 2494, second paragraph
(blueprint: lem-coef-integral-finite-extension).
Proof: choose a dimension bound for the finite-type scheme, then apply the integral
 dualizing proposition. Compose its normalized DVR counit comparisons with its
coherent finite-term origins. Their transition equation is precisely coherent. -/
theorem dualizingDatum_nonempty (F : Type u) [Field F] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) F] : Nonempty (DualizingDatum l X D hl F) := by
  classical
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le (X ↘ Spec (.of D.k))
  obtain ⟨ω, T, _, ⟨e, he⟩, _, hp, _⟩ := prop_coef_integral_dualizing D l hl F X d hd
  let : HasCountableProducts (completedIntegralDerivedCategory l F X D hl) :=
    integralOperationsDerivedCountableProducts l F X
  obtain ⟨p, δ, _, hi, hc⟩ := hp
  let r (n : ℕ) : (scalarReductionDerivedExtension l F X n).obj ω.obj ≅
      integralDualizingFiniteTerm l F D X n :=
    @asIso _ _ _ _ (normalizedDVRCounitComparison l F X D hl T ω.obj p n) (hi n) ≪≫ e n
  refine ⟨⟨ω, r, ?_⟩⟩
  intro m n h
  change normalizedDVRReductionTransition l F X D hl h ω.obj ≫
      (normalizedDVRRes l F X h).map
        (normalizedDVRCounitComparison l F X D hl T ω.obj p n ≫ (e n).hom) =
    (normalizedDVRCounitComparison l F X D hl T ω.obj p m ≫ (e m).hom) ≫
      integralDualizingExceptionalTransition l F D X hl h
  rw [Functor.map_comp, ← Category.assoc, ← hc m n h, Category.assoc, he h]
  simp only [integralDualizingFiniteComparison, Equiv.apply_symm_apply, Category.assoc]


```

These bodies are unchanged in the new module.

## New

Exactly the signatures and bodies listed above now occur in
Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels. The original module contains:

```lean
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels
```

It additionally imports the two proof lemmas and constructible scalar preservation privately.
All original public names are accessible under their unchanged qualified names. In particular,
DualizingDatum still bundles the same actual object, finite reductions and transition equation;
u is still chosen from the original unique-morphism theorem, whose proof now reconstructs
its finite maps and cancels reduction isomorphisms. Target meanings do not change and no target
statement or definition body is modified.

## Users

Every transitive importer is listed below to include textual over-approximations from
`tools/downstream.py --uses`. No consumer source adaptation is required. Direct importers
will be compiled individually against the delivered module; all have the same public names.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceProductDomain | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.AffineSpaceTraceFactorization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.ChartDiagonalSourceMate | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.ExceptionalRefinementMates | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | T3 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.FiniteTorStability | J2 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.GeneralHomComparisonCocycles | C6 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.GeometricComparisonData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.GeometricOperations | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.IntegralDualizingExceptionalUnit | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | D7 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | W2 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.NormalizedSupportEtalePresentation | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarComparisonIdentification | E1 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RelativeKunneth | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.RelativeProductInputDomains | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SfPackageCoefficientDomains | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.TraceCorrespondences | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | D2 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientSystemSymmetricCalculus | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitFiniteTor | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CoefficientUnitNormalization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.CompletedSystemPullbackPreservation | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionCoefficientUnitData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionGeometricRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemDuality | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemEnriched | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | Q9 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemDualityCompatibility | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RamifiedScalarExceptionalLimit | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalDualizingIdentification | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalExceptionalIdentifications | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalHomIdentifications | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalOperationsData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | B6 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.WeilSheaf.DualRealizationComparison | F2 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeBidualEvaluationRealization | X5 | Same public names, signatures and bodies via public re-export; no adaptation. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed | Same public names, signatures and bodies via public re-export; no adaptation. |

## Status

landed 20261025T164906-L-1121390 2026-10-25 (merge of deliver/Y7/Sheaf.SixFunctors.CoefIntegralFiniteExtension)
