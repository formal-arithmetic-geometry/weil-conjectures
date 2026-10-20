# Point-section scalar functors

## Reason

Move the eight unchanged canonical scalar constructions from PointSectionsFiniteness into the existing, unclaimed CompletedIntegralCoefficientGerm module, which already constructs the integral constant-to-completion map. The item retains all eleven original public imports, including this prerequisite, and therefore reexports the same declarations. The reduction comparison already imports this prerequisite, so removing its parent import breaks the proof cycle without replacing that import. No mathematical data, signature or target meaning changes.

## Old

```lean
/-- The constant-section coefficient map at the final object, given by sheafification's
unit, without choosing an identification of the section ring.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointConstantSectionMap (k A : Type u) [Field k] [CommRing A] :
    ULift.{u + 1, u} A →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).obj.obj
            (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((CategoryTheory.toSheafify (ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 (Spec (.of k))))))).hom

/-- Final-object evaluation with scalars restricted along the actual constant-section map.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointFiniteSections (k A : Type u) [Field k] [CommRing A] :=
  pointModuleSections k
      ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)

/-- Evaluation and restriction of scalars are additive, allowing termwise sections.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointFiniteSectionsAdditive (k A : Type u) [Field k] [CommRing A] :
    (pointFiniteSections k A).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)).Additive)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]

/-- Integral scalars act through the limit lift of their compatible constant reductions.
This is the canonical map O_E → Γ(s, completed O_E), with only the common universe lifted.
Source: blueprint order 1509 and completed coefficients, order 1455
(blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralSectionMap :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E))

/-- Completed-coefficient sections, retaining the canonical integral coefficient action.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralSections :=
  pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)

/-- Additivity of completed-coefficient sections and scalar restriction.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointIntegralSectionsAdditive :
    (pointIntegralSections l E k).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)).Additive)

/-- The original inclusion O_E ↪ E, transported through the common ULift.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable def pointIntegralToField :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+* ULift.{u + 1, u} E :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom)

/-- Tensoring with E is additive by the extension-restriction adjunction.
Source: blueprint order 1509 (blueprint: lem-weil-point-sections-finiteness). -/
noncomputable instance pointIntegralToFieldAdditive :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).left_adjoint_additive
```

## New

In `Sheaf.Paper.CompletedIntegralCoefficientGerm` (publicly reexported by the item):

```lean
/-- The constant-section coefficient map at the final object, given by sheafification's
unit, without choosing an identification of the section ring.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: def-weil-point-section-scalar-functors). -/
noncomputable def pointConstantSectionMap (k A : Type u) [Field k] [CommRing A] :
    ULift.{u + 1, u} A →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).obj.obj
            (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  ((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
    ((CategoryTheory.toSheafify (ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 (Spec (.of k))))))).hom

/-- Final-object evaluation with scalars restricted along the actual constant-section map.
Source: blueprint order 1509; Stacks Tag 03CW
(blueprint: def-weil-point-section-scalar-functors). -/
noncomputable def pointFiniteSections (k A : Type u) [Field k] [CommRing A] :=
  pointModuleSections k
      ((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)

/-- Evaluation and restriction of scalars are additive, allowing termwise sections.
Source: blueprint order 1509 (blueprint: def-weil-point-section-scalar-functors). -/
noncomputable instance pointFiniteSectionsAdditive (k A : Type u) [Field k] [CommRing A] :
    (pointFiniteSections k A).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (R := ULift.{u + 1, u} A) (pointConstantSectionMap k A)).Additive)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]

/-- Integral scalars act through the limit lift of their compatible constant reductions.
This is the canonical map O_E → Γ(s, completed O_E), with only the common universe lifted.
Source: blueprint order 1509 and completed coefficients, order 1455
(blueprint: def-weil-point-section-scalar-functors). -/
noncomputable def pointIntegralSectionMap :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      (((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).obj.obj
          (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E))

/-- Completed-coefficient sections, retaining the canonical integral coefficient action.
Source: blueprint order 1509 (blueprint: def-weil-point-section-scalar-functors). -/
noncomputable def pointIntegralSections :=
  pointModuleSections k (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k))) ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)

/-- Additivity of completed-coefficient sections and scalar restriction.
Source: blueprint order 1509 (blueprint: def-weil-point-section-scalar-functors). -/
noncomputable instance pointIntegralSectionsAdditive :
    (pointIntegralSections l E k).Additive :=
  inferInstanceAs ((pointModuleSections k _ ⋙
    ModuleCat.restrictScalars (pointIntegralSectionMap l E k)).Additive)

/-- The original inclusion O_E ↪ E, transported through the common ULift.
Source: blueprint order 1509 (blueprint: def-weil-point-section-scalar-functors). -/
noncomputable def pointIntegralToField :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+* ULift.{u + 1, u} E :=
  ULift.ringEquiv.symm.toRingHom.comp
    ((Padic.coefficientExtensionIntegers l E).subtype.comp ULift.ringEquiv.toRingHom)

/-- Tensoring with E is additive by the extension-restriction adjunction.
Source: blueprint order 1509 (blueprint: def-weil-point-section-scalar-functors). -/
noncomputable instance pointIntegralToFieldAdditive :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} (pointIntegralToField l E)).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
    (pointIntegralToField l E)).left_adjoint_additive
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointSectionsFiniteReduction | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointReductionUnits | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointSectionsFiniteness | P3 | Move eight constructions unchanged to CompletedIntegralCoefficientGerm; preserve every original public import; prove the theorem. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Quarantined consumer preserved at `quarantine/Sheaf/Paper/PointSectionsReconstruction.lean`; uses `WeilConjectures.pointFiniteSections`, `WeilConjectures.pointIntegralSections` and `WeilConjectures.pointIntegralSectionsAdditive`. Its existing import of PointSectionsFiniteness still reexports their identical signatures and bodies through CompletedIntegralCoefficientGerm; no source adaptation or withdrawal. |
| Sheaf.Paper.PointSectionsDerivedReduction | A6 | Remove only the public import of PointSectionsFiniteness to break the source cycle; existing CompletedIntegralCoefficientGerm import supplies the relocated constructions; declarations unchanged. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed | Identical public names, signatures and bodies through the existing public import; no source adaptation. |
| Sheaf.Paper.CompletedIntegralCoefficientGerm | unclaimed | Add the eight relocated declarations and their three necessary public imports; existing declarations, including quotient compatibility, unchanged. Unclaimed prerequisite. |
| Sheaf.Paper.PointSectionsFinitenessFiniteTorsion | P3 | New proved finite-torsion clause uses the same canonical scalar constructions. |
| Sheaf.Paper.PointSectionsFinitenessIntegral | P3 | New proved integral/rational clauses use the same canonical scalar constructions. |
| Sheaf.Paper.PointSectionsIntegralCohomologyControl | P3 | New proved cohomology control uses the same canonical scalar constructions. |

The existing reduction module is currently held by A6, as the server preflight reports (the local claim snapshot is stale). Its sole change is removing `public import Sheaf.Paper.PointSectionsFiniteness`. Its existing `public import Sheaf.Paper.CompletedIntegralCoefficientGerm` now supplies every scalar declaration needed by its unchanged signatures and bodies. Keeping the parent import closes the source cycle PointSectionsFiniteness → PointSectionsFinitenessIntegral → PointSectionsIntegralCohomologyControl → PointSectionsDerivedReduction → PointSectionsFiniteness. This pure import removal is checked independently by the reader. The unclaimed coefficient-germ prerequisite gains the constructions, without changing any existing declaration. The item preserves its original public imports and all original declaration signatures and bodies except the newly completed theorem proof. Target statements and all definitions they use retain their meanings.

## Status

landed 20261020T230819-L-616466 2026-10-20 (merge of deliver/P3/Sheaf.Paper.PointSectionsFiniteness)
