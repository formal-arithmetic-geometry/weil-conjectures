# PointSectionsDerivedReduction shared definitions

## Reason

The coefficient sequence and generic principal reduction proofs must use the target's
actual coefficient and point-section functors before the final theorem is assembled.
Move the existing shared declarations into a support module publicly imported by the
original item. This is the ordinary definitions/proof separation. The returned cycle
through point-reduction unit normalization is removed from the proof route entirely.

## Old

The following declarations were in `Sheaf.Paper.PointSectionsDerivedReduction`:

```lean
/-- The closure in the finite-field datum is algebraically closed.
Source: the global finite-field datum (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionDatumAlgClosed (D : FiniteFieldDatum.{u}) :
    IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- Standard localization of ordinary coefficient-module complexes in the section universe.
Source: Stacks Tag 05RU (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionModuleDerived (A : Type (u + 1)) [Ring A] :
    HasDerivedCategory (ModuleCat.{u + 1} A) := HasDerivedCategory.standard _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exactness of completed-coefficient evaluation before restricting integral scalars.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionIntegralEvalLimits :
    PreservesFiniteLimits (pointModuleSections D.k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))) :=
  ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).1

/-- Exactness of completed-coefficient evaluation at cokernels.
Source: Stacks Tags 0982 and 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionIntegralEvalColimits :
    PreservesFiniteColimits (pointModuleSections D.k
      (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))) :=
  ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2
    (completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k)))).2.1

/-- Exact integral sections, with action through the canonical constant-to-completed map.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionIntegralLimits :
    PreservesFiniteLimits (pointIntegralSections l E D.k) :=
  inferInstanceAs (PreservesFiniteLimits
    (pointModuleSections D.k _ ⋙
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E D.k)))

/-- Exact integral sections at cokernels, with the same coefficient action.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionIntegralColimits :
    PreservesFiniteColimits (pointIntegralSections l E D.k) :=
  inferInstanceAs (PreservesFiniteColimits
    (pointModuleSections D.k _ ⋙
      ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E D.k)))

/-- Exact evaluation over the finite coefficient sheaf at exponent `n+1`.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionFiniteEvalLimits (n : ℕ) :
    PreservesFiniteLimits (pointModuleSections D.k
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)) :=
  ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2
    (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)).1

/-- Exact finite-coefficient evaluation at cokernels.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionFiniteEvalColimits (n : ℕ) :
    PreservesFiniteColimits (pointModuleSections D.k
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)) :=
  ((@point_proEtale_sections_exact.{u, u + 1, u + 1} D.k).2
    (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)).2.1

/-- Exact finite sections, retaining the action of the actual quotient coefficient ring.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
  inferInstanceAs (PreservesFiniteLimits
    (pointModuleSections D.k
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))))

/-- Exact finite sections at cokernels.
Source: Stacks Tag 0946 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable instance pointReductionFiniteColimits (n : ℕ) :
    PreservesFiniteColimits
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))) :=
  inferInstanceAs (PreservesFiniteColimits
    (pointModuleSections D.k
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n) ⋙
        ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointConstantSectionMap D.k (Padic.coefficientExtensionRing l E (n + 1)))))

/-- The quotient map, transported only through the recorded coefficient-universe lift.
Source: coefficient-extension definition (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable def pointReductionQuotient (n : ℕ) :
    ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) :=
  RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))

/-- Ordinary-module derived tensor with the quotient in degree zero. The chosen universal
left-derived tensor and its K-flat computation determine the functor up to canonical
isomorphism; no underived exactness of quotient tensor is assumed.
Source: Stacks Tag 06Y6 (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable def pointReductionModuleTensor (n : ℕ) :
    DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) ⥤
    DerivedCategory (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) :=
  (Classical.choose (DerivedCategory.exists_derivedTensor_second_factor_functor
    (pointReductionQuotient l E n)).2).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))

/-- The left side of the comparison, on precisely the integral constructible subcategory.
Source: blueprint integral-to-finite comparison
(blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable def pointReductionTensorSections (n : ℕ) :=
  (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
    (pointIntegralSections l E D.k).mapDerivedCategory ⋙ pointReductionModuleTensor l E n

/-- The right side: canonical sheaf derived reduction, followed by exact point sections.
Source: Stacks Tag 06YY (blueprint: lem-pod-point-sections-derived-reduction). -/
noncomputable def pointReductionSectionsTensor (n : ℕ) :=
  (sfIntegralConstructible l E (Spec (.of D.k))).ι ⋙
    scalarReductionDerivedExtension l E (Spec (.of D.k)) n ⋙
      (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
```

## New

The exact same declarations, signatures, bodies and instance attributes are in
`Sheaf.Paper.PointSectionsDerivedReductionData`. The item has
`public import Sheaf.Paper.PointSectionsDerivedReductionData`, retaining the same public
API. Its theorem and all functor definitions retain their statements verbatim. The
unused proof-only imports from the old item are removed from the data module; the
modules implementing the proof import the APIs they actually use.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.PointSectionsDerivedReduction` | A6 | Reexports unchanged definitions, proves the original conjunction. |
| `Sheaf.Paper.PointSectionsDerivedReductionIso` | new | Uses the definitions for the proved comparison. |
| `Sheaf.Paper.PointSectionsDerivedReductionCone` | new | Uses the actual quotient and tensor definitions. |
| `Sheaf.Paper.PointSectionsDerivedReductionHomology` | new | Uses the comparison and exact point sections. |
| `Sheaf.Paper.PointPrincipalReductionCoefficients` | new | Uses the actual integral section action. |
| `Sheaf.Paper.PointReductionCoefficientRing` | new | Uses the actual lifted quotient map. |
| `Sheaf.Paper.PointReductionUnits` | A9 | No edit; its original import of the item still supplies the same declarations. |
| `Sheaf.Paper.PointReductionUnitNormalization` | unclaimed | No edit; its original imports and declarations are preserved. |
| `Sheaf.Paper.PointSectionsFiniteReduction` | unclaimed | Original import receives the unchanged public definitions; no adaptation. |
| `Sheaf.Paper.PointSectionsFiniteness` | unclaimed | Original import receives the unchanged public definitions; no adaptation. |
| `Sheaf.Paper.PointSectionsFinitenessIntegral` | unclaimed | Original import receives the unchanged public definitions; no adaptation. |
| `Sheaf.Paper.PointSectionsIntegralCohomologyControl` | unclaimed | Original import receives the unchanged public definitions; no adaptation. |

Other existing importers receive the unchanged definitions through the item's public
import, so no consumer adaptation is needed. No target meaning changes.

## Status

landed 20261021T011011-L-2027053 2026-10-21 (merge of deliver/A6/Sheaf.Paper.PointSectionsDerivedReduction)
