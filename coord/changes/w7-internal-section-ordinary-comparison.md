# The normalized section comparison maps and their endpoint interfaces

## Reason

Concrete choices expanded large dependent predicates at each coefficient specialization.
Construct the uniquely normalized ordinary and total maps generically, share them between
the global and slice constructions, and transport the actual slice map explicitly across
the proved equality of its endpoint types. Named data and endpoint types keep category
structures shared. This is a definition and interface repair; no file or proof is split
to evade the compile limit, and the limit is unchanged.

Pure tensors determine the ordinary map; mapped coproduct summands determine the total
map. The former choices satisfy these same formulas, so the repaired maps are equal to
them. The equality transport is uniquely fixed by HEq with the entire raw map. These
arguments apply also to zero rings, empty sites and unbounded complexes. No target
statement changes. Definitions used by targets are submitted for independent interpretation
review. No adopted WeilConjectures module is edited.

## Old

`InternalSectionTotalComparison.ordinaryTensorIso`

```lean
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  (internal_section_tensor_comparison (Scheme.ProEt.topology X)
    (condensedRingObj Λ X)).2.choose M N
```

`InternalSectionTotalComparison.complexTensorIso`

```lean
def complexTensorIso (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj
      (CochainComplex.mapBifunctor P Q (curriedTensor (Internal Λ X))) ≅
    CochainComplex.mapBifunctor ((complexForward Λ X).obj P)
      ((complexForward Λ X).obj Q) (sectionTensor Λ X) :=
  (canonicalComplexTensorComparison Λ X P Q).choose
```

`InternalSectionDerivedTensorComparison.totalComparison`

```lean
def totalComparison (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj (internalTotalTensor Λ X P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
      ((complexForward Λ X).obj P, (complexForward Λ X).obj Q) :=
  (totalComparison_existsUnique Λ X P Q).choose
```

`InternalSliceDerivedHomComparison.sliceTotalTensor`

```lean
abbrev sliceTotalTensor (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    CochainComplex (SliceInternal Λ X U) ℤ :=
  (sliceCochainMonoidal Λ X U).tensorObj P Q
```

`InternalSliceDerivedHomComparison.sliceOrdinaryTensorIso`

```lean
def sliceOrdinaryTensorIso (M N : SliceInternal Λ X U) :=
  sectionOrdinaryTensorIso ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U) M N
```

`InternalSliceDerivedHomComparison.sliceRawComplexTensorIso`

```lean
def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :=
  (sliceRawComplexTensorComparison Λ X U P Q).choose
```

`InternalSliceDerivedHomComparison.sliceTotalComparison`

```lean
def sliceTotalComparison (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q) :=
  (sliceTotalComparison_existsUnique Λ X U P Q).choose
```

`InternalSliceDerivedHomComparison.SliceTensorComparison`

```lean
structure SliceTensorComparison
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1}
        ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U)))
    (TU : CoefficientTensorModels.{u, u + 1, u, u + 1}
      ((Scheme.ProEt.topology X).over U) ((ring Λ X).over U) SU) where
  /-- Natural tensor comparison for all local derived objects. -/
  iso : sliceNativeTensor Λ X U ⋙ (sliceForward Λ X U) ≅
    ((sliceForward Λ X U).prod
      (sliceForward Λ X U)) ⋙ SU.tensor
  /-- The localization square with the canonical summand comparison. -/
  normalization : sliceTensorComparisonNormalized Λ X U SU TU iso
```


Additional existing definitions whose bodies or representation change:

`InternalSectionTotalComparison.forward`

```lean
def forward : DerivedCategory (Internal Λ X) ⥤ DerivedCategory (Modules Λ X) :=
  (equivalence Λ X).functor.mapDerivedCategory
```

`InternalSectionTotalComparison.complexForward`

```lean
def complexForward :
    CochainComplex (Internal Λ X) ℤ ⥤ CochainComplex (Modules Λ X) ℤ :=
  (equivalence Λ X).functor.mapHomologicalComplex (.up ℤ)
```

`InternalSectionTotalComparison.localizationIso`

```lean
def localizationIso : DerivedCategory.Q ⋙ forward Λ X ≅
    complexForward Λ X ⋙ DerivedCategory.Q :=
  (equivalence Λ X).functor.mapDerivedCategoryFactors
```

`InternalSectionDerivedTensorComparison.TensorComparison`

```lean
structure TensorComparison
    (S : CoefficientClosedStructure (hom Λ X))
    (T : CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring Λ X) S) where
  /-- Natural comparison on derived tensor products. -/
  iso : Functor.uncurry.obj (CondensedRing.derivedTensor Λ X) ⋙ forward Λ X ≅
    ((forward Λ X).prod (forward Λ X)) ⋙ S.tensor
  /-- Agreement with the canonical ordinary total comparison on K-flat models. -/
  normalization : tensorComparisonNormalized Λ X S T iso
```

`InternalSectionHomComparisonData.homRepresentativeIso`

```lean
def homRepresentativeIso (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    internalHomRepresentative.{u} Λ X P ⋙ complexForward.{u} Λ X ≅
      complexForward.{u} Λ X ⋙
        SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P) :=
  representativeCounit ((equivalence.{u} Λ X).mapHomologicalComplex (.up ℤ))
    (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
      (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P))
```

`InternalSectionScalarHomTransportData.ScalarTransport.restrictionNormalization`

```lean
  restrictionNormalization : derivedRestriction =
    (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap.{u} a X))
      (equivalence.{u} Λ X).functor).symm ≪≫
      Functor.mapDerivedCategoryNatIso restriction ≪≫
      Functor.mapDerivedCategoryCompIso (equivalence.{u} Γ X).functor
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a))
```

## New

`InternalSectionTotalComparison.ordinaryTensorIso`

```lean
def ordinaryTensorIso (M N : Internal Λ X) :
    (equivalence Λ X).functor.obj (M ⊗ N) ≅
      ((sectionTensor Λ X).obj ((equivalence Λ X).functor.obj M)).obj
        ((equivalence Λ X).functor.obj N) :=
  ordinaryTensorIsoForSite (Scheme.ProEt.topology X) (condensedRingObj Λ X) M N
```

`InternalSectionTotalComparison.complexTensorIso`

```lean
def complexTensorIso (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj
      (CochainComplex.mapBifunctor P Q (curriedTensor (Internal Λ X))) ≅
    CochainComplex.mapBifunctor ((complexForward Λ X).obj P)
      ((complexForward Λ X).obj Q) (sectionTensor Λ X) :=
  ordinaryComplexTensorIsoForSite (Scheme.ProEt.topology X) (condensedRingObj Λ X) P Q
```

`InternalSectionDerivedTensorComparison.totalComparison`

```lean
def totalComparison (P Q : CochainComplex (Internal Λ X) ℤ) :
    (complexForward Λ X).obj (internalTotalTensor Λ X P Q) ≅
    (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
      ((complexForward Λ X).obj P, (complexForward Λ X).obj Q) :=
  complexTensorIso Λ X P Q
```

`InternalSliceDerivedHomComparison.sliceTotalTensor`

```lean
def sliceTotalTensor (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    CochainComplex (SliceInternal Λ X U) ℤ :=
  (sliceCochainMonoidal Λ X U).tensorObj P Q
```

`InternalSliceDerivedHomComparison.sliceOrdinaryTensorIso`

```lean
def sliceOrdinaryTensorIso (M N : SliceInternal Λ X U) :=
  ordinaryTensorIsoForSite ((Scheme.ProEt.topology X).over U) (sliceRingObject Λ X U) M N
```

`InternalSliceDerivedHomComparison.sliceRawComplexTensorIso`

```lean
def sliceRawComplexTensorIso (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    SliceRawComplexTensorType Λ X U P Q :=
  ordinaryComplexTensorIsoForSite ((Scheme.ProEt.topology X).over U)
    (sliceRingObject Λ X U) P Q
```

`InternalSliceDerivedHomComparison.sliceTotalComparison`

```lean
def sliceTotalComparison (P Q : CochainComplex (SliceInternal Λ X U) ℤ) :
    (sliceComplexForward Λ X U).obj (sliceTotalTensor Λ X U P Q) ≅
      (coefficientTotalTensor.{u, u + 1, u} ((Scheme.ProEt.topology X).over U)
        ((ring Λ X).over U)).obj
        ((sliceComplexForward Λ X U).obj P, (sliceComplexForward Λ X U).obj Q) :=
  cast (sliceTotalComparison_type_eq Λ X U P Q).symm
    (sliceRawComplexTensorIso Λ X U P Q)
```

`InternalSliceDerivedHomComparison.SliceTensorComparison`

```lean
abbrev SliceTensorComparison
    (SU : SliceClosedStructureType Λ X U)
    (TU : SliceTensorModelsType Λ X U SU) :=
  NormalizedSliceTensorComparisonData (I := SliceTensorComparisonIsoType Λ X U SU)
    (sliceTensorComparisonNormalized Λ X U SU TU)
```


The direct forward-functor interface and global comparison record:

`InternalSectionTotalComparison.forward`

```lean
def forward : DerivedCategory (Internal Λ X) ⥤ DerivedCategory (Modules Λ X) :=
  (sectionForward Λ X).mapDerivedCategory
```

`InternalSectionTotalComparison.complexForward`

```lean
def complexForward :
    CochainComplex (Internal Λ X) ℤ ⥤ CochainComplex (Modules Λ X) ℤ :=
  (sectionForward Λ X).mapHomologicalComplex (.up ℤ)
```

`InternalSectionTotalComparison.localizationIso`

```lean
def localizationIso : DerivedCategory.Q ⋙ forward Λ X ≅
    complexForward Λ X ⋙ DerivedCategory.Q :=
  (sectionForward Λ X).mapDerivedCategoryFactors
```

`InternalSectionDerivedTensorComparison.TensorComparison`

```lean
abbrev TensorComparison
    (S : GlobalClosedStructureType Λ X)
    (T : GlobalTensorModelsType Λ X S) :=
  NormalizedGlobalTensorComparisonData (I := GlobalTensorComparisonIsoType Λ X S)
    (tensorComparisonNormalized Λ X S T)
```

The generic total data are stored in `SectionTensorTotalData`; the mapped coproduct inclusions determine the entire record, as proved by `SectionTensorTotalData.unique`. Public pure-tensor and summand theorems retain the normalized formulas. The native functor-induced coefficient monoid is named in `coefficientMonoid`, with instance transparency; its body is exactly the previously inferred constructor, before registering that name as an instance.

The public `sliceRawComplexForward` and `SliceRawComplexTensorType` name the actual raw functor and total-map endpoints. The proved `sliceTotalComparison_type_eq` has entirely public endpoint types. The definition casts the constructed raw map along this equality; `sliceTotalComparison_heq` proves the entire map is retained. The original unique characterization follows by HEq transitivity and `eq_of_heq`. No data is chosen from a new existence statement.

`GlobalClosedStructureType`, `GlobalTensorModelsType`, `GlobalTensorComparisonIsoType` and their slice counterparts name the unchanged endpoint types. `NormalizedGlobalTensorComparisonData` and `NormalizedSliceTensorComparisonData` each have exactly the fields `iso` and `normalization`; their specializations replace the concrete global and slice records. The old qualified constructor/recursor names are not used by any consumer. Both projections retain their meanings. The two normalization predicates apply `tensorLocalizationSquareHEq` to exactly their original functors and maps; their expanded formulas are definitionally equal.

The duplicated slice helpers `sectionTensorWitness`, `sectionOrdinaryTensorIso` and
private `sectionRawTensorComparison` are removed. Their only uses were the duplicate
slice construction. The shared generic API carries the same formulas and uniqueness.
Their DAG definition node stays attached and is updated to describe this route.

Public proved additive, equivalence and sheaf-composition evidence supplies the generic
interfaces. The direct and symmetric-parent braidings agree by reflexivity. The direct `sectionForward` is definitionally the original recorded equivalence functor,
as certified by `sectionForward_eq`. The three global derived/complex/factor aliases now
use this primitive functor directly; their old bodies remain definitionally equal.
Public `equivalenceAdditive` retains the recorded equivalence's inferred additive API.
`totalComparison_heq` and `sliceEquivalence_functor_heq` expose the two concrete equations
used by localization without unfolding their large implementation terms. Local transparency settings retain
named native category instances; the localization proof keeps respectTransparency enabled.

`InternalSectionHomComparisonData.homRepresentativeIso`

```lean
def homRepresentativeIso (P : CochainComplex (Internal.{u} Λ X) ℤ) :
    internalHomRepresentative.{u} Λ X P ⋙ complexForward.{u} Λ X ≅
      complexForward.{u} Λ X ⋙
        SfbHomFilteredColimit.homFixed.{u + 1, u, u}
          (Scheme.ProEt.topology X) (ring.{u} Λ X) ((complexForward.{u} Λ X).obj P) :=
  by
    simpa only [internalHomRepresentative, complexForward, sectionForward_eq,
      Equivalence.mapHomologicalComplex] using
      representativeCounit ((equivalence.{u} Λ X).mapHomologicalComplex (.up ℤ))
      (SfbHomFilteredColimit.homFixed.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring.{u} Λ X)
        (((equivalence.{u} Λ X).functor.mapHomologicalComplex (.up ℤ)).obj P))
```

The representative counit is unchanged. Its elaboration uses the proved forward-functor
equality explicitly because this consumer locally seals the recorded equivalence.

`InternalSectionScalarHomTransportData.ScalarTransport.restrictionNormalization`

```lean
  restrictionNormalization : derivedRestriction =
    (Functor.mapDerivedCategoryCompIso (Mod.comap (coefficientMap.{u} a X))
      (sectionForward.{u} Λ X)).symm ≪≫
      Functor.mapDerivedCategoryNatIso restriction ≪≫
      Functor.mapDerivedCategoryCompIso (sectionForward.{u} Γ X)
        (SheafOfModules.scalarRestriction.{u + 1, u, u + 1} (sectionCoefficientMap.{u} a))
```

The canonical derived restriction square now names the primitive forward functor
whose derived functor occurs in `derivedRestriction`. The primitive and recorded
forward functors are definitionally equal. Thus this is precisely the original
normalization equation, with no change to its maps or permitted transport data.
Its only downstream module is `InternalSectionHomContinuityComparison`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.InternalSectionTotalComparison | unclaimed | Construct shared generic ordinary and total maps and expose their normalized API. |
| Sheaf.Paper.InternalSectionDerivedTensorComparison | unclaimed | Use the already constructed complex map directly; name normalization types and formula. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Use shared maps and explicit endpoint transport; name raw endpoint types and specialize the generic comparison record. |
| Sheaf.Paper.InternalSectionTensorLocalization | W7 | Prove the assigned theorem from normalized ordinary coherence, coherent derived descent and native ringed models. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Forced proof adaptation of globalHomIso: use forward.asEquivalence, with its proved equivalence instance, so the supplied tensor comparison has the exact functor endpoint. Signatures and slice proof unchanged. |
| Sheaf.Paper.FiniteFreeDualChainComparison | unclaimed | Uses the fixed total map in formulas only; its unique normalization and mathematical value are unchanged. |
| Sheaf.Paper.FiniteFreeOrdinaryChainComparison | unclaimed | Uses the fixed total map in formulas only; its unique normalization and mathematical value are unchanged. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.Paper.NativeOrdinaryEvaluationLocalization | unclaimed | Uses the fixed total map in formulas only; its unique normalization and mathematical value are unchanged. |
| Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletionData | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.SixFunctors.OpenTensorAugmentationLimitSquare | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.SixFunctors.OpenTensorQuotientCochains | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.SixFunctors.OpenTensorQuotientData | unclaimed | Textual last-segment hit only: its totalComparison is a different record field or namespace; unaffected. |
| Sheaf.Paper.FiniteFreeDualChainModels | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.InternalDerivedClosedLocalization | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | Forced counit elaboration adaptation: explicitly use sectionForward_eq under the locally sealed recorded equivalence. Existing signatures and actual counit unchanged. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | unclaimed | Forced proof adaptations use the direct functor for bounds and continuity, and expose the recorded equivalence for scalar identity. Statements and existing holes unchanged. |
| Sheaf.Paper.InternalSectionMonoidalNormalization | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Express canonical derived restriction normalization through the direct sectionForward API, retaining exactly the former formula. |
| Sheaf.Paper.ProfiniteFreeSliceDerivedHom | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.StrictCompletionRestrictionData | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.StrictSectionPrincipalQuotientModels | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.StrictSectionQuotientTensorModels | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Uses retained functor aliases or comparison types/projections; their data and equations retain their meaning. |

The textual downstream queries are retained in the sandbox scratchpad. The helper names
removed from the slice module occur only in that defining module. No consumer uses the
former qualified slice constructor or recursors. The other last-segment `totalComparison`
hits in the table refer to unrelated record fields, as shown by their namespaces and uses.

The full textual audits for the functor aliases and global comparison are in
`scratchpad/final-forward-users.txt` and `scratchpad/final-global-record-users.txt`.
No source uses the old qualified global or slice constructor/recursor/projection names.
The three global aliases are checked by Lean reflexivity against their original bodies;
both normalization predicates are checked by reflexivity against the former expanded
formulas. Consumer compilations and original/adapted diagnostics are recorded in report.md.
The three adapted consumer modules keep every existing declaration header and public
import unchanged. The representative counit remains equal to its old expression by
reflexivity, checked in a separate importing module. The continuity consumer retains
its six pre-existing named holes without adding any.

## Status

landed 20261026T105350-L-1169695 2026-10-26 (merge of deliver/W7/Sheaf.Paper.InternalSectionTensorLocalization)
