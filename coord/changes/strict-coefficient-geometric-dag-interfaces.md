# Lower geometric coefficient interfaces in the DAG

## Reason

The item uses only already-proved proper/open scalar mates and finite presentation helpers, not the later recorded compact-support realization. Their broad DAG owners reach this item through that later realization. A first delivery (4805be2ab4e) omitted dependencies to avoid those cycles; this packet supersedes that incomplete metadata with explicit lower interface nodes. No Lean file outside the item and its two new modules changes.

The new nodes reattach existing declarations. The broad coefficient-data node retains projection comparisons as its primary attachment; the broad integral comparison node retains its main theorem. The native evaluation definition is exactly its previous definition; only its DAG citations are narrowed from the later compact-support/tower interfaces to the finite open/direct-image construction used in its proved body. The functor F_n = Rp_* j_! is unchanged.

## Old

`def-pur-integral-compact-support-coefficient-data`

```json
{
  "lean": {
    "module": "Sheaf.Paper.IntegralCompactSupportCoefficientData",
    "declaration": "WeilConjectures.PurCompactSupport.completed",
    "declarations": [
      "WeilConjectures.PurCompactSupport.Change",
      "WeilConjectures.PurCompactSupport.ProjectionComparisons",
      "WeilConjectures.PurCompactSupport.comparison",
      "WeilConjectures.PurCompactSupport.completed",
      "WeilConjectures.PurCompactSupport.completedChange_square",
      "WeilConjectures.PurCompactSupport.completedPullMap",
      "WeilConjectures.PurCompactSupport.completedPullMap_isIso",
      "WeilConjectures.PurCompactSupport.completedPull_comp",
      "WeilConjectures.PurCompactSupport.finite",
      "WeilConjectures.PurCompactSupport.geometricPullComposition",
      "WeilConjectures.PurCompactSupport.image",
      "WeilConjectures.PurCompactSupport.modulePushComposition_existsUnique",
      "WeilConjectures.PurCompactSupport.openProjectionIso",
      "WeilConjectures.PurCompactSupport.openRestriction",
      "WeilConjectures.PurCompactSupport.openRestrictionMap",
      "WeilConjectures.PurCompactSupport.openRestrictionMap_isIso",
      "WeilConjectures.PurCompactSupport.projection",
      "WeilConjectures.PurCompactSupport.projectionComparisons_existsUnique",
      "WeilConjectures.PurCompactSupport.projectionMap",
      "WeilConjectures.PurCompactSupport.projectionOpenFactor",
      "WeilConjectures.PurCompactSupport.push",
      "WeilConjectures.PurCompactSupport.restriction",
      "WeilConjectures.PurCompactSupport.tensorCurried"
    ],
    "file": "lean/Sheaf/Paper/IntegralCompactSupportCoefficientData.lean",
    "branch": "newtargets-dag",
    "by": "NQ",
    "date": "2026-10-18",
    "existing": false,
    "note": "C6: the six general open-adjunction definitions and the existing projection-invertibility theorem are reattached to def-sp-open-coefficient-adjunction-data and lem-sp-intrinsic-open-projection-invertible. Their Lean code is unchanged. All integral/completed coefficient data stays here.",
    "statement": "def completed : Coefficients.{u}"
  }
}
```

`lem-pur-compact-support-integral-coefficient-comparison`

```json
{
  "lean": {
    "module": "Sheaf.Paper.IntegralCompactSupportCoefficientComparison",
    "declaration": "WeilConjectures.PurCompactSupport.integralCoefficientComparison",
    "declarations": [
      "WeilConjectures.PurCompactSupport.IsScalarShiftNormalized",
      "WeilConjectures.PurCompactSupport.scalarCommShift_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarCommShift",
      "WeilConjectures.PurCompactSupport.imageCommShift",
      "WeilConjectures.PurCompactSupport.comparison_commShift",
      "WeilConjectures.PurCompactSupport.tensorComposition",
      "WeilConjectures.PurCompactSupport.comparison_composition",
      "WeilConjectures.PurCompactSupport.restrictIdentity_existsUnique",
      "WeilConjectures.PurCompactSupport.tensorIdentity",
      "WeilConjectures.PurCompactSupport.comparison_identity",
      "WeilConjectures.PurCompactSupport.tensorModel_exists",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_naturality",
      "WeilConjectures.PurCompactSupport.scalarTensorTotal",
      "WeilConjectures.PurCompactSupport.scalarTensorTotal_isIso",
      "WeilConjectures.PurCompactSupport.scalarTensor_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarTensor",
      "WeilConjectures.PurCompactSupport.geometricPushComposition",
      "WeilConjectures.PurCompactSupport.refinementPull",
      "WeilConjectures.PurCompactSupport.refinementRestriction",
      "WeilConjectures.PurCompactSupport.scalarPull",
      "WeilConjectures.PurCompactSupport.retainedTower",
      "WeilConjectures.PurCompactSupport.IsCofinalRoosMap",
      "WeilConjectures.PurCompactSupport.completedChange",
      "WeilConjectures.PurCompactSupport.properComparison",
      "WeilConjectures.PurCompactSupport.openComparison",
      "WeilConjectures.PurCompactSupport.openComparison_isIso",
      "WeilConjectures.PurCompactSupport.comparison_factorization",
      "WeilConjectures.PurCompactSupport.Ramification",
      "WeilConjectures.PurCompactSupport.ramifiedKernel",
      "WeilConjectures.PurCompactSupport.ramifiedMap",
      "WeilConjectures.PurCompactSupport.ramifiedSheafMap",
      "WeilConjectures.PurCompactSupport.finiteChange_square",
      "WeilConjectures.PurCompactSupport.finiteChange",
      "WeilConjectures.PurCompactSupport.projection_square",
      "WeilConjectures.PurCompactSupport.reduction",
      "WeilConjectures.PurCompactSupport.ramified_reduction_square",
      "WeilConjectures.PurCompactSupport.tensorSquare",
      "WeilConjectures.PurCompactSupport.ReductionComparisonEquation",
      "WeilConjectures.PurCompactSupport.comparison_reduction",
      "WeilConjectures.PurCompactSupport.finiteTensorSource",
      "WeilConjectures.PurCompactSupport.finiteTensorTarget",
      "WeilConjectures.PurCompactSupport.finiteTensorMap",
      "WeilConjectures.PurCompactSupport.finiteSourceProjection",
      "WeilConjectures.PurCompactSupport.finiteTargetProjection",
      "WeilConjectures.PurCompactSupport.strictLevelProjection",
      "WeilConjectures.PurCompactSupport.finiteDirectImage_eq",
      "WeilConjectures.PurCompactSupport.finitePullbackIso",
      "WeilConjectures.PurCompactSupport.finiteOpenIso",
      "WeilConjectures.PurCompactSupport.finiteImageIso",
      "WeilConjectures.PurCompactSupport.finiteReductionIso",
      "WeilConjectures.PurCompactSupport.finiteQuotient",
      "WeilConjectures.PurCompactSupport.finiteQuotient_square",
      "WeilConjectures.PurCompactSupport.finiteQuotientChange",
      "WeilConjectures.PurCompactSupport.ramified_quotient_square",
      "WeilConjectures.PurCompactSupport.ComparisonSquareEquation",
      "WeilConjectures.PurCompactSupport.comparison_quotients",
      "WeilConjectures.PurCompactSupport.finiteComparison_isIso",
      "WeilConjectures.PurCompactSupport.coefficientPrimeUnit",
      "WeilConjectures.PurCompactSupport.integralCoefficientComparison",
      "WeilConjectures.PurCompactSupport.completedMap_identity",
      "WeilConjectures.PurCompactSupport.completedMap_composition",
      "WeilConjectures.PurCompactSupport.ProjectionComparisonEquation",
      "WeilConjectures.PurCompactSupport.comparisonOnFiniteTor_isIso",
      "WeilConjectures.PurCompactSupport.comparisonIso",
      "WeilConjectures.PurCompactSupport.finiteTorIntegralInclusion",
      "WeilConjectures.PurCompactSupport.recordedSupport",
      "WeilConjectures.PurCompactSupport.IsRecordedIdentification",
      "WeilConjectures.PurCompactSupport.recordedIdentification_existsUnique",
      "WeilConjectures.PurCompactSupport.recordedIdentification",
      "WeilConjectures.PurCompactSupport.scalarFiniteTor",
      "WeilConjectures.PurCompactSupport.recordedComparisonIso",
      "WeilConjectures.PurCompactSupport.reductionComparison_isIso",
      "WeilConjectures.PurCompactSupport.refinementProperOpen_existsUnique",
      "WeilConjectures.PurCompactSupport.refinementProperOpen",
      "WeilConjectures.PurCompactSupport.refinementComparison",
      "WeilConjectures.PurCompactSupport.comparison_refinement",
      "WeilConjectures.PurCompactSupport.refinementComparison_coherence",
      "WeilConjectures.PurCompactSupport.identityReductionTower",
      "WeilConjectures.PurCompactSupport.identityReductionMap",
      "WeilConjectures.PurCompactSupport.comparison_strict_towers",
      "WeilConjectures.PurCompactSupport.comparison_projection",
      "WeilConjectures.PurCompactSupport.projectionDomain_complete",
      "WeilConjectures.PurCompactSupport.coefficientSiteSmall",
      "WeilConjectures.PurCompactSupport.coefficientRingSheafify",
      "WeilConjectures.PurCompactSupport.coefficientAbSheafify",
      "WeilConjectures.PurCompactSupport.coefficientAbLocallyBijective"
    ],
    "file": "lean/Sheaf/Paper/IntegralCompactSupportCoefficientComparison.lean",
    "statement": "theorem integralCoefficientComparison (D : FiniteFieldDatum.{u}) (hl : l \u2260 D.p) {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [LocallyOfFiniteType (X \u2198 Spec (.of D.k))] [QuasiCompact (X \u2198 Spec (.of D.k))] [IsSeparated (X \u2198 Spec (.of D.k))] [LocallyOfFiniteType (Y \u2198 Spec (.of D.k))] [QuasiCompact (Y \u2198 Spec (.of D.k))] [IsSeparated (Y \u2198 Spec (.of D.k))] (f : X \u27f6 Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) (M : DerivedCategory (scalarReductionSource l E X)) (hM : finiteTorConstructibleIntegral l E X M) : finiteTorConstructibleIntegral l F X ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) \u2227 sfIntegralConstructible l E Y ((image (completed l E) c).obj M) \u2227 sfIntegralConstructible l F Y ((image (completed l F) c).obj ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) \u2227 IsIso ((comparison (completedChange l E F i) c).app M) \u2227 Nonempty ((image (completed l E) c).obj M \u2245 (sfIntegralCompactSupportValue l E D.k (coefficientPrimeUnit l D hl) c \u27e8M, hM.1\u27e9).obj)",
    "branch": "newtargets-dag",
    "by": "Q14",
    "date": "2026-10-17",
    "existing": false,
    "note": "The primary theorem states invertibility and domain preservation. recordedComparisonIso is the natural isomorphism on the recorded sfCompactSupportFiniteIntegralFunctor, transported by recordedIdentification with the chosen Roos-projection normalization IsRecordedIdentification. comparison_strict_towers includes the actual Ramification datum, canonical source/target projection equations, and identifies each retained evaluation with finiteTensorMap, the ordered proper/open composite, before the full or cofinal Roos map. Other coherence clauses are named in declarations."
  }
}
```

`def-weil-compact-support-native-system-evaluation`

```json
{
  "statement": "Let l be prime, E/Q_l finite, A_n its positive integer-ring quotients, and c=(j,p) a compactification X to Y [def-weil-compactifications-refinements]. On the ringed sequence sites take the native exact extension J along j and separately right-derived direct image P along p [def-sp-varying-ring-operations]. There is a specified natural isomorphism (J followed by P) followed by evaluation at n to evaluation at n followed by intrinsic compact support F_n [def-compact-support-direct-image-detailed]. The direct-image model comparison is fixed by the constant-sheaf adjunction, and the open model comparison by the adjunction unit.",
  "stmt_deps": [
    "def-weil-compact-support-reduction-tower-data",
    "def-sp-varying-ring-operations",
    "def-compact-support-direct-image-detailed",
    "lem-trf-open-square-exchange"
  ],
  "proof": [
    {
      "text": "Identify the ordinary direct-image coefficient map using the sheaf adjunction homEquiv inverse law. Identify the two ordinary open extensions by left-adjoint uniqueness and the constant open pullback model.",
      "uses": [
        "def-weil-compact-support-reduction-tower-data",
        "lem-trf-open-square-exchange"
      ],
      "elementary": false
    },
    {
      "text": "Compose native evalP and evalJ with right-derived and exact-derived model isomorphisms. Insert functor associators to obtain the specified evaluation.",
      "uses": [
        "def-sp-varying-ring-operations"
      ],
      "elementary": false
    }
  ],
  "proof_deps": [
    "def-weil-compact-support-reduction-tower-data",
    "lem-trf-open-square-exchange",
    "def-sp-varying-ring-operations"
  ],
  "proof_origin": {
    "by": "agent",
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/lem-weil-compact-support-representative-independence.proof.md",
    "place": "Original tower proof steps 2 and 3: geometric evaluation before the transition calculation."
  }
}
```

## New

`def-pur-integral-compact-support-coefficient-data`

```json
{
  "lean": {
    "module": "Sheaf.Paper.IntegralCompactSupportCoefficientData",
    "declaration": "WeilConjectures.PurCompactSupport.ProjectionComparisons",
    "declarations": [
      "WeilConjectures.PurCompactSupport.ProjectionComparisons",
      "WeilConjectures.PurCompactSupport.completedChange_square",
      "WeilConjectures.PurCompactSupport.geometricPullComposition",
      "WeilConjectures.PurCompactSupport.modulePushComposition_existsUnique",
      "WeilConjectures.PurCompactSupport.openProjectionIso",
      "WeilConjectures.PurCompactSupport.projectionComparisons_existsUnique",
      "WeilConjectures.PurCompactSupport.projectionMap",
      "WeilConjectures.PurCompactSupport.projectionOpenFactor",
      "WeilConjectures.PurCompactSupport.tensorCurried"
    ],
    "file": "lean/Sheaf/Paper/IntegralCompactSupportCoefficientData.lean",
    "branch": "newtargets-dag",
    "by": "NQ",
    "date": "2026-10-18",
    "existing": false,
    "note": "C6: the six general open-adjunction definitions and the existing projection-invertibility theorem are reattached to def-sp-open-coefficient-adjunction-data and lem-sp-intrinsic-open-projection-invertible. Their Lean code is unchanged. All integral/completed coefficient data stays here.",
    "statement": "structure ProjectionComparisons (R : Coefficients.{u})\n    {X Y : Scheme.{u}} {f : X \u27f6 Y} (c : Compactification f)\n    (a : ProEtaleTensorModel X (R.ring X)) (b : ProEtaleTensorModel c.Z (R.ring c.Z))\n    (d : ProEtaleTensorModel Y (R.ring Y))\n    (hc : R.pull (c.i \u226b c.g) = proEtaleRingCompositeCoefficients c.i c.g\n      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))"
  }
}
```

`lem-pur-compact-support-integral-coefficient-comparison`

```json
{
  "lean": {
    "module": "Sheaf.Paper.IntegralCompactSupportCoefficientComparison",
    "declaration": "WeilConjectures.PurCompactSupport.integralCoefficientComparison",
    "declarations": [
      "WeilConjectures.PurCompactSupport.IsScalarShiftNormalized",
      "WeilConjectures.PurCompactSupport.scalarCommShift_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarCommShift",
      "WeilConjectures.PurCompactSupport.imageCommShift",
      "WeilConjectures.PurCompactSupport.comparison_commShift",
      "WeilConjectures.PurCompactSupport.tensorComposition",
      "WeilConjectures.PurCompactSupport.comparison_composition",
      "WeilConjectures.PurCompactSupport.restrictIdentity_existsUnique",
      "WeilConjectures.PurCompactSupport.tensorIdentity",
      "WeilConjectures.PurCompactSupport.comparison_identity",
      "WeilConjectures.PurCompactSupport.tensorModel_exists",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor",
      "WeilConjectures.PurCompactSupport.scalarOrdinaryTensor_naturality",
      "WeilConjectures.PurCompactSupport.scalarTensorTotal",
      "WeilConjectures.PurCompactSupport.scalarTensorTotal_isIso",
      "WeilConjectures.PurCompactSupport.scalarTensor_existsUnique",
      "WeilConjectures.PurCompactSupport.scalarTensor",
      "WeilConjectures.PurCompactSupport.geometricPushComposition",
      "WeilConjectures.PurCompactSupport.refinementPull",
      "WeilConjectures.PurCompactSupport.refinementRestriction",
      "WeilConjectures.PurCompactSupport.scalarPull",
      "WeilConjectures.PurCompactSupport.retainedTower",
      "WeilConjectures.PurCompactSupport.IsCofinalRoosMap",
      "WeilConjectures.PurCompactSupport.completedChange",
      "WeilConjectures.PurCompactSupport.Ramification",
      "WeilConjectures.PurCompactSupport.ramifiedKernel",
      "WeilConjectures.PurCompactSupport.ramifiedMap",
      "WeilConjectures.PurCompactSupport.ramifiedSheafMap",
      "WeilConjectures.PurCompactSupport.finiteChange_square",
      "WeilConjectures.PurCompactSupport.finiteChange",
      "WeilConjectures.PurCompactSupport.projection_square",
      "WeilConjectures.PurCompactSupport.ramified_reduction_square",
      "WeilConjectures.PurCompactSupport.tensorSquare",
      "WeilConjectures.PurCompactSupport.ReductionComparisonEquation",
      "WeilConjectures.PurCompactSupport.comparison_reduction",
      "WeilConjectures.PurCompactSupport.finiteTensorSource",
      "WeilConjectures.PurCompactSupport.finiteTensorTarget",
      "WeilConjectures.PurCompactSupport.finiteTensorMap",
      "WeilConjectures.PurCompactSupport.finiteSourceProjection",
      "WeilConjectures.PurCompactSupport.finiteTargetProjection",
      "WeilConjectures.PurCompactSupport.strictLevelProjection",
      "WeilConjectures.PurCompactSupport.finitePullbackIso",
      "WeilConjectures.PurCompactSupport.finiteQuotient",
      "WeilConjectures.PurCompactSupport.finiteQuotient_square",
      "WeilConjectures.PurCompactSupport.finiteQuotientChange",
      "WeilConjectures.PurCompactSupport.ramified_quotient_square",
      "WeilConjectures.PurCompactSupport.ComparisonSquareEquation",
      "WeilConjectures.PurCompactSupport.comparison_quotients",
      "WeilConjectures.PurCompactSupport.finiteComparison_isIso",
      "WeilConjectures.PurCompactSupport.coefficientPrimeUnit",
      "WeilConjectures.PurCompactSupport.integralCoefficientComparison",
      "WeilConjectures.PurCompactSupport.completedMap_identity",
      "WeilConjectures.PurCompactSupport.completedMap_composition",
      "WeilConjectures.PurCompactSupport.ProjectionComparisonEquation",
      "WeilConjectures.PurCompactSupport.comparisonOnFiniteTor_isIso",
      "WeilConjectures.PurCompactSupport.comparisonIso",
      "WeilConjectures.PurCompactSupport.finiteTorIntegralInclusion",
      "WeilConjectures.PurCompactSupport.recordedSupport",
      "WeilConjectures.PurCompactSupport.IsRecordedIdentification",
      "WeilConjectures.PurCompactSupport.recordedIdentification_existsUnique",
      "WeilConjectures.PurCompactSupport.recordedIdentification",
      "WeilConjectures.PurCompactSupport.scalarFiniteTor",
      "WeilConjectures.PurCompactSupport.recordedComparisonIso",
      "WeilConjectures.PurCompactSupport.reductionComparison_isIso",
      "WeilConjectures.PurCompactSupport.refinementProperOpen_existsUnique",
      "WeilConjectures.PurCompactSupport.refinementProperOpen",
      "WeilConjectures.PurCompactSupport.refinementComparison",
      "WeilConjectures.PurCompactSupport.comparison_refinement",
      "WeilConjectures.PurCompactSupport.refinementComparison_coherence",
      "WeilConjectures.PurCompactSupport.identityReductionTower",
      "WeilConjectures.PurCompactSupport.identityReductionMap",
      "WeilConjectures.PurCompactSupport.comparison_strict_towers",
      "WeilConjectures.PurCompactSupport.comparison_projection",
      "WeilConjectures.PurCompactSupport.projectionDomain_complete",
      "WeilConjectures.PurCompactSupport.coefficientSiteSmall",
      "WeilConjectures.PurCompactSupport.coefficientRingSheafify",
      "WeilConjectures.PurCompactSupport.coefficientAbSheafify",
      "WeilConjectures.PurCompactSupport.coefficientAbLocallyBijective"
    ],
    "file": "lean/Sheaf/Paper/IntegralCompactSupportCoefficientComparison.lean",
    "statement": "theorem integralCoefficientComparison (D : FiniteFieldDatum.{u}) (hl : l \u2260 D.p) {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [LocallyOfFiniteType (X \u2198 Spec (.of D.k))] [QuasiCompact (X \u2198 Spec (.of D.k))] [IsSeparated (X \u2198 Spec (.of D.k))] [LocallyOfFiniteType (Y \u2198 Spec (.of D.k))] [QuasiCompact (Y \u2198 Spec (.of D.k))] [IsSeparated (Y \u2198 Spec (.of D.k))] (f : X \u27f6 Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f) (M : DerivedCategory (scalarReductionSource l E X)) (hM : finiteTorConstructibleIntegral l E X M) : finiteTorConstructibleIntegral l F X ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) \u2227 sfIntegralConstructible l E Y ((image (completed l E) c).obj M) \u2227 sfIntegralConstructible l F Y ((image (completed l F) c).obj ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)) \u2227 IsIso ((comparison (completedChange l E F i) c).app M) \u2227 Nonempty ((image (completed l E) c).obj M \u2245 (sfIntegralCompactSupportValue l E D.k (coefficientPrimeUnit l D hl) c \u27e8M, hM.1\u27e9).obj)",
    "branch": "newtargets-dag",
    "by": "Q14",
    "date": "2026-10-17",
    "existing": false,
    "note": "The primary theorem states invertibility and domain preservation. recordedComparisonIso is the natural isomorphism on the recorded sfCompactSupportFiniteIntegralFunctor, transported by recordedIdentification with the chosen Roos-projection normalization IsRecordedIdentification. comparison_strict_towers includes the actual Ramification datum, canonical source/target projection equations, and identifies each retained evaluation with finiteTensorMap, the ordered proper/open composite, before the full or cofinal Roos map. Other coherence clauses are named in declarations."
  }
}
```

`def-weil-compact-support-native-system-evaluation`

```json
{
  "statement": "Let l be prime, E/Q_l finite, A_n its positive integer-ring quotients [def-weil-l-adic-coefficient-extension], and c=(j,p) a compactification X to Y [def-weil-compactifications-refinements]. On the ringed sequence sites [def-coef-ringed-sequence-site] take the native exact extension J along j and separately right-derived direct image P along p [def-sp-varying-ring-operations]. There is a specified natural isomorphism (J followed by P) followed by evaluation at n to evaluation at n followed by the intrinsic finite functor F_n = Rp_* j_!, formed from exact extension by zero [def-weil-extension-by-zero] and ordinary derived direct image [def-weil-pbc-proetale-operations]. The direct-image model comparison is fixed by the constant-sheaf adjunction, and the open model comparison by the adjunction unit. The open presentation comparison is the unit-normalized one of [lem-trf-open-square-exchange].",
  "stmt_deps": [
    "def-weil-l-adic-coefficient-extension",
    "def-coef-ringed-sequence-site",
    "def-sp-varying-ring-operations",
    "def-weil-extension-by-zero",
    "def-weil-pbc-proetale-operations",
    "lem-trf-open-square-exchange",
    "def-weil-compactifications-refinements"
  ],
  "proof": [
    {
      "text": "Identify the ordinary direct-image coefficient map using the sheaf adjunction homEquiv inverse law. Identify the two ordinary open extensions by left-adjoint uniqueness and the constant open pullback model.",
      "uses": [
        "lem-trf-open-square-exchange"
      ],
      "elementary": false
    },
    {
      "text": "Compose native evalP and evalJ with right-derived and exact-derived model isomorphisms. Insert functor associators to obtain the specified evaluation.",
      "uses": [
        "def-sp-varying-ring-operations"
      ],
      "elementary": false
    }
  ],
  "proof_deps": [
    "def-sp-varying-ring-operations",
    "lem-trf-open-square-exchange"
  ],
  "proof_origin": {
    "by": "worker",
    "group": "P9",
    "document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-pf-field/lem-weil-compact-support-representative-independence.proof.md",
    "place": "Existing proved native evaluation; dependency refinement to finite ringed operations, with no realization theorem used."
  }
}
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unchanged | DAG attachments only; all Lean declarations identical |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unchanged | DAG attachments only; all Lean declarations identical |
| Sheaf.Paper.CompactSupportNativeSystemEvaluation | unchanged | DAG dependencies and equivalent inline description only; Lean identical |
| Sheaf.Paper.QcqsCompactSupportStrictReductionData | P9 | proof uses the refined lower interfaces |
| All Lean consumers of these interfaces | unchanged | no source, type, attribute, import or reduction behavior changes |

## Status

landed 20261027T034724-L-3679198 2026-10-27 (merge of deliver/P9/Sheaf.Paper.QcqsCompactSupportStrictReductionData)
