# AlgebraicGeometry.ProEtale.CondensedRing.modelCompactComparisonWithoutIdentity

## Reason

Restore the assigned quarantined module from coord/rework.tsv and repair the obsolete
upstream endomorphism-Weil interface. Current upstream removed
compactCohomologyFrobeniusComparison and renamed WeilBoundedConstructibleOfEnd to
WeilBoundedConstructible. The actual comparison used by weilCompactCohomology is now
the trivial-square specialization of weilLowerShriekFrobeniusComparison. Its published
identity-removal theorem proves that it is the same compactPullback, so this repair
preserves the specified construction rather than choosing an arbitrary isomorphism.
No adopted source-library file is changed.

## Old

The active module is absent; the archived construction is:

```lean
noncomputable def modelCompactComparisonWithoutIdentity
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  letI := hΦ.isUniversalHomeomorphism r
  (Functor.isoWhiskerLeft _
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) ≪≫
    Functor.rightUnitor _).inv ≫
      (compactCohomologyFrobeniusComparison ℓ (frobeniusIterate Φ r)).hom
```

The global-operator helper and theorem quantified over
`WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ r)`.

The old global-operator helper and theorem signature, verbatim:

```lean
noncomputable def modelCompactGlobalOperator (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ)
    (K : WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ r)) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  letI : IsFinite (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isFinite r
  letI : IsUniversalHomeomorphism (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isUniversalHomeomorphism r
  K.globalOperator 1

theorem modelCompactComparison_eq_properUnit
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) (hr : 1 ≤ r) :
    modelCompactComparisonWithoutIdentity ℓ hΦ r = modelCompactProperUnit ℓ hΦ r ∧
      (∀ (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (v : M ⟶ N),
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map v ≫
            (modelCompactProperUnit ℓ hΦ r).app N =
          (modelCompactProperUnit ℓ hΦ r).app M ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
                (frobeniusIterate Φ r)).map v)) ∧
      (∀ K : WeilBoundedConstructibleOfEnd ℓ (frobeniusIterate Φ r),
        modelCompactGlobalOperator ℓ hΦ r K =
          (modelCompactProperUnit ℓ hΦ r).app K.carrier ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              K.str.hom)
```

## New

```lean
noncomputable def modelCompactComparisonWithoutIdentity
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) :
    boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (frobeniusIterate Φ r) ⋙
        boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X) :=
  letI := hΦ.isFinite r
  letI := hΦ.isUniversalHomeomorphism r
  (Functor.isoWhiskerLeft _
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj ℓ) ℓ (point k)) ≪≫
    Functor.rightUnitor _).inv ≫
      (weilLowerShriekFrobeniusComparison ℓ (frobeniusIterate Φ r)
        (𝟙 (point k)) (toPoint X) (isPullback_toPoint X) (frobeniusIterate Φ r)
        (Category.comp_id _) (comp_toPoint _)).hom
```

The same global-operator helper and theorem now quantify over the current name
`WeilBoundedConstructible ℓ (frobeniusIterate Φ r)`, which is the category of internal
bounded constructible module objects with an invertible pullback structure for an
arbitrary endomorphism. All explicit and included geometric hypotheses, coefficient
ring, universes, naturality, and the global-operator conclusion are retained.
The theorem-local unused-hypothesis linter settings preserve the original explicit
include of algClosure, qcModel and sepModel, and the hr binder. No setting is exported.
The published globalOperator implementation is still called at degree one with the
same finiteness and universal-homeomorphism instances; it is not replaced by the
proper-unit formula. The theorem is proved using the published identity-removal and
globalOperator_eq API. A private proved helper compares the explicit proper-unit
recipe with compactPullback.

The public CompactCohomology import provides the actual comparison used in the body
of the restored definition. The archived public imports are retained. Private proof
imports of SchemeFrobeniusFiniteRadicial, BoundedConstructiblePushforwardRestriction,
CoefficientBoundedConstructibleProEtale, and redundant finite/proper imports are
removed; the imported canonical construction already supplies their needed API.

The repaired global-operator helper and theorem signature, verbatim:

```lean
noncomputable def modelCompactGlobalOperator (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ)
    (K : WeilBoundedConstructible ℓ (frobeniusIterate Φ r)) :
    (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier ⟶
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier :=
  letI : IsFinite (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isFinite r
  letI : IsUniversalHomeomorphism (frobeniusIterate (frobeniusIterate Φ r) 1).left :=
    (frobeniusIterate_one (frobeniusIterate Φ r)) ▸ hΦ.isUniversalHomeomorphism r
  K.globalOperator 1

theorem modelCompactComparison_eq_properUnit
    (hΦ : IsModelFrobenius Φ f₀ π) (r : ℕ) (hr : 1 ≤ r) :
    modelCompactComparisonWithoutIdentity ℓ hΦ r = modelCompactProperUnit ℓ hΦ r ∧
      (∀ (M N : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) (v : M ⟶ N),
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map v ≫
            (modelCompactProperUnit ℓ hΦ r).app N =
          (modelCompactProperUnit ℓ hΦ r).app M ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
                (frobeniusIterate Φ r)).map v)) ∧
      (∀ K : WeilBoundedConstructible ℓ (frobeniusIterate Φ r),
        modelCompactGlobalOperator ℓ hΦ r K =
          (modelCompactProperUnit ℓ hΦ r).app K.carrier ≫
            (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).map
              K.str.hom)
```

## Users

The active-source downstream query with --allow-missing lists zero modules. A name
and import scan of both active library roots and quarantine finds this one archived
importer. It does not mention any of the five restored declaration names; it imports
Statement and all its needed coefficient/category modules directly. No consumer
adaptation is needed. The parent nodes lem-zl-condensed-global-frobenius-comparison
and lem-zl-general-condensed-weil-realization retain their dependency on this node.
The module and its Lean attachment are restored, not withdrawn. No target type or
mathematical definition used by a target is weakened or changed in meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModelCompactComparisonUnit | Y2 (dispatcher assignment) | Restore and repair obsolete API; fill its theorem hole. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in shared claim records | Quarantined private importer; no restored declaration is mentioned; no adaptation. |

## Status

landed 20261025T051027-L-3923214 2026-10-25 (merge of deliver/Y2/Sheaf.Paper.ModelCompactComparisonUnit)
