# AlgebraicGeometry.Etale.finiteTor_directImage_coefficients

## Reason

Complete the assigned theorem from the existing direct-image bound, constructibility,
residue Tor window, scalar-flat-model and projection/mate declarations. The additional
local irreducibility attributes keep the final use of the mate-isomorphism helper from
unfolding the chosen derived functors. With a typed projection-isomorphism instance the
complete file compiles in approximately 15 seconds, within the unchanged 60-second limit.

The static gate treats changed attribute commands as a possible interface change and
requests this record. Both attributes are explicitly local. Every public signature,
public import and existing definition is unchanged; three new helpers are private and
proved. No target statement or target definition changes meaning.

## Old

```lean
attribute [local instance 20000] CommRing.toRing
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

theorem finiteTor_directImage_coefficients
    (p l : ℕ) (_hp : 0 < p) [Fact l.Prime] (_hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (U V : Scheme.{u}) [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] :
    ∃ c : ℕ,
      (∀ (M : Sheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (coefficientExtensionRing l E n))) (q : ℕ), c < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) ∧
      (∀ (K : DerivedCategoryModule (coefficientExtensionRing l E n) U)
        (a b : ℤ), a ≤ b →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
          (finite_coefficientExtensionRing l E n hn) U K →
        DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) U a b K →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) V
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) V a (b + c)
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          ∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (φ : coefficientExtensionRing l E n →+* B),
            IsIso ((scalarMate φ h).app K) ∧
              (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).map
                  ((scalarMate φ h).app K) ≫
                  (scalarRestrictionDirectImageMap φ h).app ((scalarExtension φ U).obj K) =
                (scalarTensorIso φ V).hom.app
                    (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ≫
                  ((rightDerivedLowerStarProjectionMap
                    (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).app K).app
                    (scalarCoefficient φ V) ≫
                  R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).map
                    (((derivedTensor
                        (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) U).obj K).map
                        (scalarCoefficientPullbackIso φ h).hom ≫
                      (scalarTensorIso φ U).inv.app K)) ∧
      (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
        (φ : coefficientExtensionRing l E n →+* B)
        (W : Scheme.{u}), (W = U ∨ W = V) →
        ∀ (J : DerivedCategoryModule (coefficientExtensionRing l E n) W)
          (r s : ℤ), r ≤ s →
          @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) W J →
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) W r s J →
          DerivedCategory.isBoundedConstructible B W ((scalarExtension φ W).obj J) ∧
            DerivedCategory.hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J))
```

## New

```lean
attribute [local instance 20000] CommRing.toRing
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar
  scalarMate rightDerivedLowerStarProjectionMap

theorem finiteTor_directImage_coefficients
    (p l : ℕ) (_hp : 0 < p) [Fact l.Prime] (_hlp : l ≠ p)
    (k : Type u) [Field k] [CharP k p]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (U V : Scheme.{u}) [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    (h : U ⟶ V) [h.IsOver (Spec (.of k))] :
    ∃ c : ℕ,
      (∀ (M : Sheaf U.smallEtaleTopology
          (ModuleCat.{u + 1} (coefficientExtensionRing l E n))) (q : ℕ), c < q →
        IsZero ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).obj
          (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj M)))) ∧
      (∀ (K : DerivedCategoryModule (coefficientExtensionRing l E n) U)
        (a b : ℤ), a ≤ b →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
          (finite_coefficientExtensionRing l E n hn) U K →
        DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) U a b K →
        @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) V
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) V a (b + c)
            (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ∧
          ∀ (B : Type (u + 1)) [CommRing B] [Finite B]
            (φ : coefficientExtensionRing l E n →+* B),
            IsIso ((scalarMate φ h).app K) ∧
              (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ).map
                  ((scalarMate φ h).app K) ≫
                  (scalarRestrictionDirectImageMap φ h).app ((scalarExtension φ U).obj K) =
                (scalarTensorIso φ V).hom.app
                    (R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).obj K) ≫
                  ((rightDerivedLowerStarProjectionMap
                    (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).app K).app
                    (scalarCoefficient φ V) ≫
                  R(lowerStar (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) h).map
                    (((derivedTensor
                        (ModuleCat.{u + 1} (coefficientExtensionRing l E n)) U).obj K).map
                        (scalarCoefficientPullbackIso φ h).hom ≫
                      (scalarTensorIso φ U).inv.app K)) ∧
      (∀ (B : Type (u + 1)) [CommRing B] [Finite B]
        (φ : coefficientExtensionRing l E n →+* B)
        (W : Scheme.{u}), (W = U ∨ W = V) →
        ∀ (J : DerivedCategoryModule (coefficientExtensionRing l E n) W)
          (r s : ℤ), r ≤ s →
          @DerivedCategory.isBoundedConstructible (coefficientExtensionRing l E n) _
            (finite_coefficientExtensionRing l E n hn) W J →
          DerivedCategory.hasTorAmplitudeIn (coefficientExtensionRing l E n) W r s J →
          DerivedCategory.isBoundedConstructible B W ((scalarExtension φ W).obj J) ∧
            DerivedCategory.hasTorAmplitudeIn B W r s ((scalarExtension φ W).obj J))
```

The theorem now has a complete proof and the three proved private helpers
`bounded_of_constructible`, `scalar_constructible_tor` and `coefficient_killed`.
The additional imports serve the proof and are not public imports.

## Users

`tools/downstream.py Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients --uses
AlgebraicGeometry.Etale.finiteTor_directImage_coefficients` reports zero downstream
modules and one textual use, in the item itself. DAG parents with unfinished proofs
continue to use exactly the same statement; no parent dependency or unit route changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | V1 | Existing statement unchanged; proof completed. |

No consumer adaptation is required. Local attributes have no effect on importers.

## Status

landed 20261022T202102-L-1254739 2026-10-22 (merge of deliver/V1/Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients)
