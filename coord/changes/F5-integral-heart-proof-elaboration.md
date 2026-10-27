# integral_constructible_heart: coefficient transport and explicit cached presentation

## Reason

Reviewer C-26f9f requested a direct proof of the finite-model/duality clauses
and either preservation or explicit declaration of the elaborated type change.
The repair proves those clauses directly. It takes the reviewer's second option:
the final local clause now spells the coefficient object with its cached alias
and the stratum complex with the existing abbreviation. The original and new
objects and predicates are definitionally equal; this is an elaboration repair,
not a mathematical change. No hypothesis or conclusion is added or removed.

## Old

The public signature is:

```lean
theorem integral_constructible_heart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ C : SmallAdicCompletion.Modules ℓ E X,
      IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X C →
      ∃ s : Scheme.FiniteLocallyClosedStratification X,
        (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
        ∀ a : Fin s.n,
          (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
            ∀ i : 𝒰.I₀,
              ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
                Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
                Nonempty ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                    (𝒰.f i ≫ s.immersion a)).obj C ≅
                  (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) ∧
          ∃ D : integralHeartDerivedCategory.{u} ℓ E (s.domain a),
            Nonempty (ExactPairing D
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                  (s.immersion a)).obj C))) ∧
            DerivedCategory.torAmplitudeIn _ (-1) 0
              ((DerivedCategory.singleFunctor _ 0).obj
                ((CondensedRing.upperStar (integralHeartCoefficientRingObj ℓ E)
                  (s.immersion a)).obj C)) ∧
            DerivedCategory.torAmplitudeIn _ 0 1 D)
```

The original proof is `by sorry`. The returned packet disabled
`integerRingMonObj` and `integerRingComm` at this public declaration; that
command is removed from the public declaration in this repair.

## New

The public signature is now:

```lean
theorem integral_constructible_heart
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (_hp : 0 < p)
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ p)
    (E : Type v) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderIsomorphisms
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsTriangulated
      (constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ K, constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K →
      DerivedCategory.TStructure.t.bounded K ∧ ∀ n : ℤ,
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
        constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X
          ((DerivedCategory.TStructure.t.truncGE n).obj K)) ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Full ∧
    (ObjectProperty.ι (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
      DerivedCategory.singleFunctor _ 0).Faithful ∧
    (∀ K, (ObjectProperty.ι
        (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ⋙
        DerivedCategory.singleFunctor _ 0).essImage K ↔
      constantModelBoundedConstructible (integralHeartCoefficientRingObj ℓ E) X K ∧
      DerivedCategory.TStructure.t.le 0 K ∧ DerivedCategory.TStructure.t.ge 0 K) ∧
    Nonempty (Abelian (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X)) ∧
    ObjectProperty.IsClosedUnderKernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderCokernels
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    ObjectProperty.IsClosedUnderExtensions
      (IsConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible (integralHeartCoefficientRingObj ℓ E) X) ∧
    (∀ C : SmallAdicCompletion.Modules ℓ E X,
      IsConstantModelConstructible (SmallAdicCompletion.Coefficients.integerRing ℓ E) X C →
      ∃ s : Scheme.FiniteLocallyClosedStratification X,
        (∀ a : Fin s.n, Topology.IsConstructible (s.stratum a)) ∧
        ∀ a : Fin s.n,
          (∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (s.domain a),
            ∀ i : 𝒰.I₀,
              ∃ N : ModuleCat.{u + 1} (integralHeartScalars.{u} ℓ E),
                Module.Finite (integralHeartScalars.{u} ℓ E) N ∧
                Nonempty ((CondensedRing.upperStar
                    (SmallAdicCompletion.Coefficients.integerRing ℓ E)
                    (𝒰.f i ≫ s.immersion a)).obj C ≅
                  (integralHeartRealization.{u} ℓ E (𝒰.X i)).obj N)) ∧
          ∃ D : integralHeartDerivedCategory.{u} ℓ E (s.domain a),
            Nonempty (ExactPairing D
              (integralHeartStratumComplex ℓ E (s.immersion a) C)) ∧
            DerivedCategory.torAmplitudeIn _ (-1) 0
              (integralHeartStratumComplex ℓ E (s.immersion a) C) ∧
            DerivedCategory.torAmplitudeIn _ 0 1 D)
```

The first eleven factors and all binders stay verbatim. In the final factor,
`integralHeartCoefficientRingObj ℓ E` is replaced by
`SmallAdicCompletion.Coefficients.integerRing ℓ E`, and the displayed restriction
in degree zero is written `integralHeartStratumComplex ℓ E (s.immersion a) C`.
The two coefficient abbreviations have identical bodies; the stratum abbreviation
is exactly the original single-functor/upper-star expression. This avoids repeated
kernel conversion of the full dependent conjunction. Neither cached coefficient
instance is disabled on the public theorem.

Private helpers transport the categorical package along a proved equality of the
canonical and cached monoid structures. Instance removal occurs only on the
canonical private helpers. Proposition irreducibility is local to the private
helper section. The old public statement was checked against a verbatim restatement
with `Lean.Meta.isDefEq`, which returned true despite differing proof arguments for
a site instance. A comparison of the final presentation is also included in the
compile validation. The delivered Lean file contains no metaprogram or diagnostic.

The four original public imports remain. `IntegralHeartDualizable` is now a public
import because the public statement uses its stratum-complex abbreviation. The
proof additionally imports the braided exact-pairing API. No source-library
construction, coefficient definition or other public declaration is changed.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralConstructibleHeart --uses
integral_constructible_heart` lists these nine downstream modules; the only
textual declaration use is the item itself. The type presentation changes as declared above; all consumers continue to see
the same mathematical proposition, with no source adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Definitionally equal cached type presentation; completed proof. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Identical interface; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Identical interface; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Identical interface; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Identical interface; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Identical interface; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | claimed; not adapted | Identical interface; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Identical interface; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | claimed; not adapted | Identical interface; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Identical interface; no adaptation. |

## Status

landed 20261023T231053-L-3539352 2026-10-23 (merge of deliver/F5/Sheaf.Paper.IntegralConstructibleHeart)
