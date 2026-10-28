# integralSystemReduction_map_ext: dispute and a proved sufficient criterion

## Reason

The arbitrary-scheme extensionality assertion ignores a possibly nonzero Milnor
lim-one kernel. The report gives an explicit arithmetic counterexample. Preserve
the disputed signature and hole; add a separately named, proved finite-Hom
criterion to show the precise sufficient hypothesis used by the existing Milnor
proof. Correct the original DAG attachment's module-name typo.

## Old

The existing assertion, retained verbatim:

```lean
theorem integralSystemReduction_map_ext
    {X : Scheme.{u}}
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    {A B : sfIntegralConstructibleCategory l E X}
    (p q : A ⟶ B)
    (h : ∀ n : ℕ,
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map p) =
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map q)) :
    (integralSystemReduction l E X).map p =
      (integralSystemReduction l E X).map q
```

No declaration named `integralSystemReduction_map_ext_of_finite` existed.

## New

The existing assertion has exactly the old signature and hole, with a
`STATEMENT-DISPUTED` explanation. The separately named new theorem is:

```lean
theorem integralSystemReduction_map_ext_of_finite
    {X : Scheme.{u}}
    {A B : sfIntegralConstructibleCategory l E X}
    (p q : A ⟶ B)
    (hfinite : ∀ n : ℕ, Finite
      (A.obj⟦(1 : ℤ)⟧ ⟶ (sfDerivedReductionRestricted l E X n).obj B.obj))
    (h : ∀ n : ℕ,
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map p) =
        (finiteSystemDerivedEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) X n).map
          ((integralSystemReduction l E X).map q)) :
    (integralSystemReduction l E X).map p =
      (integralSystemReduction l E X).map q
```

Its proof is complete. No definition, instance, attribute, or public import is
changed. The new import of `DerivedCompleteFiniteReductionDetection` is private
to proofs. No target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralSystemReductionMapExt | Q1 | Original signature retained; proved sufficient criterion added. |
| Sheaf.Paper.IntegralPullbackTensorCompositionReduced | No holder found in shared claim records | Sole direct importer and user of the original lemma. Source unchanged; compiled against this delivery in 4.4 seconds. Its mathematical reliance on the disputed assertion remains reported for review. |

No existing consumer mentions the new declaration. No forced adaptation.

## Status

landed 20261028T055733-L-802513 2026-10-28 (merge of deliver/Q1/Sheaf.Paper.IntegralSystemReductionMapExt)
