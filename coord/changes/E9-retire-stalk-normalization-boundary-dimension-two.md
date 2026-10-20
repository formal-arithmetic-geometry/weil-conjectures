# AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two

## Reason

The retirement listed in `coord/retire-items.tsv` replaces the assigned
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`
with its existing upstream twin. Both theorems prove the identical conclusion;
the upstream theorem omits only the unused hypothesis `hs : s ∉ U`.
This packet performs that replacement and preserves the consumer signature.

## Old

Declared by the assigned Sheaf module:

```lean
theorem stalk_normalization_boundary_dimension_two {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z)
```

## New

Use the declaration already provided by
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo`:

```lean
theorem stalk_normalization_boundary_dimension_two {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    IsFinite n → ∀ z : (pullback
      (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a) : Scheme.{u}),
      n z ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤ ringKrullDim
        ((pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
          (pullback.fst c a) : Scheme.{u}).presheaf.stalk z)
```

The consumer replaces its private proof import and omits `hs` at this application.
Its original public `hs` binder is retained; a theorem-local unused-variable
linter setting records that the stronger upstream result no longer needs it.
The Sheaf duplicate is withdrawn through `deleted.txt`. The node's Lean attachment
points to the upstream theorem and records its exact signature. Its mathematical
statement, proof, dependencies and unit route remain in use. All upstream files
remain unchanged. No definition or target statement changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo | E9 assignment; no local claim file | Retire the duplicate under the listed retirement. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths | unclaimed in local snapshot | Replace proof import, omit hs at the call, retain signature. |

`tools/downstream.py` lists exactly the consumer above. Source scans over
`lean/Sheaf`, `lean/WeilConjectures` and `quarantine` find no other importers.
The sole attached node is `lem-sbc-stalk-normalization-boundary-dimension-two`;
its parent `lem-sbc-stalk-normalization-formal-boundary-depths` still invokes
that node through the adapted consumer. The parent edges need no change because
the mathematical result is preserved, rather than bypassed.

The conclusion is identical for every source point, including the vacuous empty
normalization case. If s belongs to U, the omitted hypothesis is unnecessary:
the boundary condition and minimality still give the same dimension argument.
For the stated node, s outside U remains an available assumption. Empty U and
empty pullbacks introduce no new obligation. The unit's depth-two extension step
still uses boundary dimension, normality and the flat local depth formula.

## Status

landed 20261020T233131-L-898052 2026-10-20 (merge of deliver/E9/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo)
