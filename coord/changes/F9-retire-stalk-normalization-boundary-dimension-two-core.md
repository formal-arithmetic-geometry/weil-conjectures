# AlgebraicGeometry.Scheme.stalk_normalization_boundary_dimension_two_target

## Reason

The human-approved retirement listed in `coord/retire-items.tsv` replaces
`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore` with its existing upstream twin `WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`.
The upstream theorem omits the unused `hS` and `hs` hypotheses. The sole direct
consumer must omit those two arguments when applying it. This is an import and
proof adaptation; every consumer signature and all upstream files stay verbatim.

## Old

Declared by `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`:

```lean
theorem stalk_normalization_boundary_dimension_two_target {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    let a := S.fromSpecStalk s
    ∀ y : (pullback c a : Scheme.{u}),
      y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤
        ringKrullDim ((pullback c a).presheaf.stalk y)
```

## New

Use the existing declaration in `WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore`:

```lean
theorem stalk_normalization_boundary_dimension_two_target {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (s : S)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s)
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth
      (R := S.presheaf.stalk s) (S.presheaf.stalk s)) :
    let a := S.fromSpecStalk s
    ∀ y : (pullback c a : Scheme.{u}),
      y ∉ (pullback.fst c a) ⁻¹ᵁ (c ⁻¹ᵁ U) →
      (2 : WithBot ℕ∞) ≤
        ringKrullDim ((pullback c a).presheaf.stalk y)
```

The duplicate module is withdrawn through `deleted.txt`. The consumer imports
the upstream module and applies
`stalk_normalization_boundary_dimension_two_target c U s hmin hdepth`.
The existing node keeps its mathematical statement, proof and dependencies;
its Lean attachment points to the upstream declaration and its exact signature.
No target statement or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore | F9 | Duplicate withdrawn. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwo | unclaimed | Replace proof import and omit hS and hs at the call; signature unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths | unclaimed | Indirect consumer; unchanged and checked against the adapted consumer. |

The user list was checked with `tools/downstream.py` and source searches over
both library roots and quarantined Lean files. There are no other direct users.
The retained upstream theorem has precisely the same conclusion and all needed
hypotheses; the removed hypotheses were unused in the former proof. Empty
pullbacks remain vacuous, and an empty U still uses the same hmin argument.

## Status

landed 20261020T221149-L-4151720 2026-10-20 (merge of deliver/F9/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationBoundaryDimensionTwoCore)
