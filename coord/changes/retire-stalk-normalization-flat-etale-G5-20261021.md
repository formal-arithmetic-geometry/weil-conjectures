# AlgebraicGeometry.Scheme.finiteEtale_stalk_normalization_etale_of_flat

## Reason

Retire the zero-hole duplicate listed in `coord/retire-items.tsv`. The adopted
upstream theorem has the same normalization, finiteness premise, arbitrary source
open, flatness premise and etaleness conclusion. It drops only the unused `hS`
and `hηU` hypotheses. Applying the upstream result proves the old full signature.
The upstream theorem and every other adopted source file remain verbatim.

The current source scan has no importers of the Sheaf module. The historical
consumer in the retirement row, `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource`,
is already absent; its replacement imports the upstream module and uses its
current signature. No quarantined source references the retired module.
The one mathematical parent `lem-sbc-stalk-normalization-depth-two-section-source`
keeps its dependency on this node, whose Lean attachment now points upstream.
Other occurrences in `blueprint.from.via` are ancestry references, which remain valid.
The unit's depth-two purity step is retained. `lcompile.py` checks the full old
signature by direct application in 2.6 seconds; both axiom probes report exactly
`[propext, Classical.choice, Quot.sound]`. The unchanged upstream proof and consumer
compile cleanly in 6.4 and 3.7 seconds respectively.

## Old

Module `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`:

```lean
theorem finiteEtale_stalk_normalization_etale_of_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
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
    IsFinite n → ∀ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a)).Opens, Flat (V.ι ≫ n) → Etale (V.ι ≫ n)
```

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/Morphisms/StalkNormalizationFlatEtale.lean`
using `deleted.txt`, and attach the node to the existing declaration in
`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale`:

```lean
theorem finiteEtale_stalk_normalization_etale_of_flat {S C : Scheme.{u}}
    [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
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
    IsFinite n → ∀ V : (pullback (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization
      (pullback.fst c a)).Opens, Flat (V.ι ≫ n) → Etale (V.ι ≫ n)
```

The mathematical node statement is unchanged. Its two extra hypotheses may still
be supplied, but the theorem does not require them. No target or definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale` | G5 | Withdraw unused duplicate. |
| `WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource` | unclaimed; unchanged | Already imports upstream and calls the more general signature; compile checked. |

`tools/downstream.py` reports zero downstream modules for the Sheaf module. The
qualified declaration search reports only the copy itself, while a short-name scan
also finds the unchanged adopted consumer above. No existing consumer is adapted.

## Status

landed 20261020T211720-L-3492138 2026-10-20 (merge of deliver/G5/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFlatEtale)
