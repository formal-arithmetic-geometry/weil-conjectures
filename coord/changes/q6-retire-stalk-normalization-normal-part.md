# AlgebraicGeometry.Scheme.stalk_normalization_normal_part

## Reason

The item is a duplicate listed in `coord/retire-items.tsv`. Its public theorem already has a
complete adopted proof in `WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`.
Keep that source module verbatim, switch the only remaining direct Sheaf importer to it,
withdraw the duplicate Sheaf module, and reattach its existing DAG node to the source theorem.
This prevents two modules from declaring the same public name. No mathematical statement,
definition, hypothesis, conclusion, or target changes.

## Old

`Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart` declares:

```lean
theorem stalk_normalization_normal_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z)
```

Its consumer imports `Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart`.

## New

`WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart` already declares, and is preserved verbatim:

```lean
theorem stalk_normalization_normal_part {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c]
    (U : S.Opens)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    ∀ z : (pullback f.fromNormalization l : Scheme.{u}),
      IsDomain ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z) ∧
      IsIntegrallyClosed ((pullback f.fromNormalization l : Scheme.{u}).presheaf.stalk z)
```

The old unused `let n` reduces away. A scratch compatibility theorem with the complete old
signature is proved by `exact stalk_normalization_normal_part hS c U PA s`, importing only
its canonical module. Both proofs have exactly the three permitted axioms.

The duplicate Sheaf module is withdrawn via `deleted.txt`. The only changed consumer line is
its proof import, switched from the Sheaf module to the canonical module; every declaration
and proof in that consumer is unchanged. The node keeps its mathematical statement, proof
steps, and proof dependencies, with `lean` pointing to the canonical module and signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart | Q6 assignment; no current claim file | Withdraw duplicate only. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths | unclaimed | Only direct importer returned by downstream.py; one proof import migrated; compiles. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense | unclaimed | DAG parent already imports the canonical module; unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFormalBoundaryDepths | unclaimed | Already imports the canonical module; unchanged. |

The two DAG parents are `lem-sbc-stalk-normalization-formal-boundary-depths` and
`lem-sbc-stalk-normalization-normal-dense`; both retain the same dependency node. There are
no importers in quarantine. The unit and its realized proof steps stay unchanged.

## Status

landed 20261020T221312-L-4170814 2026-10-20 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalPart)
