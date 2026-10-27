# AlgebraicGeometry.exists_stage_isAmple_of_limit_isAmple

## Reason

The source and DAG use a small directed inverse system. The previous Lean signature
allowed an independent index universe `v`, while every stated continuity dependency
and Mathlib's affine transition limit API require `I : Type u` for `Scheme.{u}`.
The standing decision in `coord/STATE.md`, “INDEX UNIVERSES FOR LIMITS AND
FILTERED COLIMITS” (11:39 UTC, decision of L), explicitly requires the index
type to live in the objects' universe; its follow-up “INDEX UNIVERSES REPAIRED”
records the same correction for 19 earlier modules. This packet implements that
ambient smallness convention. It does not
claim to prove the former arbitrary-universe signature. No target statement changes.

## Old

```lean
theorem exists_stage_isAmple_of_limit_isAmple
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op))
    (i₀ : I) (L₀ : (D.obj (op i₀)).Modules) [L₀.IsInvertible]
    (hL : ∃ h : ((tensorPullback (c.π.app (op i₀))).obj L₀).IsInvertible,
      @IsAmple c.pt ((tensorPullback (c.π.app (op i₀))).obj L₀) h)
    : ∃ (j : I) (hij : i₀ ≤ j),
      ∃ h : ((tensorPullback (D.map (homOfLE hij).op)).obj L₀).IsInvertible,
        @IsAmple (D.obj (op j)) ((tensorPullback (D.map (homOfLE hij).op)).obj L₀) h
```

## New

```lean
theorem exists_stage_isAmple_of_limit_isAmple
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D) (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (h : i ≤ j), IsAffineHom (D.map (homOfLE h).op))
    (i₀ : I) (L₀ : (D.obj (op i₀)).Modules) [L₀.IsInvertible]
    (hL : ∃ h : ((tensorPullback (c.π.app (op i₀))).obj L₀).IsInvertible,
      @IsAmple c.pt ((tensorPullback (c.π.app (op i₀))).obj L₀) h)
    : ∃ (j : I) (hij : i₀ ≤ j),
      ∃ h : ((tensorPullback (D.map (homOfLE hij).op)).obj L₀).IsInvertible,
        @IsAmple (D.obj (op j)) ((tensorPullback (D.map (homOfLE hij).op)).obj L₀) h
```

## Users

`tools/downstream.py ... --uses AlgebraicGeometry.exists_stage_isAmple_of_limit_isAmple`
finds no call outside the item's declaration. All downstream modules were checked
for name use; their existing signatures and statements are unchanged. The only direct
importer is `Sheaf.TraceFormula.AmpleNeighbourhood`, whose proof is still unfinished
and whose index already belongs to the schemes' universe. No adaptation is needed.
DAG citers `lem-trf-model-fibre-ample-open` and `lem-sfb-space-relative-ample-locus`
have no Lean attachments and use small ambient inverse systems; both uses hold.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent | Z5 | Item: index universe repaired; proof completed. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No declaration reference; signatures and meanings unchanged; no adaptation. |

## Status

landed 20261023T135806-L-2973244 2026-10-23 (merge of deliver/Z5/Sheaf.AlgebraicGeometry.AmpleAffineLimitDescent)
