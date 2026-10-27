# chartSourceCoordinateComparison

## Reason

The original unconstrained search for separatedness of the composite open inclusion
and pullback projection took about 34 seconds in the profile. Supply the composition
proof and the separated base-change proof explicitly. This changes only a proof of `IsSeparated`, a
proposition. Lean proof irrelevance preserves the resulting isomorphism definitionally;
its signature, every data-valued factor, and its mathematical meaning stay the same.
No target review is reopened by this proof-term replacement.

Original typeclass binders are named so these proofs can refer directly to the
existing hypotheses. No binder type, order or visibility changes.

The analogous finite-type and quasi-compactness instances in the `chartEpsilon_standing_composition` statement
and the etale-composition instance in the neighbourhood proof are also supplied
explicitly. The theorem proposition is unchanged by proof irrelevance.

## Old

```lean
def chartSourceCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (hc : Etale (O.ι ≫ chartCoordinateDifferences d h u))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := P.noetherian (pullback.fst h h ≫ (h ≫ aV))
  letI := P.noetherian ((O.ι ≫ pullback.fst h h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (O.ι ≫ pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := hc
  letI : IsSeparated ((O.ι ≫ chartCoordinateDifferences d h u) ≫
      (AffineSpace (ULift.{u} (Fin d)) U ↘ U)) :=
    (chartCoordinateDifferences_over d h u O).symm ▸
      inferInstanceAs (IsSeparated (O.ι ≫ pullback.fst h h))
  letI := IsSeparated.of_comp (O.ι ≫ chartCoordinateDifferences d h u)
    (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N O.ι (pullback.fst h h)
            (O.ι ≫ pullback.fst h h) rfl (pullback.diagonal h) s hs ≪≫
          (P.chartSectionEtaleRestriction N (O.ι ≫ chartCoordinateDifferences d h u)
            (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (O.ι ≫ pullback.fst h h)
            (chartCoordinateDifferences_over d h u O)
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) s
            (sq.w.trans (Category.id_comp _))).symm)
```

## New

```lean
def chartSourceCoordinateComparison (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} [IsAffine U] [IsAffine V]
    (d : ℕ) (h : U ⟶ V) [hh : IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (u : U ⟶ AffineSpace (ULift.{u} (Fin d)) V)
    (O : (pullback h h).Opens) (s : U ⟶ O.toScheme)
    (hs : s ≫ O.ι = pullback.diagonal h)
    (hc : Etale (O.ι ≫ chartCoordinateDifferences d h u))
    (sq : IsPullback s (𝟙 U) (O.ι ≫ chartCoordinateDifferences d h u)
      (AffineSpace.zeroSection (ULift.{u} (Fin d)) U))
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    Dnc.sourceSection P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.obj
          (P.chartStandardSection U d (h ≫ aV)) :=
  letI := P.noetherian aV
  letI := P.noetherian (h ≫ aV)
  letI := P.noetherian (pullback.fst h h ≫ (h ≫ aV))
  letI := P.noetherian ((O.ι ≫ pullback.fst h h) ≫ (h ≫ aV))
  letI := Dnc.compactifiable P (pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (O.ι ≫ pullback.fst h h) (h ≫ aV)
  letI := Dnc.compactifiable P (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (h ≫ aV)
  letI := P.noetherian ((AffineSpace (ULift.{u} (Fin d)) U ↘ U) ≫ (h ≫ aV))
  letI := hc
  letI : IsSeparated ((O.ι ≫ chartCoordinateDifferences d h u) ≫
      (AffineSpace (ULift.{u} (Fin d)) U ↘ U)) :=
    (chartCoordinateDifferences_over d h u O).symm ▸
      MorphismProperty.comp_mem _ O.ι (pullback.fst h h)
        (IsSeparated.isSeparated_of_mono O.ι)
        (IsSeparated.isStableUnderBaseChange.of_isPullback
          (IsPullback.of_hasPullback h h).flip hh)
  letI := IsSeparated.of_comp (O.ι ≫ chartCoordinateDifferences d h u)
    (AffineSpace (ULift.{u} (Fin d)) U ↘ U)
  Dnc.sourceComparison P d (pullback.fst h h) (h ≫ aV) (pullback.diagonal h) ≪≫
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.mapIso
        (P.chartSectionEtaleRestriction N O.ι (pullback.fst h h)
            (O.ι ≫ pullback.fst h h) rfl (pullback.diagonal h) s hs ≪≫
          (P.chartSectionEtaleRestriction N (O.ι ≫ chartCoordinateDifferences d h u)
            (AffineSpace (ULift.{u} (Fin d)) U ↘ U) (O.ι ≫ pullback.fst h h)
            (chartCoordinateDifferences_over d h u O)
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) U) s
            (sq.w.trans (Category.id_comp _))).symm)
```

## Users

`tools/downstream.py` with `--uses chartSourceCoordinateComparison` lists the following
three modules. Their uses were read; none requires adaptation because only a proof
argument changed. Current claims were checked in `coord/claims`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalDncChartNormalization | T5 | proof instance supplied explicitly |
| Sheaf.Paper.CentredDiagonalSourcePasting | unclaimed | definitionally identical map |
| Sheaf.Paper.PurityCompositionCompatibleDncCharts | unclaimed | definitionally identical map |

## Status

landed 20261026T002820-L-117385 2026-10-26 (merge of deliver/T5/Sheaf.Paper.DiagonalDncChartNormalization)
