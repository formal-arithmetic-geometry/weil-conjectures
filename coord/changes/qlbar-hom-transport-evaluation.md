# AlgebraicGeometry.ProEtale.QlbarInternalHom.HomTransportNormalized

## Reason

Refer to the existing canonical `ModuleObjectRingedComparison.internalEvaluation`
instead of expanding its braiding/counit composite again. Its definition expands
verbatim to the old expression, so the proposition is definitionally unchanged.
The repeated expansion made checking the two evaluation fields in
`coefficient_comparison_roof` take about 19 extra seconds in the kernel and pushed
the complete file above the 60-second limit. The named map matches the existing
`HomPresentation.evaluation` interface directly. Its defining module is added as a
plain `import` (it is already imported, privately, through
`Sheaf.Paper.InternalSectionHomContinuityComparison`), and `HomTransportNormalized` is
marked `@[no_expose]`, so that its body may name `internalEvaluation`.

Reviewer correction (2026-10-26; given first on head 042fc66d1af and dropped by this
re-delivery, re-applied on 71cf87a60cf0): a `public import` of the module exposes its
transitive coefficient instances to every importer and breaks two of them
(`Sheaf.Paper.FiniteModelTopologyComparisonMaps` line 112 and
`Sheaf.Paper.QlbarBoundedTensorColimit` line 120: `stuck at solving universe
constraint u + 1 =?= max (u + 1) ?u` for `EssentiallySmall X.ProEt`). With the plain
import and `@[no_expose]` the item and all three direct importers compile. The only
effect visible to other modules is that the body of `HomTransportNormalized` is not
unfolded outside this module; no other module names it or `coefficient_comparison_roof`.

No target statement uses `HomTransportNormalized`; it is used only by the auxiliary
roof theorem. No hypothesis, conclusion, universe or chosen map changes. This
refactor also agrees on zero objects, the empty scheme, and identity coefficient
maps because it is a definitional equality, not a conditional mathematical claim.

## Old

```lean
def HomTransportNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (S : WeilConjectures.CoefficientClosedStructure (hom R X))
    (T : WeilConjectures.CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring R X) S)
    (t : TensorComparison R X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
      ((forward R X).op.prod (forward R X)) ⋙ hom R X) : Prop :=
  ∀ K N : DerivedCategory (Internal R X),
    (forward R X).map
      ((@BraidedCategory.braiding _ _ _ (internalBraiding R X)
          (((CondensedRing.derivedHom R X).obj (op K)).obj N) K).hom ≫
        (CondensedRing.derivedTensorHomAdjunction R K).counit.app N) =
      t.iso.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward R X).obj (((CondensedRing.derivedHom R X).obj (op K)).obj N),
            (forward R X).obj K))
          (Y := ((hom R X).obj (op ((forward R X).obj K), (forward R X).obj N),
            (forward R X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward R X).obj K)) ≫
        S.evaluation ((forward R X).obj K) ((forward R X).obj N)
```

## New

```lean
@[no_expose] def HomTransportNormalized
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (S : WeilConjectures.CoefficientClosedStructure (hom R X))
    (T : WeilConjectures.CoefficientTensorModels.{u, u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (ring R X) S)
    (t : TensorComparison R X S T)
    (θ : Functor.uncurry.obj (CondensedRing.derivedHom R X) ⋙ forward R X ≅
      ((forward R X).op.prod (forward R X)) ⋙ hom R X) : Prop :=
  ∀ K N : DerivedCategory (Internal R X),
    (forward R X).map (internalEvaluation R X K N) =
      t.iso.hom.app (((CondensedRing.derivedHom R X).obj (op K)).obj N, K) ≫
        S.tensor.map
          (X := ((forward R X).obj (((CondensedRing.derivedHom R X).obj (op K)).obj N),
            (forward R X).obj K))
          (Y := ((hom R X).obj (op ((forward R X).obj K), (forward R X).obj N),
            (forward R X).obj K))
          (θ.hom.app (op K, N), 𝟙 ((forward R X).obj K)) ≫
        S.evaluation ((forward R X).obj K) ((forward R X).obj N)
```

## Users

`tools/downstream.py Sheaf.Paper.QlbarInternalHomCoefficientComparison --uses
HomTransportNormalized` lists the five downstream modules below, and reports only
the item itself as actually using this declaration (three occurrences). Each of
the five source files was checked: none mentions the definition or the roof theorem.
No consumer needs an adaptation. There are no active claim files for those five
modules at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | U4 | Same normalized evaluation proposition; proof uses existing presentation fields. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | No direct use; statements and definitions retain their meaning. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | No direct use; statements and definitions retain their meaning. |
| Sheaf.Paper.GlobalInternalHomDetection | unclaimed | No direct use; statements and definitions retain their meaning. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | No direct use; statements and definitions retain their meaning. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | No direct use; statements and definitions retain their meaning. |

The owning node gains the existing definition node
`def-sfb-internal-section-hom-comparison-data` in `stmt_deps`; its mathematical
statement is unchanged. The delivery adds no axiom or sorry and adapts no other
module. The full item compiles cleanly in 47.2 seconds through `lcompile.py` (exit code 0).
The independent delivery reviewer checks the definitional replacement and consumer audit.

The returned head `042fc66d1af` passed review but could not land because the
reviewer override was named `qlbar-hom-transport-evaluation.md`. The stage-3 landing
interface (`tools/batch_land.py`, `fixes`) addresses a change-record override as
`<record-stem>.change.md`. If this record requires a reviewer override, its filename
must therefore be `qlbar-hom-transport-evaluation.change.md`; the delivery path
remains `coord/changes/qlbar-hom-transport-evaluation.md`. This repair includes the
record at that path and refreshes the owning node from current main before applying
only the delivery-owned changes. No mathematical repair was requested by the review. The repaired packet compiled
cleanly through a fresh server request in 51.3 seconds (exit code 0).

## Status

landed 20261026T002950-L-134916 2026-10-26 (merge of deliver/U4/Sheaf.Paper.QlbarInternalHomCoefficientComparison)
