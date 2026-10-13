## What changed

Repaired `glued_model_chart_pullbacks` by adding the indispensable hypothesis
`∀ i, q₀ ⁻¹ᵁ (j i).opensRange = U i`, then proved it directly with Mathlib's
`IsOpenImmersion.isPullback`. This is a recorded correction of the existing false
intermediate criterion, not a proof of its false original formulation.

Forced adaptation of `Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts` preserves
its entire public statement and visibility. Its proof now retains the actual
`exists_descended_overlap_glue_data` witnesses, constructs the glued scheme and
maps, and proves the required inverse-image equality pointwise with a proved
private helper. It uses `Scheme.GlueData.ι_eq_iff` and
`Scheme.exists_preimage_of_isPullback`. Both files compile together without warnings.
Updated both DAG proof routes. Change record:
`coord/changes/glued-model-chart-pullbacks.md`.

Repair of return X-275d6: restored the original plain import of
`Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` in the forced caller adaptation.
This addresses the landing checker's downstream visibility refusal without
editing the Jacobian module or any declaration. The delivery dry run rebases
on the current `sheaf-dag`. Both delivered files compile cleanly locally.
The exact `tools/import_prune_check.py` invocation for the adapted caller exits
0. The dry run with `WEIL_SERVER_COMPILE=1` printed OK: server compilation,
axiom probes, forced-adaptation checks and preflight passed; nothing pushed.

## Proved and sorry left

Proved the corrected intermediate criterion:
`CategoryTheory.Over.DescentDatum.glued_model_chart_pullbacks`
(node `lem-pd-glued-effective-model-charts-pullback`), after the recorded interface
correction. The original false statement is not proved and its replacement is not
claimed as a proof closure of that statement. No unchanged item hole is closed.
No holes are split off or added. No `sorry` remains in either delivered
module. The private `glued_chart_preimage` is fully proved; the existing
`CategoryTheory.Over.DescentDatum.exists_glued_effective_model_charts` remains fully
proved with exactly its original statement. This repairs one false abstraction and
preserves the caller's mathematical strength; it is not a decomposition.

## No longer needed

The old caller proof dependency `def-pd-descent-datum` is no longer a direct proof
dependency (it remains a statement dependency and is used inside the descended
overlap theorem).

Retained `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend` (node
`lem-galois-fpqc-morphisms-descend`) for downstream import compatibility: the
landing checker reports that the Jacobian module relies on reaching
`AlgebraicGeometry.Scheme.baseChangeMap` through this import. It is not a direct
proof dependency, and no pruning of this module is claimed.

Removed caller proof imports:
- `Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent` (node
  `lem-weil-pbc-open-subscheme-fpqc-descent`): no direct use; this remains needed
  transitively by `DescendedOverlapGlueData`, so no global pruning is claimed.
- `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsAux` (node
  `lem-pd-glued-effective-model-charts-aux`): its weak existential forgets the
  actual overlap identifications. Its dependency `Sheaf.AlgebraicGeometry.GluedModelStructure`
  (node `lem-pd-glued-model-compatible-charts`) is also unnecessary on this route.

The item does not need `Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle`
or its two nodes `lem-pd-glued-effective-model-chart-pullback-single` and
`lem-pd-glued-effective-model-chart-pullback-single-core`: the Mathlib criterion
applies directly. These were not imported by the baseline disputed item, but are
unnecessary lower steps. Removed the item's unused public imports `Mathlib.AlgebraicGeometry.Sites.Fpqc` and
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`; its signature uses neither
fpqc coverings nor descent data. `Restrict` supplies schemes, opens and Over.
The caller's original public imports remain because its signature uses them.
No unit statement or realized unit step is bypassed; the source's descended-overlap
construction, scheme gluing, and chart verification are all retained.

## Where the brief, the DAG or earlier work was wrong

The baseline item was already correctly marked STATEMENT-DISPUTED. Local squares
over p, commuting chart equations, and covering target embeddings do not force
cartesianity of the chart squares. The disjoint-union/fold counterexample in the
baseline docstring applies. Merely proving an inverse-image lemma for the arbitrary
witnesses of `exists_glued_model_data` would still be false. The actual gluing
construction must remain available. The caller now obtains its witnesses directly
from the proven descended-overlap interface and establishes the equality.

The item's statement dependency on the full existential caller was circular once
the caller's real proof dependency is recorded. Replaced it with the actual scheme,
open-immersion and fibre-product definition nodes, with a statement-change record.
No DAG node cites this item through stmt_deps or proof_deps at the baseline, so the
correction's citer list is empty. The only Lean caller is adapted in this delivery.
The existing single-chart node's blueprint ancestry points here but is not a
statement/proof dependency and its corrected statement is compatible.

## Forced adaptations

`Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts` is the sole forced adapted
module, unclaimed in this checkout. Its original final application to the changed
item lacks the new inverse-image argument: its type becomes a function expecting
that argument, where the existential conclusion expects chart pullbacks.
The delivery tool records the exact compiler error below after compiling the
original against this delivery's overlay; the adapted file compiles.

Changed imports retain the actual overlap interface and the two
Mathlib APIs needed to construct and inspect the gluing. The proved private helper
verifies the missing equality from local cartesian intersection
lifts. Replacement theorem proof reconstructs the witnessed gluing,
rather than unpacking a weak existential that cannot justify the new argument.
All this code is necessary to keep the original caller theorem without adding a
hypothesis or a `sorry`; every existing signature, visibility and docstring is
unchanged. The change record lists every transitive user and the sole actual caller.

The unchanged original was also checked directly with `lcompile.py` against the
compiled sandbox overlay. Exact compiler error at its original final application:

```text
GluedEffectiveModelCharts.lean:77:2: error: Type mismatch
  glued_model_chart_pullbacks U W q W₀ q₀ j hcart hopen hcover₀ hover hcomm
has type
  (∀ (i : I), q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i) →
    ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀
```

The complete delivered set and the delivery axiom probes passed. The first dry run
printed OK; its only deferred preflight requirement was the independent second
reading, which the dispatcher supplies. Nothing was pushed.

## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository using diff. The sole
   existing signature change is the declared, recorded inverse-image hypothesis
   of `glued_model_chart_pullbacks`. The caller's signature is byte-identical;
   its original docstring and visibility are unchanged. The disjoint-union/fold
   counterexample validates the correction, which is an intermediate statement
   repair, not a proof of the original false statement. No target or definition
   changes. Verdict: passes the recorded-change and forced-adaptation rules.
2. Compiled both modules together locally. Independently appended `#print axioms`
   in scratch copies for the corrected criterion, private inverse-image helper,
   and unchanged existential caller: all show exactly `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. Inspected both files:
   no sorry, axiom, unsafe, opaque, implemented_by or extern; no definitions
   or data chosen from an unproved existence theorem are added. Verdict: sound.
3. No statements are split off and no holes are added. Read the fully proved
   private helper: cover a source point by chart k, identify the common image
   using `GlueData.ι_eq_iff`, lift through the cartesian intersection, and use
   its two source projections to put the point in chart i. Reverse inclusion
   follows from the commuting equation. Empty charts and empty index types
   satisfy the same argument. Independent Mathlib grep via msearch and local
   searches found the exact existing APIs already used and no shorter duplicate
   of this specialized helper. Verdict: genuine reduction, no restatement hole.
4. The corrected criterion directly applies Mathlib's open-immersion pullback
   theorem. The caller constructs the actual descended-overlap gluing and
   proves the inverse-image equality; its weaker old existential cannot supply
   this equality. Proof imports are plain imports. Pruning lists now include
   every old caller proof dependency not used directly, including
   `def-pd-descent-datum` (still a statement/transitive dependency). Read
   `dag/units/sk-prop-jacobian-descent.json`: neither delivered node realizes a
   unit step, and the effective-descent route remains. Verdict: passes.
5. Opened both node records, compared changed fields, checked their verbatim
   Lean statements, and followed every written proof step. The corrected
   criterion's change record and stmt_deps remove the old circular dependency;
   the caller's proof_deps match descended overlaps, fpqc base change, scheme
   gluing, morphism gluing and the corrected criterion. No new nodes.
   Verdict: agrees with Lean.

Second reading changes: removed the item's two unused public imports (Fpqc and
DescentDatum); corrected its erroneous Tag 01IN citation (that tag concerns
closed immersions) to the actual Mathlib open-immersion API, retaining the
verified [Stacks 0AP4](https://stacks.math.columbia.edu/tag/0AP4) source; expanded
pruning completeness; corrected progress wording so replacing a false statement
is not counted as proving it; stored the full original statement in
statement_change.old_statement. The metadata by field retains the preflight-required
`E3 stage 2` form for an interface review performed during stage 3. No proof body or
caller statement needed repair. The final clean compile and delivery preflight
are checked below by deliver3.py.

## Second reading by E3

1. Compared both delivered modules with the repository versions. The only
   existing declaration whose statement differs is
   `glued_model_chart_pullbacks`, and the difference is the recorded
   inverse-image hypothesis in `coord/changes/glued-model-chart-pullbacks.md`.
   The caller's public statement is byte-identical. Verdict: pass.
2. Compiled the delivered modules together with `lcompile.py --all`; both
   compile without errors or warnings. Axiom probes for the corrected criterion
   and the caller show only `propext`, `Classical.choice`, and `Quot.sound`;
   no forbidden declarations or `sorry` occur in the delivered source. Verdict:
   pass.
3. The corrected criterion is a direct application of
   `IsOpenImmersion.isPullback` and introduces no split-off theorem. The caller's
   private inverse-image helper uses the actual descended overlap pullbacks and
   `GlueData.ι_eq_iff`; its pointwise argument is strictly stronger than the
   former weak existential interface and is needed for the repaired criterion.
   Empty covers and charts are covered by the same argument. Verdict: pass.
4. The proof follows the descended-overlap construction, then explicitly glues
   the scheme and morphism and verifies chart inverse images before applying the
   criterion. Removed proof-only imports and retained the downstream compatibility
   import recorded in the report. The unit route and its realized steps are kept;
   no target statement is weakened. Verdict: pass.
5. The pullback node's Lean statement, proof, dependencies, and recorded
   statement change agree with the source. The caller node retains its original
   statement and its proof dependencies describe the descended-overlap route.
   Verdict: pass.

Changed during this reading: made the caller's application explicit with
`(I := I)` to stabilize elaboration against the repaired criterion's index
parameter. No theorem statement or definition changed. The required dry run is
ready to rerun.

## Forced adaptations

### Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts
Original against changed dependencies failed:
```
/tmp/forced-adaptation-_tti47cg/lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelCharts.lean:77:2: error: Type mismatch
  glued_model_chart_pullbacks U W q W₀ q₀ j hcart hopen hcover₀ hover hcomm
has type
  (∀ (i : I), q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i) → ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀

(with the modules compiled into /tmp/forced-adaptation-_tti47cg/.lbuild) [2.0 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Forced adaptations

### Sheaf.AlgebraicGeometry.GluedEffectiveModelCharts
Original against changed dependencies failed:
```
/tmp/forced-adaptation-gcksjf0z/lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelCharts.lean:77:2: error: Type mismatch
  glued_model_chart_pullbacks U W q W₀ q₀ j hcart hopen hcover₀ hover hcomm
has type
  (∀ (i : I), q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i) → ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  ∀ (i : I), IsPullback (q i) (U i).ι (j i) q₀

(with the modules compiled into /tmp/forced-adaptation-gcksjf0z/.lbuild) [2.1 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
