## What changed

Removed the earlier attempt's false Lift and FacUniq lemmas and their nodes. In particular,
FacUniq incorrectly asserted factorization for an arbitrary function of candidate maps.
Repaired `glued_model_chart_pullback_core` by requiring the necessary inverse-image equality,
and proved this corrected criterion directly from Mathlib `IsOpenImmersion.isPullback`.
The proof-only Mathlib import is private. No target statement or definition changes. Both existing node proof records now describe
the actual corrected core and the disputed caller; the caller no longer claims to apply
the core without its missing hypothesis.
Change record: coord/changes/glued-model-chart-pullback-core.md.

## Proved and sorry left

The corrected `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_core` is proved.
This is a statement repair, NOT a proof of the original false assertion and NOT a net
hole reduction. The old core hole is removed, but the existing false caller
`CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single` is now explicitly
left with sorry (node `lem-pd-glued-effective-model-chart-pullback-single`). Its signature
is unchanged. One old hole removed, one exposed caller hole added; net zero.
No new intermediate statements with sorry are introduced; zero split off.
The two rejected prior-attempt holes `glued_model_chart_pullback_lift` and
`glued_model_chart_pullback_fac_uniq` are absent from this delivery.

## No longer needed

The unlanded prior-attempt proof imports Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackLift
and Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackFacUniq are removed, as are their
unlanded nodes lem-pd-glued-effective-model-chart-pullback-single-lift and
lem-pd-glued-effective-model-chart-pullback-single-fac-uniq. No baseline imports are removed.
The corrected core needs no scheme-gluing intermediate lemma: Mathlib suffices.
The old caller proof dependency lem-pd-glued-effective-model-chart-pullback-single-core
is no longer used by the caller and is removed from its proof_deps. The corrected core
remains in the same module, so this does not prune a baseline module. The blueprint
unit's realized arrays are empty; no realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `glued_model_chart_pullback_single` is false, as was the original core.
Take X nonempty, Y = W₀ = X, p and j identity, V = X coproduct X, U the first component,
W = X with identity structure map, q the component isomorphism, q₀ = V.hom the fold map,
and I = PUnit. Local cartesianness follows because q is an isomorphism and U.ι ≫ fold = q.
The target cover is the singleton identity map, hover is trivial, and hcomm is the same
equality. A purported pullback of j = identity would force U.ι to be an isomorphism;
its image misses every point of the second component. Both universal statements are
formally refuted in scratchpad/Counterexample.lean, with #print axioms showing only
propext, Classical.choice, Quot.sound. This scratch file is verification evidence and
is not delivered as a new library module. The old hypotheses cannot be strengthened
implicitly by arbitrary lift choices. The missing inverse-image equality must be
established from actual descended overlap data upstream, with an explicit interface repair.

The repaired core is tested on empty schemes as well: its proof is categorical and
requires no nonemptiness. For j identity its added hypothesis requires U = top, exactly
excluding the two-component counterexample. No arbitrary data is chosen from an
unproved existence theorem. Compiled corrected core and counterexample separately.


## Second reading by Y3

1. Compared the delivered module and both existing nodes with the read-only repository.
   The single-chart theorem signature is byte-for-byte identical. The only signature
   change is the core's explicit inverse-image hypothesis, documented verbatim in
   coord/changes/glued-model-chart-pullback-core.md. No definition or target changes.
   A library-wide use search found no external direct user of the core; the caller
   remains the interface for downstream users. Verdict: explicit statement repair.
2. Compiled the delivered module and a scratch copy printing both declarations' axioms.
   The corrected core uses only propext, Classical.choice and Quot.sound; the unchanged
   disputed caller has sorryAx. There are no prohibited declarations, hollow definitions,
   arbitrary witness choices, or concealed holes. Independently compiled the full core
   and caller refutations; both use only the three permitted axioms. Verdict: sound core
   proof and a correctly exposed false caller, not a net proof gain.
3. There are no new split-off statements or nodes. Checked every hypothesis of the
   two-component counterexample, including the singleton target cover. For j identity
   the repaired hypothesis forces U = top; the example fails precisely this hypothesis.
   Empty schemes cause no exception to the Mathlib argument. The remaining false caller
   is explicitly disputed; its docstring gives the intended missing step and explains
   why no complete proof exists under its present hypotheses. Verdict: no false new
   lemma, with the existing statement awaiting upstream repair.
4. Read Mathlib IsOpenImmersion.isPullback and opensRange_ι and searched the local library
   for chart pullbacks and open-range criteria. The direct Mathlib application is the
   short route; no lower scheme-gluing holes are needed. The added proof-only import is
   private; existing public imports preserve the module's export interface. Checked
   dag/units/sk-prop-jacobian-descent.json: all realized arrays are empty, and no unit
   step is bypassed. Added the old core proof dependency to No longer needed; no baseline
   module is pruned. Verdict: direct route and accurate pruning claim.
5. Checked both node proof records against Lean: the core applies the Mathlib criterion
   and extracts its limit cone, with no node proof dependencies; the caller records the
   dispute and no longer falsely claims an application of the corrected core. The core
   statement_change records the added hypothesis and the failing caller. Verdict: DAG
   agrees with the delivered proof and interface repair.

Second reading changed only the report: completed the independent review and clarified
that the old caller-to-core proof dependency is removed but no baseline module is pruned.
The corrected core and its proof were retained as written.
