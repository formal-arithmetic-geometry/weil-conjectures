## What changed

Repaired the held intermediate theorem `glued_model_chart_pullback_single`: added
`hpreimage : q₀ ⁻¹ᵁ (j i).opensRange = U i`, then proved it from the existing
`glued_model_chart_pullback_core` and `IsPullback.of_isLimit`. The core is unchanged.
Updated node `lem-pd-glued-effective-model-chart-pullback-single`, including an explicit
statement_change. No targets or definitions changed and no hollow data were introduced.
Change record: coord/changes/glued-model-chart-pullback-single.md.

The one forced caller, Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback,
keeps its signature and visibility, but its invalid proof is replaced by a disputed
sorry and its unused private import removed. Its node now records the obstruction.

## Proved and sorry left

The corrected `CategoryTheory.Over.DescentDatum.glued_model_chart_pullback_single`
is proved with no sorry. `glued_model_chart_pullback_core` was already proved and
remains unchanged. This is a statement repair, NOT a proof of the old false assertion.
One hole is removed in the corrected item; one false caller hole is exposed.
Net holes removed: zero. Zero new intermediate statements and zero split off.

The sole sorry added is
`CategoryTheory.Over.DescentDatum.glued_model_chart_pullbacks` in the forced caller,
node `lem-pd-glued-effective-model-charts-pullback`. It is explicitly disputed.
There are no sorries left in the held module. The caller is an existing statement,
not a new false lemma introduced to pretend to prove the item.

## No longer needed

The forced caller's private proof import
`Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle` is removed, because
its former application is invalid and no longer used. This removes that caller's
edge to the held module and its two local nodes
`lem-pd-glued-effective-model-chart-pullback-single` and
`lem-pd-glued-effective-model-chart-pullback-single-core`. No other source module
imports the held module in this checkout, so the held module drops out of the
current targets' import closure through this edge. Both repaired local criteria
remain available for a later corrected gluing interface.

The forced caller's stale DAG proof dependency `lem-pd-glued-effective-model-charts`
is removed: its sorry supplies no proof from that node. This is deletion of a false
proof claim, not mathematical elimination of the actual descended-overlap argument.
No baseline public imports are removed. The held theorem uses the existing core
and needs no new gluing lemma. The unit's realized arrays are empty; no unit
statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the original single-chart theorem and its all-charts caller
are false under their displayed hypotheses. The singleton target identity chart
and first source component of V = X coproduct X give the counterexample already
checked by Y3. The existing core had previously been corrected to require the
inverse-image equality, but its caller had not been repaired. The current node's
plan already says that no proof exists; its proof_deps is empty, so there is no
remaining named plan to translate into Lean for the old statement. The previous
attempt correctly detected the issue but left no deliverable repair.

The allowed intermediate-statement repair now supplies the missing hypothesis
explicitly and gives the actual complete Lean proof. It exposes the remaining
upstream obstruction rather than asserting a false inverse-image theorem.
The node for the all-charts caller was stale: its recorded proof_deps did not name
the single-chart theorem even though its Lean proof applied it. The statement_change
therefore has no formal DAG citers, but the external Lean caller is fully recorded
in the change record and below. Empty schemes and opens cause no exception in the
corrected categorical proof. No data are chosen from unproved existence.

## Forced adaptations

Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback (unclaimed) is the only
external direct user. The unchanged original compiled against the baseline; the
unchanged original failed against the changed item with:

```
lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelChartsPullback.lean:28:2: error: Type mismatch
  glued_model_chart_pullback_single U W q W₀ q₀ j i (hcart i) hopen hcover hover hcomm
has type
  q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i → IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  IsPullback (q i) (U i).ι (j i) q₀
```

Original lines 27–28 (intro and exact) are replaced by exactly `sorry`, because
there is no inverse-image equality to pass. The signature and visibility are
unchanged. Its docstring is expanded only to document the newly exposed disputed
hole with source and counterexample. Its private proof import is removed because
it is now unused, as required by pruning. No other caller edit is made. Updated
its existing DAG proof record to match the remaining dispute. Both modules compile
individually via lcompile.py, and the delivery tool will repeat the baseline and
changed-dependency counterfactual checks and the axiom probes. This adaptation
adds one existing caller sorry and is not counted as a decomposition.

## Second reading by N4

1. Compared both delivered modules against the repository versions. The repaired single-chart
   theorem changes its intermediate statement only as declared in the change record; the
   forced caller keeps its signature and only its proof, docstring, and unused private import
   change. Verdict: pass.
2. Compiled both modules with lcompile.py. The held theorem has no sorry, axiom, unsafe,
   opaque, or hollow definition; the forced caller retains its explicitly disputed sorry.
   Verdict: pass subject to the documented caller hole.
3. Checked the corrected inverse-image hypothesis and the two-component counterexample. The
   corrected statement is true and exactly supports the core proof; the caller's unchanged
   statement is genuinely unsupported. Verdict: pass.
4. The proof uses the existing core and IsPullback.of_isLimit, and removes the caller's now
   unused private import. The old invalid proof dependency is removed from the caller node;
   the unit's realized route is unchanged. Verdict: pass.
5. Node proof, proof_deps, proof_origin, statement_change, and the forced adaptation record
   agree with the Lean sources. Verdict: pass.

Changed the single-chart statement and proof, adapted the forced all-charts caller to its
unchanged disputed interface, removed one proof-only import, and recorded the missing
inverse-image compatibility and counterexample.

## Forced adaptations

### Sheaf.AlgebraicGeometry.GluedEffectiveModelChartsPullback
Original against changed dependencies failed:
```
/tmp/forced-adaptation-hx4nz8fv/lean/Sheaf/AlgebraicGeometry/GluedEffectiveModelChartsPullback.lean:28:2: error: Type mismatch
  glued_model_chart_pullback_single U W q W₀ q₀ j i (hcart i) hopen hcover hover hcomm
has type
  q₀ ⁻¹ᵁ Scheme.Hom.opensRange (j i) = U i → IsPullback (q i) (U i).ι (j i) q₀
but is expected to have type
  IsPullback (q i) (U i).ι (j i) q₀

(with the modules compiled into /tmp/forced-adaptation-hx4nz8fv/.lbuild) [2.3 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
