## What changed

Repaired the landing refusal by retiring the false arbitrary-alpha declaration
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations_d`.
Its corrected statement was exactly the existing `exists_chart_completed_localizations`.
The D module retains its public section-module import, declares no replacement theorem,
and documents the existing canonical theorem to use. Its DAG node points to that theorem.

Forced adaptation of `PuncturedCompletionChartCompletedLocalizations`: remove the obsolete
Alpha and D proof imports and replace the proof using the retired false theorem by a named
construction hole. Its signature and visibility stay unchanged; its source and proof docstring are retained.
An additional D blueprint tag records that both nodes now use this canonical theorem.
The change record is `coord/changes/exists-chart-completed-localizations-d.md`.

The delivery tool rebases this repair on freshly fetched sheaf-dag. Single-file compilation
and the delivery preflight check the resulting sources; nothing is pushed by this worker.

## Proved and sorry left

Mathematical proofs completed: 0 of 1. Retired hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations_d`
(node `lem-sbc-punctured-completion-chart-completed-localizations-d`).

One existing canonical theorem now has the named construction hole:
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_chart_completed_localizations`
(node `lem-sbc-punctured-completion-chart-completed-localizations`).
No new declaration or split-off theorem is added. Holes removed: 1; holes added: 1;
net: 0. This repairs a false statement and consolidates a duplicate, not a proof reduction.
The remaining canonical theorem's docstring specifies the localization, affine pullback,
overlap, scalar compatibility and generator arguments, including empty charts.

## No longer needed

Removed the caller's proof imports of
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizationsAlpha` and
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizationsD`.
The caller no longer uses `exists_chart_completed_localizations_alpha` or
`exists_chart_completed_localizations_d`, or their separate proof nodes
`lem-sbc-punctured-completion-chart-completed-localizations-alpha` and
`lem-sbc-punctured-completion-chart-completed-localizations-d`.
The D node reuses the canonical construction node rather than maintaining another proof.
No definition dependency or realized unit step is removed; the unit has no realized attachment
for these auxiliary nodes. The existing canonical theorem remains on the target route.

## Where the brief, the DAG or earlier work was wrong

The old arbitrary-alpha statement is false. The previous repair correctly changed it to joint
existence but missed that this is exactly the existing canonical theorem. The earlier second
reading's claim that no duplicate existed was wrong. Reversing the imports while retaining
both original proofs would create a cycle: the canonical theorem originally imported D.
This repair removes the duplicate rather than reproducing its statement under another name.
It explicitly keeps the canonical construction obligation open and claims no net progress.

## Forced adaptations

Only `Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizations`
is adapted (unclaimed). Original proof line 88 calls the removed D theorem; compiling the
original against the delivered D module reports an unknown identifier. The changed lines
remove its two proof imports and replace the three-line proof by `sorry`. This is necessary
because the old proof uses a false, retired premise. Its statement and public visibility are
identical. An additional D blueprint tag is required by preflight because the retired D node now points
to this same canonical theorem. No unrelated proof or declaration is changed.

## Second reading by R4

1. **Statements and interfaces.** Compared both delivered modules with the repository versions
   and checked all declaration signatures. The canonical theorem keeps its signature; the D
   theorem is deliberately retired under the recorded change, and the caller's signature and
   visibility are unchanged. Verdict: pass.
2. **Proof and axioms.** Compiled both files with `lcompile.py --all`; there are no errors,
   forbidden declarations, or hollow definitions. The only remaining hole is the named
   canonical construction theorem, with its existing proof docstring and node. Verdict: pass.
3. **New or split statements.** No new theorem is introduced. The former arbitrary-alpha
   statement is false because alpha may be negated, while the canonical joint statement is
   already present and is exactly the needed construction. Verdict: pass.
4. **Pruning and dependencies.** The caller no longer imports or invokes the obsolete Alpha and
   D proof modules; the DAG records those dependencies as removed and redirects the D node to
   the canonical theorem. The unit's realized route is unchanged (these auxiliary nodes had no
   realized attachment). Verdict: pass.
5. **DAG agreement.** The D node's Lean record, proof, proof dependencies, and proof origin
   agree with the retired interface and canonical theorem; the change record names the forced
   adaptation and unchanged caller interface. Verdict: pass.

Changed the D module to document the retirement, adapted the canonical caller to leave one
named construction hole, redirected the D node, and recorded the interface change.

## Forced adaptations

### Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizations
Original against changed dependencies failed:
```
/tmp/forced-adaptation-gmoupsyo/lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedCompletionChartCompletedLocalizations.lean:88:28: error(lean.unknownIdentifier): Unknown identifier `exists_chart_completed_localizations_d`
/tmp/forced-adaptation-gmoupsyo/lean/Sheaf/AlgebraicGeometry/Morphisms/PuncturedCompletionChartCompletedLocalizations.lean:88:9: error: Tactic `rcases` failed: `x✝ : ?m.441` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-gmoupsyo/.lbuild) [4.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
