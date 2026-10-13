## What changed

Repaired E2, C4, H8 and F1–F4. Restored the public
`exists_affine_chart_transitions_succ` with its original signature, the proved
`empty_chart_transitions`, and the original case-split proof of
`exists_affine_chart_transitions`. Removed the rejected core and arbitrary-map
realization declarations, their two new node files, and
`coord/changes/exists_affine_chart_transitions_succ.md`.

Then replaced the successor sorry with a concrete reduction. The new module
`PuncturedCompletionChartSectionModules` constructs the actual completed and chart
section modules using structural ring maps and `Module.compHom`. The chart action
uses the canonical localization isomorphism with sections on D(f), followed by
pullback. Its restriction to A is proved in `chartSectionModule_smul` using
`AlgEquiv.commutes` and naturality of the section maps.

Two new construction modules supply separate overlap-localization and completed
pullback-localization statements. Each quantifies over the fixed section modules
and constructs its own equivalences together with the restriction identities.
The successor proof combines these results into `FormalGlueing.Transitions` and
`AffineChartTransitions`, with identity identifications e and c. It imports the
construction modules for proofs only. Its existing docstring received only a line
wrap. The successor node now records this construction and these dependencies;
the main node and its use of the successor declaration remain valid.

## Proved and sorry left

Closed the one original hole in `exists_affine_chart_transitions_succ`
(node `lem-sbc-punctured-completion-affine-chart-transitions-succ`) by decomposition
into two strictly smaller construction statements. This is one hole closed and
two holes added, not a complete proof from sorry-free dependencies.

There is no sorry in the item's module. `empty_chart_transitions` remains proved,
and `exists_affine_chart_transitions` retains its original complete case split.
The actual section module definitions contain no sorry, and
`chartSectionModule_smul` is proved.

The complete list of remaining holes introduced by this delivery is:

- `exists_chart_overlap_localizations`, in
  `PuncturedCompletionChartOverlapLocalizations`, node
  `lem-sbc-punctured-completion-chart-overlap-localizations`.
- `exists_chart_completed_localizations`, in
  `PuncturedCompletionChartCompletedLocalizations`, node
  `lem-sbc-punctured-completion-chart-completed-localizations`.

Both are public named theorems with whole proofs `:= by sorry`, their own source,
blueprint id and full construction proof in the docstring. All four delivered
modules compile with `lcompile.py`; the final dry-run also checks the axiom probe.

## No longer needed

Withdrawn from the returned delivery:
`exists_affine_chart_transition_core`,
`exists_affine_chart_transition_maps`,
`lem-sbc-punctured-completion-affine-chart-transitions-core`, and
`lem-sbc-punctured-completion-affine-chart-transitions-maps`.
The false arbitrary-transition realization is not imported or reused.

No original import or existing baseline DAG module was pruned. The matching-section
and formal-glueing public imports remain necessary for the original definitions.
Each new proof import is used in the successor proof. No existing module outside
this item was adapted.

## Where the brief, the DAG or earlier work was wrong

The reviewer supplied a counterexample to the returned maps theorem: take A=Q,
its zero-ideal completion C isomorphic to Q, U=Spec A, Y=Spec A, E=Spec C,
the canonical overlap identification, one chart with f=1, the usual section modules
and alpha, and alpha_overlap(0,0)=-id. These satisfy that theorem's hypotheses.
Its two b restriction formulas and injectivity would force -m=m, contradicting
m=1. The earlier second reading's assertion that this maps theorem was true was
wrong and is withdrawn.

The correction constructs the equivalences existentially and jointly on actual
section modules. It never asserts that an arbitrary F or arbitrary e admits chart
realizations. The overlap result has no completed model or arbitrary transition
input; the completed result has no overlap alpha or b input. Thus neither can
impose the false restriction compatibility on an arbitrary negated transition.
For the counterexample data, the constructed overlap equivalence is the canonical
identity. Empty principal opens give zero sections and localized modules; repeated
charts use the same restriction maps. The construction statements also allow an
empty chart index, while the main proof retains the already proved empty case.

The deleted successor declaration was public, contrary to the previous change
record. Restoring its original signature corrects the DAG/Lean mismatch: the main
proof calls precisely the declaration its node cites. The removed core comment and
maps docstring were insufficient proof documentation. The replacements each give
explicit fraction and pure-tensor formulas, explain their universal properties,
and derive the scalar and generator identities.

## New nodes

`def-sbc-punctured-completion-chart-section-modules` records the concrete chart and
completed section modules and the proved structural action formula, in
`PuncturedCompletionChartSectionModules`. These definitions use canonical maps,
not an arbitrary witness from a sorry theorem.

`lem-sbc-punctured-completion-chart-overlap-localizations` records localization on
double chart intersections and its restriction/scalar formulas, in
`PuncturedCompletionChartOverlapLocalizations`.

`lem-sbc-punctured-completion-chart-completed-localizations` records the affine
pullback tensor-product and completed-side localization identifications, in
`PuncturedCompletionChartCompletedLocalizations`.

No change record remains: the old public successor declaration is restored, and
there are no forced adaptations of existing modules.

## Second reading by J4

1. **Repository comparison:** Compared the delivered transition module with the
repository version. Existing declaration signatures, including both transition
existence theorems and the structures, are unchanged. The delivery adds only the
proof imports and the concrete proof body, plus the separately listed construction
modules and node files.

2. **Compilation and axioms:** Compiled all four delivered modules with
`lcompile.py --all`; compilation succeeds. The only remaining `sorry`s are the two
named construction theorems listed above, each public and documented with a matching
node. No definitions contain `sorry`, and no forbidden declarations occur. The
construction modules use actual structural modules rather than arbitrary witnesses.

3. **Statement review:** The successor theorem has exactly its original type. The
two split statements quantify over fixed concrete section modules and construct the
equivalences jointly; they do not accept arbitrary transition data, so they avoid the
counterexample described above. Their restriction and scalar formulas are the exact
properties used by the successor proof and are strictly smaller than the target.

4. **Pruning and imports:** The successor proof uses both construction imports and
the section-module definitions. The two public imports remain required for the
existing structures; proof-only imports are plain `import`. The successor node's
`proof_deps` names the construction nodes, and no old proof dependency is listed as
unused.

5. **Unit route and DAG:** The positive-chart route through concrete chart modules,
overlap localization, and completed pullback localization is retained. The successor
node, the three new nodes, and their Lean declarations agree; no unit statement or
target statement was changed.

**Changes made during this reading:** no Lean proof changes were needed after
compilation. Confirmed the successor node metadata already records both construction
dependencies and replaced the withdrawn placeholder review with this review.
