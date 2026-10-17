## What changed

Matched the public import named in the return to the current upstream multiline spelling.
The second reader restored the current upstream module documentation describing the
open–closed proof, replacing the stale list of sorried exchange inputs, and removed a
redundant local properness instance already provided by the proof helper's binder.
The retained proof closes both exchange-isomorphism holes by the open/closed argument:
identify the mate, prove invertibility on the open, use proper base change and disjoint
support on the closed complement, then apply joint reflection of isomorphisms.

All existing public signatures, visibility, four public imports, and non-theorem
construction bodies are preserved. The retained namespace opening is documented in
`coord/changes/shriek-composition-proof-scope.md`. No dependency source is changed.

The retained proof compiled through `lcompile.py` on 2026-10-17 with exit code 0,
no warnings, in 14.5 seconds. Final compilation and dry-run output are recorded in
`scratchpad/repair-final-compile.log` and `scratchpad/repair-final-dry-run.log`.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl`

Added 0 holes; split off 0 statements; 0 remaining `sorry` in the item module.
These two closures are relative to the original returned item. At this second reading,
the current shared source already contains the retained proofs: this repair claims
0 additional hole closures against that current source.
These are proofs relative to existing imported obligations, including proper base change.
No independent completion of those dependencies is claimed.

## No longer needed

No original import, node, or target-reachable module is pruned. The added proof imports
are used. The existing private `openUnitIsIso` comes from
`import all Sheaf.Paper.CondensedOpenClosedRecollement`; its former local duplicate is
absent. No new statement or node is introduced. No DAG node attaches directly to the
assigned module; the composition unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was refused because the import parser recognized only single-line
public imports and treated its wrapped import as removed. A single-line repair then failed
the 100-character width check. During this repair the shared upstream file was itself
updated to the wrapped spelling, so the delivered header now matches current upstream
verbatim and no public-import delta is reported. This resolves the return without changing
what Lean imports or reexports, any declaration signature, or any non-theorem body.

Read-only comparisons against the current source are recorded in
`scratchpad/repair-final-interface-check.log`. All existing interfaces and construction
bodies match, and all delivered lines are at most 100 characters. No checker was changed.

The temporary second-reading section written during this attempt was removed. The next
independent reader supplies that section; the original independent reading is historical
evidence in `scratchpad/returned-report.md`, not a fresh review of this repair. The worker
dry run permits a missing second-reading section. No push was attempted.


## Second reading by H2

1. **Interfaces: pass.** Read the complete delivered module and compared it with
   the current repository source using `diff`. Also compared all ten existing public
   declaration signatures, visibility, and all non-theorem construction bodies with the
   retained original repository backup using the project's declaration parser. They are
   unchanged; no declaration was removed or added publicly. The four public imports match
   the current repository verbatim. No target or dependency source is edited. The retained
   scope record is `coord/changes/shriek-composition-proof-scope.md`.
2. **Proofs: pass relative to imported obligations.** Independently compiled the module
   through `lcompile.py`: exit 0, no errors or warnings, 13.4 seconds. A scratch copy with
   `#print axioms` for all ten private proof helpers, both exchange theorems, the exchange
   definition, and all four composition definitions compiled in 13.9 seconds. Each lists
   only `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`. There is no
   `sorry` in this module, no forbidden axiom/unsafe/opaque/extern/implemented_by declaration,
   no hollow definition introduced, and no new selection of existential data. Existing
   composition construction bodies are untouched. Logs: `scratchpad/second-reader-axioms.log`
   and `scratchpad/second-reader-interface.log`.
3. **Splits: pass (none).** No statement is split off and no node is added. Read the generic
   mate lemma, imported open-unit proof, abelian closed-support API, and both proper-base-
   change statements. The local disjoint-support lemma is stronger than the existing
   complement-only private lemma and is needed on the pulled-back closed complement.
   Checked the argument for an empty open, an empty complement, and a zero complex: the
   zero-object and joint-conservativity steps continue to apply without a hidden
   nonemptiness assumption. No restatement moves an original hole elsewhere.
4. **Route and pruning: pass.** The exchange is identified with the actual adjunction mate;
   full faithfulness proves its open restriction invertible. Both closed restrictions
   vanish by disjointness and proper base change. Exact pullbacks jointly reflect
   isomorphisms first on modules (kernels/cokernels), then on derived categories. Both
   coefficient specializations apply the existing proper-base-change theorem. Searched
   the existing recollement and étale composition APIs by support, joint reflection, and
   exchange; they supply the reused pieces, not an existing theorem of this same condensed
   bounded category. All added imports are private and used. Original imports and the
   composition route remain, so `## No longer needed` is complete: no pruning is claimed.
5. **DAG: pass / no attached node to update.** Scanned `dag/nodes` for a direct
   `lean.module` attachment: none names the assigned module. Read the three records whose
   text mentions composition modules and checked their unit records. They attach to other
   modules; this delivery does not alter their statements, proofs, proof dependencies,
   origins, or `realized` fields. No new node is required for a proved private helper.

Second-reading changes: restored the stale module documentation to the current repository
wording, clarified the report's original-versus-current closure accounting, and removed
the redundant properness instance described below.
The current shared Lean source already contains the substantive exchange proofs. The first
dry run then rejected an identical item module, so removed the redundant local
`have : IsProper p'.left := inferInstance` inside `exchangeIsIsoOfProperBC`: that instance
is already a binder of the helper. This shortens the proof without changing its argument.
No signature, construction body, import, DAG record, or checker was changed.

The final proof cleanup compiled cleanly in 14.1 seconds; see
`scratchpad/second-reader-final-compile.log`.
