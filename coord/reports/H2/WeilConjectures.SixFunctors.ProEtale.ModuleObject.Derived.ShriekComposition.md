## What changed

Retained the completed proofs of the two open/proper exchange-isomorphism theorems and
repaired the return at head `d1c66b2f3`: removed the duplicate private `openUnitIsIso`
proof. The bounded open-unit argument now uses the existing theorem from
`Sheaf.Paper.CondensedOpenClosedRecollement`, accessed with a proof-only `import all`,
as other library consumers already do. The recollement module is unchanged.

The exchange proof uses the adjunction mate on the open and proper base change with
vanishing on the closed complement, then joint conservativity. Public statements and
composition constructions retain their original interfaces. The proof-scope edit remains
documented in `coord/changes/shriek-composition-proof-scope.md`.

Validation: the repaired module compiles cleanly with `lcompile.py` in 14.1 seconds.
`tools/import_prune_check.py` accepts the repaired source. The declaration comparison
reports zero statement changes, only the two completed original theorem bodies, and
no changed construction body. The required delivery dry run is the final check.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange`
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleLowerStarOpenImmersionLowerShriekExchange_padicAlgCl`

Added 0 holes; split off 0 statements. The assigned module contains 0 remaining `sorry`
declarations. Existing imported obligations retain their declarations; none is restated.
This repair removes a duplicate already-proved private helper and adds no proof obligation.

## No longer needed

Removed the delivered duplicate private `openUnitIsIso`, reusing the existing recollement
helper instead. The baseline module had no direct `Sheaf.Paper.ProfinitePointPullback`
import; the recollement proof import supplies the private helper used by this proof. All
four original public imports remain required. No original DAG node or module is pruned from
the targets' closure.

The earlier draft imports of `Functor.ReflectsIso.Exact` and the directly imported
derived exact-functor module remain absent.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a duplicate theorem. Its existing declaration is private,
but `import all` makes it available for proof reuse; copying its proof was unnecessary.
The repaired bounded open-unit helper now applies that existing declaration directly.

No DAG node attaches to this module and its declarations have no blueprint IDs. The
proof retains the open/proper exchange step of `sk-thm-sf-comp-composition`; no unit
route is bypassed and no new statement or definition needs a node.

The retained sandbox includes local artifacts of unchanged source dependencies because
the published compiled library and source checkout differ. Diagnostic source copies and
local compilation artifacts stay under `scratchpad/` and `.lbuild`, outside the delivered
`lean/` tree. The repair's validation refreshed incompatible local dependency artifacts from unchanged
shared source. In particular, the bounded-constructible module compiles in 43.4 seconds
after refreshing its constructible and derived tensor inputs; no timeout limit or source
definition was changed.

The long original public import remains wrapped across two lines to meet the 100-character
limit. The statement-change parser misreports that wrapping as removal, although Lean and
the import-pruning check preserve the same public import. The change record documents it.
The current downstream check finds five consumers, including `TraceFormula.Basic`, all
listed in the updated change record with unchanged interfaces and no adaptations.

The previous second reading covered the returned version; it is saved in
`scratchpad/returned-report.md`. A fresh second reading must check this repaired version.

## Second reading by H2

1. **Interfaces and accidental changes: PASS.** I compared the delivered module with the
repository version. The ten existing public declaration signatures and all existing
construction bodies are unchanged; the two original theorem bodies are the only existing
proof bodies replaced. The original four public imports are preserved (one is wrapped to
respect the line limit), and the four added imports are proof-only. The namespace opening
change is recorded in `coord/changes/shriek-composition-proof-scope.md`; no downstream
module needs adaptation.

2. **Compilation and axioms: PASS.** `lcompile.py` compiles the module without errors or
warnings. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. The two target theorems and the unchanged constructions have only the
permitted kernel axioms plus inherited `sorryAx` from imported obligations; the delivered
proof introduces no new axiom or hollow definition.

3. **Statements and split holes: PASS.** No statement was changed, no new public theorem
was split off, and no `sorry` was added. The two closed theorems retain their exact original
signatures. The private helper arguments cover the empty-open and empty-complement cases
through `IsZero` and do not assume nonemptiness. Searches of the imported module-object,
recollement, and category-theory APIs found no existing public theorem that directly
replaces the exchange argument.

4. **Route and pruning: PASS.** The proof uses the mate description on the open, proper
base change and disjoint-support vanishing on the closed complement, then derived
open-closed joint conservativity. The composition and conjugation constructions remain
unchanged, so the unit route `sk-thm-sf-comp-composition` is retained. Every added proof
import is used; no original target-reachable node or module is pruned.

5. **DAG agreement: PASS.** No DAG node has this module as its `lean.module`, and no new
statement or split theorem requires a node. The unit record and its realized route are
unchanged. The proof dependencies recorded by the existing module remain sufficient.

I corrected the report's stale wording about a direct `ProfinitePointPullback` import; that
import was not present in the repository baseline. No Lean source or declaration required
repair in this second reading.
