## What changed

Repaired the landing return from reviewer X-0a8cc: the corrected relation theorem
was a duplicate of the already proved
`RingTheory.exists_stage_flat_relation_factorization_of_preserves`. Withdrawn
`lean/Sheaf/RingTheory/ColimitFlatRelationDescent.lean` through `deleted.txt`;
the landing leaves an empty module. No replacement wrapper or alias is introduced.
Both actual callers, `IdealKernelElementDescent` and `FiniteIdealKernelDescent`,
now import `ColimitFlatRelationDescentElementwise` and apply its existing theorem
directly. The relation node's Lean attachment names that existing declaration.
No caller still imports the withdrawn module or uses the retired theorem.

The earlier reviewed preservation correction remains in the three unclaimed
independent-universe interfaces: `FiniteIdealKernelDescent`,
`ColimitMaximalKernelDescent` and `ColimitEventuallyFlat`. Their complete original
proofs remain, with the finite-kernel proof now using the existing relation theorem
directly. The single-element caller and three common-universe callers of eventual
flatness retain their original signatures and add the filtered-ring-colimit proof
import supplying preservation. The base-flat-stage caller already imports it and
requires no adaptation. The packet uses the launcher's 2026-10-14 permission to
correct unclaimed modules. No target, definition or universe parameter changes.

Change records:

- `coord/changes/colimit-flat-relation-preservation.md`
- `coord/changes/FiniteIdealKernelDescent-preservation.md`
- `coord/changes/ColimitMaximalKernelDescent-preservation.md`
- `coord/changes/ColimitEventuallyFlat-preservation.md`

The delivery tool rebases the packet on the current `sheaf-dag`. The worker runs
only `--no-push`; the independent second reader delivers it.

## Proved and sorry left

No new proof of the false original
`RingTheory.exists_stage_flat_relation_factorization` is claimed: 0 of its 1
original holes are proved with the original statement. That declaration is retired,
removing its hole, and the corrected node reuses the already proved
`RingTheory.exists_stage_flat_relation_factorization_of_preserves`. This is a
statement correction and duplicate removal, not a decomposition or a fresh proof
of the existing theorem. No holes are added, no new theorems are introduced and no
statements are split off. There is no `sorry` in any delivered Lean file.

`RingTheory.exists_stage_finite_ideal_kernel_vanishes`,
`RingTheory.exists_stage_maximal_kernel_vanishes` and
`RingTheory.exists_flat_stage` retain complete proofs on their corrected interfaces.
The single-element and three approximation/fibre callers keep complete proofs and
their original signatures. All seven delivered modules compile through
`lcompile.py --all` without errors or warnings (observed times 2.5 to 6.0 seconds).
The dry run with `WEIL_SERVER_COMPILE=1` printed OK after local compilation,
axiom probes, server compilation and preflight on the current `sheaf-dag`
(commit `4cfc2c1cce`); only the independent second reading remains. Nothing was
pushed. A separate check using the landing checker's statement parser found zero
duplicate-statement conflicts in the seven remaining delivered files. A source-wide
scan of the final library overlay found no import of the withdrawn module and no
use of the retired theorem. All four nodes' proof-step uses equal their proof_deps.

## No longer needed

Withdrawn module: `Sheaf.RingTheory.ColimitFlatRelationDescent`. Removed its proof
imports from `IdealKernelElementDescent` and `FiniteIdealKernelDescent`; each directly
imports `Sheaf.RingTheory.ColimitFlatRelationDescentElementwise` instead. Retired
declaration: `RingTheory.exists_stage_flat_relation_factorization`. Its DAG node
is retained and attached to the existing theorem; no DAG node is deleted.

The relation node no longer directly needs
`lem-weil-pbc-flat-equational-criterion`,
`lem-weil-pbc-filtered-colimit-algebras-elementwise`,
`lem-weil-pbc-filtered-colimit-modules-elementwise` or
`lem-weil-pbc-filtered-colimit-rings-zero`. Its direct proof dependency is the
existing proved `lem-weil-pbc-colimit-flat-relation-descent-elementwise`, which
implements that argument. These four underlying nodes are not claimed globally
pruned. No other module is claimed globally pruned. The blueprint unit route stays.

## Where the brief, the DAG or earlier work was wrong

The preceding packet corrected the missing preservation assumption but introduced
a theorem with exactly the statement of the existing elementwise theorem. The
landing's duplicate check correctly rejected it. The repair removes the wrapper,
updates every actual caller and reuses the existing declaration directly.

The original independent-universe categorical-colimit assumption does not ensure
underlying ring representatives or eventual equality. The earlier reviewed V2
valuation-domain counterexample also refutes the old finite-kernel statement:
a nonzero principal-ideal generator tensored with 1 multiplies to zero but remains
nonzero after every transition. Retaining the false declaration with a `sorry`
would be invalid. The corrected interfaces express the algebraic directed colimits
used by Stacks Tags 00HK, 00QX and 00R6. The preservation condition propagates through
the general finite-kernel, maximal-kernel and eventual-flatness interfaces and ends
at the common-universe applications, where Mathlib supplies the instance.

The existing elementwise theorem allows empty finite row and column families,
zero modules and zero ideals. The finite-kernel proof handles an empty finite
subset by retaining the initial index. The preserved proofs add no nonzero or
finite-generation hypothesis. Unit `sk-thm-p1` has no changed realized statement
or proof step, and no target statement or target definition changes.

## Forced adaptations

The seven companion modules were unclaimed in the reviewed packet. The three
interface corrections use the launcher's explicit unclaimed-module permission;
no signature change relies on the exception for another group's held module.

Both original direct callers import the withdrawn module and apply the retired
name. The repair changes those two imports and theorem applications. The
single-element caller additionally retains the proof import
`Mathlib.Algebra.Category.Ring.FilteredColimits` to supply preservation. The
finite-kernel caller needs the explicit preservation binder for its independent
universes. Its original tensor/common-stage proof is otherwise retained.

The original maximal-kernel and eventual-flatness applications fail after the
preservation correction with
`failed to synthesize instance PreservesColimit A (forget CommRingCat)`.
Their corrected interfaces supply that binder and its public import, retaining
the original proof bodies. Three common-universe callers need only the proof
import `Mathlib.Algebra.Category.Ring.FilteredColimits`:

- `Sheaf.RingTheory.FiniteTypeApproximationFlatPoint`, original line 192:
  missing `PreservesColimit Aq (forget CommRingCat)`.
- `Sheaf.RingTheory.IntegerApproximationFlatPointStage`, original line 168:
  missing `PreservesColimit Aₗ (forget CommRingCat)`.
- `Sheaf.RingTheory.NoetherianLocalModelTowerFiberFlatStage`, original line 68:
  missing `PreservesColimit A (forget CommRingCat)`.

The original failures and successful import-only variants were compiled in the
previous reviewed packet. The current seven-file packet was freshly compiled.
`Sheaf.RingTheory.NoetherianLocalModelTowerBaseFlatStage` already imports filtered
ring colimits and compiled unchanged against the corrected dependencies in the
previous reviewed packet; no adaptation is included. Indexing and first-ring
universes coincide in all four applications. The second reader should check the
whole coordinated withdrawal and interface correction together.

## Second reading by N1

Independent second reader, 2026-10-14. I did not write this packet. Verdict: pass
as a coordinated statement correction and duplicate withdrawal, not as a proof
of the false original statement.

1. **Interfaces and visibility.** Diffed all seven delivered modules against the
   repository and read the withdrawn original. The four common-universe callers'
   public theorem signatures are byte for byte unchanged. Each of the three general
   interfaces changes by exactly the recorded
   `[PreservesColimit A (forget CommRingCat.{v})]` binder; universe parameters,
   other hypotheses and conclusions are unchanged. The three public preservation
   imports are needed by their signatures; the four filtered-colimit imports and
   the two elementwise-relation imports are proof-only. No definition or target
   changes. The four open change records cover the withdrawal, interface changes
   and all actual callers. The unclaimed-module exception is explicitly implemented
   in the launcher's `deliver3.py` counterfactual check (2026-10-14); the packet does
   not claim the signature-preserving exception for a module held by another group.

2. **Proof and axioms.** Fresh `lcompile.py --all` compiled the seven delivered files
   without errors or warnings (2.8--6.6 seconds each). Read the finite tensor-map
   construction, single-element balancing argument, common-stage composition,
   maximal-kernel span argument and final local flatness criterion. The approximation
   callers' proof bodies are unchanged. A fresh scratch module printed the axioms of
   all seven delivered public theorems and the existing relation theorem: every
   result uses only `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   The delivered source scan found no `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, `extern` or kernel-check bypass. There is no new definition and
   no witness is chosen from an unproved existence theorem. The original hole is
   retired, not proved: 0 of 1 original holes proved, one hole removed by statement
   correction, zero holes added.

3. **Split statements and small cases.** No new theorem, node or split-off statement
   is introduced. The existing elementwise theorem is applied directly; no duplicate
   wrapper survives. Checked its empty row/column cases and zero-module case in the
   finite-sum argument, and the zero ideal and empty finite subset in kernel descent.
   For the empty subset the common-stage construction takes the initial index, and
   the vanishing assertion is vacuous. Read the earlier V2 universe/valuation-domain
   counterexample: a nonzero coefficient in a domain forces every column coefficient
   to zero, contradicting the row expansion of 1. This justifies retiring the old
   overgeneral categorical interface rather than retaining its false hole.

4. **Shortest route and pruning.** Rechecked the official source:
   [00HK](https://stacks.math.columbia.edu/tag/00HK),
   [00QX](https://stacks.math.columbia.edu/tag/00QX), and
   [00R6](https://stacks.math.columbia.edu/tag/00R6). The explicit ring-colimit
   preservation expresses the algebraic direct limit used there. The repo's local
   Stacks TeX file is absent on this machine, so these were read from the official
   site. Searched with LeanFinder for "Finite algebraic relations over a filtered
   system become trivial after one transition when the limit module is flat" and
   with `rg` for trivial relations, relation factorization and kernel/stage descent
   in Mathlib and both library roots. Results gave equational-flatness tools and the
   existing elementwise implementation, not a shorter exact theorem. A Loogle
   query using the unqualified name `IsTrivialRelation` was inconclusive because
   that identifier was unknown; the LeanFinder signatures and source search supply
   the useful check. Reusing the existing theorem is the shortest route. The report
   names all four former direct proof dependencies and the withdrawn module.
   `sk-thm-p1.json` is untouched; none of the four changed nodes is a realized unit
   statement or step, and the unit's route remains intact.

5. **Nodes and coordinated callers.** For all four nodes, checked that proof-step
   uses equal `proof_deps`, `proof_origin` describes the code, the old statement in
   `statement_change` is verbatim, and the recorded citers are exactly the source-wide
   DAG citer set. All four Lean attachment signatures now match their declarations
   verbatim. The relation node attaches to the already existing proved declaration.
   Fresh scratch copies of the original maximal-kernel and eventual-flatness modules
   fail at lines 101 and 109 with missing `PreservesColimit A`; the original finite-type,
   integer and fibre-flatness callers fail at lines 192, 168 and 68 with the corresponding
   missing preservation instance. Their delivered versions compile. The unchanged
   `NoetherianLocalModelTowerBaseFlatStage` compiled against the corrected overlay
   in 9.3 seconds, confirming it needs no adaptation. A source-wide caller scan found
   no additional theorem use to repair, and no overlay importer of the withdrawn
   module or use of the retired theorem remains.

Second-reading changes: replaced collapsed one-line signatures by verbatim Lean
signatures in the Old/New sections of the three downstream preservation change
records, and in the three corresponding nodes' `lean.statement` fields. Added this
independent review and fresh scratch checks. No Lean proof or interface needed
further editing; no holes were added or split off.
