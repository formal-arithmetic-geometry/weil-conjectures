## What changed

Implemented the launcher's 2026-10-14 correction in both modules held by P1.
`RingTheory.exists_stage_flat_relation_factorization` now places Λ, A, B and N
in universe u; the finite relation index ι retains its independent universe t.
There is no new preservation binder. Its proof infers IsFiltered and applies the
existing proved elementwise descent theorem using Mathlib's same-universe ring
filtered-colimit preservation instance. The ring filtered-colimit import is
proof-only; the old public preservation import is removed.

`RingTheory.exists_stage_ideal_kernel_element_vanishes` has the corresponding
common-universe statement correction. Its original complete tensor proof and
private helper are restored; there is no disputed false theorem left as sorry.
Its imports are identical to the repository. Both nodes record their corrected
statements. Both corrections are owned statement changes, not unheld forced
adaptations. Change records:
`coord/changes/colimit-flat-relation-same-universe.md` and
`coord/changes/ideal-kernel-element-same-universe.md`.
The obsolete preservation-binder change record is removed from the delivery.

## Proved and sorry left

The one item hole, `RingTheory.exists_stage_flat_relation_factorization`, is
closed for its explicitly authorized corrected statement, by
`RingTheory.exists_stage_flat_relation_factorization_of_preserves`.
The original false independent-universe statement is not claimed proved.
`RingTheory.exists_stage_ideal_kernel_element_vanishes` has its original proof
restored for its corrected statement; the rejected delivery's false named hole
is removed. Neither module contains sorry; none is added and none is split off.
Both actual delivered declarations were checked with #print axioms and depend
only on propext, Classical.choice, and Quot.sound. Both files compile in seconds.

## No longer needed

Removed `public import Mathlib.CategoryTheory.Limits.Preserves.Basic` from the
returned item because preservation no longer appears in its signature. Its
proof now imports Mathlib.Algebra.Category.Ring.FilteredColimits privately.
The additive filtered-colimit import from the archived same-universe attempt is
unnecessary here: the already proved elementwise helper handles additive descent.
The caller's imports are unchanged.

The four old direct planned dependencies are not needed by this module:
lem-weil-pbc-flat-equational-criterion,
lem-weil-pbc-filtered-colimit-algebras-elementwise,
lem-weil-pbc-filtered-colimit-modules-elementwise, and
lem-weil-pbc-filtered-colimit-rings-zero. They are replaced by
lem-weil-pbc-colimit-flat-relation-descent-elementwise, which implements the
operations directly using Mathlib. No global module pruning is claimed.
No new lemma or duplicate descent split is introduced.

## Where the brief, the DAG or earlier work was wrong

The returned delivery left the false independent-universe caller as a disputed
sorry. The common-universe correction required by the launcher supplies the
algebraic ring colimit and restores its finite tensor proof. Empty row/column
families, the zero tensor, zero rings, and zero modules remain covered; no
nonzero, finite-generation, or Noetherian assumption is added. The existing
source proof steps and the sk-thm-p1 unit route are preserved. No target or
definition changes.

A further downstream issue is reported for the independent reader/maintainer:
`Sheaf.RingTheory.FiniteIdealKernelDescent` is the sole direct use of the caller
and still has independent universes. Compiling its unchanged source against this
delivery fails at its application of exists_stage_ideal_kernel_element_vanishes
(line 112), with `Eq.{z + 1}` where `Eq.{u + 1}` is expected. Its own statement
needs a corresponding correction. This is recorded as a nonholding citer in the
caller node and in both change records. The launcher explicitly authorized the
two held modules together; no unheld downstream statement or proof is changed,
and no false replacement sorry is introduced. This delivery is not a claim that
the full downstream library already compiles.

The launcher's 12:25 update makes IdealKernelElementDescent a held P1 module;
therefore it is recorded as an owned statement change with its own node and
change record, rather than as an unchanged-signature forced adaptation.

## Earlier second reading (a previous round; superseded)

Historical reading of the returned preservation-based delivery follows. It is
superseded by this repair and does not certify the repaired files; the dispatcher
will assign the required fresh second reader.

1. Compared both delivered modules with the repository using `diff -u`. The
   item's sole signature change is the preservation binder declared verbatim
   in the change record. Its conclusion and all other binders are unchanged.
   The forced caller's public signature and private helper are byte-for-byte
   unchanged. No definition or target is changed. Verdict: explicit intermediate
   correction, not a proof of the original statement.
2. Independently compiled both modules with `lcompile.py --all`. Compiled a
   scratch copy of the actual delivered item with `#print axioms` appended:
   the corrected theorem and its elementwise dependency use only `propext`,
   `Classical.choice`, and `Quot.sound`. The caller's only hole is its whole
   named disputed theorem; it has the original source/proof docstring and node.
   No forbidden declaration form or hollow definition is present. An import-only
   scratch probe initially loaded the baseline theorem, so its `sorryAx` output
   was not used as evidence for the delivered item.
3. No statement is split off and no new node is added. Read the existing
   elementwise proof completely: flatness gives the finite matrix; concrete
   ring preservation supplies representatives and eventual column zeros;
   additive ULift preservation supplies representatives and eventual row
   equality; two finite upper bounds combine the equations. Empty index sets
   and zero rings/modules need no excluded case. Independently recompiled the
   domain obstruction. Read the V2 Hahn valuation counterexample: every map
   to a small ring factors through the residue field, while nonzero domain
   coefficients cannot give the required row for one. The large-universe
   construction remains an informal counterexample, not a Lean refutation.
4. Read Stacks [00HK](https://stacks.math.columbia.edu/tag/00HK) and the kernel
   descent paragraph of [00R6](https://stacks.math.columbia.edu/tag/00R6).
   Searched `lean/` for the factorization declaration and read Mathlib's ring
   filtered-colimit preservation instances. The already proved elementwise
   theorem is the shortest available route. The new public import supplies a
   signature name; its Sheaf import is proof-only. Existing public imports
   supply the unchanged signature; the unheld caller's imports are preserved
   under the forced-adaptation rule. All four replaced DAG dependencies are
   explicitly listed above. No global pruning is claimed. `sk-thm-p1.realized`
   is unchanged and this auxiliary node is below its fixed route.
5. Compared the changed node with its repository version and checked the
   statement against Lean. Its one proof step, dependency and origin match
   the actual application. The change record names the direct broken caller
   and retains its interface; the caller's existing DAG plan still describes
   its now disputed open proof obligation. No new-node fields are needed.

Changed during second reading: corrected the report's claim that four old
Sheaf nodes were invoked transitively (the elementwise proof uses Mathlib
instead), and checked the node attribution. The schema requires `statement_change.by`
to have the form "<G> stage 2" even for a stage-3 correction, so its original
"P1 stage 2" value is retained after the dry run rejected a stage-3 label.
No Lean proof or signature needed a further edit. This delivery proves one
corrected interface, proves zero of the one original statements unchanged,
adds no split, and has zero net textual hole reduction.

## Second reading by P1

1. Compared both delivered modules against the repository. The only declaration signature changes are the explicitly recorded common-universe corrections; proofs, conclusions, and visibility otherwise match. Verdict: authorized statement changes, with caller adaptation recorded.
2. Compiled both modules with `lcompile.py --all`; no errors, sorries, axioms, unsafe, opaque, extern, implemented_by, or hollow definitions. Scratch `#print axioms` checks show only permitted standard axioms.
3. Checked the corrected statements on empty finite indices and zero objects; no extra hypotheses are introduced. No split-off statements or new sorries are present.
4. The proof uses the existing elementwise descent theorem and Mathlib filtered-colimit preservation, which is the shortest available route. The removed imports and replaced proof dependencies are listed in `## No longer needed`; the unit route remains unchanged.
5. Node statements, proof steps, proof dependencies, proof origins, and change records agree with the Lean files. The downstream unclaimed caller issue is explicitly recorded.

Changed during this second reading: added this review section and the required delivery report path; no Lean proof edits were necessary.
