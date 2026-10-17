## What changed

Repaired the returned delivery against the current upstream-synchronized library.
`Sheaf.RingTheory.PopescuLiftPartialChart` now restores the original
`Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension` and
`Algebra.PopescuLiftPresentation.partial_chart_flat`, with their original signatures
and complete proofs. Its proof-only `import all` now names
`WeilConjectures.RingTheory.SmoothAtPrimeDifferentialsDimension` directly.

`Sheaf.RingTheory.PopescuLiftChartFlat` proves the unchanged
`Algebra.popescu_lift_chart_flat` directly: pull back the prime and chart coefficient,
apply the restored partial-chart flatness, base change the annihilator equality,
apply `chart_comparison_bijective`, localize the base, and compose the flat local maps.
The two new helper modules from the returned delivery are unnecessary and are omitted;
there are no new modules or nodes. Updated both existing DAG nodes to the actual proofs
and restored the partial-chart node's Lean attachment.

Change record: `coord/changes/popescu-lift-partial-chart-upstream-import.md`.

Both delivered files compiled in dependency order. Explicit `#print axioms` checks
for the item and both restored theorems returned only `propext`, `Classical.choice`
and `Quot.sound`. The original, unchanged
`PopescuLiftChartComparison` and `PopescuLiftSmoothSpecial` sources also compiled
against the changed dependencies. The original restored dimension proof with the old
import was compiled separately and reproduced the reported missing `FormallyEtale`
and differential-base-change identifiers. Source checked: Stacks Tag 07CP, especially
the partial chart's equation count and polynomial fibre description, followed by
the final annihilator comparison. The existing sk-thm-p1 unit route is retained.

Repair retry validation on 2026-10-17: compared the retained source delta with the
current shared source after the e47efb5a5 sync. Recompiled both delivered modules,
the unchanged comparison and smooth-special consumers, and an explicit three-theorem
axiom audit against the live published build. All passed; the audit again listed
only propext, Classical.choice and Quot.sound. The substantive import repair and
restoration above are retained; this is not a rebase-only delivery.

## Proved and sorry left

Closed the one original hole: `Algebra.popescu_lift_chart_flat`
(`lem-weil-pbc-popescu-lift-chart-flat`). Added zero holes. Left zero holes in either
delivered module. Also restored the complete, sorry-free original proofs of
`Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension` and
`Algebra.PopescuLiftPresentation.partial_chart_flat`
(`lem-weil-pbc-popescu-lift-partial-chart-dimension`). Nothing is split off.

## No longer needed

The returned delivery's `Sheaf.RingTheory.PopescuLiftChartPartialFlat` and
`Sheaf.RingTheory.PopescuLiftChartMapsFlat`, and their nodes
`lem-weil-pbc-popescu-lift-chart-partial-flat-repair` and
`lem-weil-pbc-popescu-lift-chart-maps-flat`, are omitted. The first duplicates the
restored original corollary; the second only separates proof steps now done inline.
They are already absent on current sheaf-dag, so no withdrawal file is needed.

Removed the proof-only import of the retired
`Sheaf.RingTheory.SmoothAtPrimeDifferentialsDimension` wrapper and replaced it with
the actual upstream module. The item keeps the original annihilator and comparison
imports and explicitly imports the restored partial-chart API. No existing module or
node is claimed to leave the target import closure: pruning against current main is
none. The equation-count, fibre-dimension, annihilator, comparison and base-localization
lemmas remain needed.

## Where the brief, the DAG or earlier work was wrong

The sandbox initially contained only launcher metadata, so the returned delivery was
recovered from its recorded landing. Its earlier report said the fibre-dimension theorem
was available, but the current upstream-sync source has both that theorem and the
partial-flatness corollary commented out. Restoring only a corollary under a fresh name
cannot repair this failure. The cause is a module-system import boundary: the retired
Sheaf wrapper does not expose the proof-only dependencies of the upstream dimension
module. A direct `import all` of that upstream module fixes the original proof,
including its private dimension-preservation lemma. No mathematical statement changes.

The edge cases are unchanged: the zero ring has no relevant prime; if pi is a unit
the prime-containment hypothesis is impossible; pi=0 needs no cancellation; empty
E_k and m=0 are handled by the existing polynomial equivalences and cardinal identities.
No arbitrary data are chosen from an unproved existence theorem.


## Earlier second reading (a previous round; superseded)

1. **Visible interface: pass.** Read both complete delivered modules and diffed each
   against the shared repository. Every existing active declaration keeps its exact
   signature, visibility and definition body. The item's only original hole is replaced
   by a proof. In `PopescuLiftPartialChart`, the only changes are the direct proof-only
   upstream `import all` and removal of the two take-out comment wrappers; the restored
   theorem signatures and proof bodies are the originals. The change record declares
   this restoration. No target, algebra construction or scalar structure is changed.

2. **Proof and trust: pass.** Compiled both delivered modules with `lcompile.py` in
   dependency order. Independently appended `#print axioms` to scratch copies for
   `Algebra.popescu_lift_chart_flat`,
   `Algebra.PopescuLiftPresentation.partial_chart_fibre_dimension` and
   `Algebra.PopescuLiftPresentation.partial_chart_flat`: each reports exactly `propext`,
   `Classical.choice`, `Quot.sound`. Both delivered files contain zero holes and no
   forbidden declarations. The chart quotient, its maps and polynomial equivalences
   are actual constructions; no unproved existence supplies arbitrary data.

3. **Split statements: pass, none.** There are no new nodes or statements left with
   `sorry`. The two restored theorems are fully proved, not surrogate assumptions for
   the item. Checked the cases pi=0, empty E_k and m=0: the proof uses no cancellation
   of pi, and its rank identity is `Nat.sub_add_cancel (hd.card_le k)`. A zero ring has
   no chosen prime, and a unit pi cannot lie in the pulled-back special-fibre prime.
   For r=0 there is no k. No case is silently excluded by a new hypothesis.

4. **Route and pruning: pass.** Read Stacks Tag 07CP, especially the partial-chart
   presentation, polynomial special fibre and final local kernel argument, and checked
   the Lean hypotheses at each application. `polynomial_value` uses exactly hc and
   scalar compatibility to transfer chart nonmembership. The residue field kills pi
   because its contraction contains pi; the prepared differential basis gives fibre
   dimension n. Equation-count flatness supplies the hypothesis for both annihilator
   base changes. The resulting equality is exactly what the existing
   `chart_comparison_bijective` requires. Base localization and composition identify
   the canonical local map in the unchanged conclusion. Read that comparison helper,
   `exists_flat_away_of_fibre_dimension_eq`, the annihilator-base-change theorem and
   the upstream differential-dimension theorem. A fresh LeanFinder search returned
   generic `RingHom.Flat.localRingHom` and localization results; the former assumes
   flatness of the unlocalized chart map, whereas here only its target localization
   has been proved flat, so it does not replace the calculation. Source searches found
   no existing prepared-chart flatness theorem that bypasses these steps. All public
   imports supply signature vocabulary. The explicit proof import of the repaired
   partial-chart API also keeps the two-file local compilation in dependency order.
   A scratch removal test confirmed that `Mathlib.RingTheory.Kaehler.TensorProduct`
   is needed for `tensorKaehlerEquiv`. The retired wrapper import is removed as reported.
   No old proof dependency is omitted, and pruning against the current library is none.
   Read `dag/units/sk-thm-p1.json`: its statement and every `realized` step are retained;
   these repairs are below the unit route.

5. **DAG: pass.** Checked both delivered JSON records against the sources and Lean.
   Only permitted stage-3 fields differ: `proof`, `proof_origin`, and, for the repaired
   partial-chart node, `proof_deps` and its restored `lean` attachment. In both nodes
   `proof_deps` is exactly the union of the steps' `uses`. The main proof records
   polynomial extensionality, partial-chart flatness, annihilator base change,
   bijective comparison and localized-base composition in their actual order. The
   dependency node records differential rank and open-embedding dimension invariance,
   then the restored equation-count corollary. Its attachment names both restored
   declarations. No new split or claimed net progress is concealed in the records.

Second reading changes: added this independent review. No Lean or DAG repair was
needed; the delivered proofs and dependency restoration are retained. One original
hole is closed, zero holes added, zero split off; the two restored theorems remain
sorry-free. Independently compiled the unchanged `PopescuLiftChartComparison` and
`PopescuLiftSmoothSpecial` sources against the restored API; both passed without warnings.

## Second reading by R4

1. **Visible interface: pass.** I diffed both delivered Lean modules against the
shared repository. The target theorem signature is byte-for-byte unchanged. The
partial-chart theorem signatures are the original signatures restored from the
upstream-sync comments; the import repair and restoration are declared by
`coord/changes/popescu-lift-partial-chart-upstream-import.md`. No target, definition,
hypothesis, conclusion, or visibility was weakened or changed.

2. **Proof and trust: pass.** I compiled `PopescuLiftPartialChart` and
`PopescuLiftChartFlat` with `lcompile.py --all`, then compiled the unchanged
`PopescuLiftChartComparison` and `PopescuLiftSmoothSpecial` consumers. An explicit
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound` for
`partial_chart_fibre_dimension`, `partial_chart_flat`, and
`popescu_lift_chart_flat`. There are no `sorry`s, forbidden declarations, or hollow
definitions. The chart and localization objects are explicit constructions.

3. **Split statements: pass, none.** No new statement or node is introduced and no
`sorry` remains. The restored partial-chart declarations are complete proofs, not
surrogate assumptions. The proof handles the zero, empty-equation, and empty-chart
cases through the existing finite-cardinality and polynomial identities; no extra
hypothesis is introduced.

4. **Route and pruning: pass.** The target proof follows the retained `sk-thm-p1`
route: polynomial evaluation, restored partial-chart flatness, flat annihilator base
change at `π` and `π²`, the existing chart comparison bijection, and localization of
the base followed by composition. The partial-chart proof retains its explicit
equation-count and differential-dimension route. The direct proof-only import of the
upstream `SmoothAtPrimeDifferentialsDimension` module is necessary to expose the
proof dependencies used by the restored proof; the retired Sheaf wrapper import is
removed. No old proof dependency is unused and no reachable module is pruned.

5. **DAG: pass.** I checked both node records against the Lean declarations. Their
`proof`, `proof_deps`, and `proof_origin` describe the actual proof order; the
partial-chart node records both restored declarations and the repaired import. No
statement or `stmt_deps` field changes, no new node is added, and the unit's
`realized` route remains intact.

I changed only the report by adding this second-reading record; no further Lean or
DAG repair was needed.
