## What changed

Proved `Algebra.exists_popescu_lift_preparation` in
`Sheaf.RingTheory.PopescuLiftPresentation` from the existing smooth conormal chart theorem
and the new `Algebra.exists_popescu_cleared_conormal_chart`.
The Lean proof constructs the finite polynomial presentation using Mathlib, lifts its relations,
transports smoothness across its quotient equivalence, reindexes the conormal bases,
selects a finite subcover using Noetherianity, and proves the normalized coefficients by
finite-sum simplification. Existing definitions, signatures, and visibility are unchanged.
Added the proof import `Sheaf.RingTheory.PopescuClearConormalChart` and the Mathlib prime
spectrum Noetherian module. Updated the preparation node's proof route and dependencies.
Both modules compile with the prescribed compiler wrapper without errors or warnings.

## Proved and sorry left

Closed: `Algebra.exists_popescu_lift_preparation`
(node `lem-weil-pbc-popescu-lift-preparation`). No sorry remains in the item's module.
Its already proved `Algebra.PopescuLiftPresentation.finitePresentation` is unchanged.

Added and left: `Algebra.exists_popescu_cleared_conormal_chart`
(node `lem-weil-pbc-popescu-clear-conormal-chart`). Its proof is exactly `by sorry` in
its own new module, with the complete Nakayama and denominator-clearing proof in its docstring.
It takes one already chosen chart and selected conormal basis, and only refines that chart;
it neither chooses a polynomial presentation nor makes a global covering assertion.
This is a decomposition (one upper hole closed, one strictly smaller hole added), not a
sorry-free proof or a net reduction in the closure's holes. The existing conormal chart
module is still needed, including the remaining holes in its dependency modules.

Edge cases checked in the argument: empty smooth locus yields an empty finite subcover;
n=0 and m=0 remain valid, including the empty finite sums; E empty is compatible with
Nakayama on I/I_E; no assumption that pi is nonzero or a nonunit is used. The zero ring
and zero localizations are admitted. All witnesses are chosen inside theorem proofs;
no definition chooses data from an unproved existence theorem.

## No longer needed

Removed the item's direct proof import `Mathlib.RingTheory.Finiteness.Nakayama`.
The item's new proof does not directly use node
`lem-weil-pbc-nakayama-one-plus-ideal-annihilator`; its use belongs to the new chart
refinement node. Nakayama is therefore not claimed as globally pruned.
The old direct dependency `def-weil-pbc-smooth-ring-map` is also removed from the
parent node: it remains needed through the chart refinement and the original conormal
chart theorem. This is not a globally pruned node or module.
No Sheaf or WeilConjectures module or unit realization is pruned: the original conormal
chart theorem and all its dependencies remain needed. No unused proof import remains.

## Where the brief, the DAG or earlier work was wrong

No statement correction or forced adaptation was needed. The original node's step (4)
called denominator clearing elementary; its Lean implementation also needs transport of
prescribed bases across the positive-power localization equivalences. The new node records
this residual work explicitly. The main proof refines individual charts before taking a
finite subcover, which is equivalent to the source's order and does not change the unit route.

The local Stacks source file is absent in this clone; the source was read from the official
Tag 07CP and Tag 07C6 pages. The source's replacement by a_k*b_k would kill the quotient
chart if b_k lies in I; the parent node already corrected it to a_k*(a_k^N+b_k), and
this delivery follows that correction. LeanSearch returned Internal Server Error; its
search is recorded as unavailable, alongside successful LeanFinder, Loogle, and grep searches.

## New nodes

`lem-weil-pbc-popescu-clear-conormal-chart`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-popescu-clear-conormal-chart.json`, states
only the refinement of a prescribed chart to exact lifted polynomial relations, with
unchanged selected conormal generators and differential rank. Its source is Stacks 07CP,
preparation (3)--(4), with Nakayama 00DV. Searches found the Nakayama annihilator and
localization ideal-membership ingredients, but no matching result or duplicate blueprint
node. Its one theorem is in `Sheaf.RingTheory.PopescuClearConormalChart`.
No change record is needed because no existing statement, definition, or public import changed.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface: PASS.** Read the full diff against the repository module.
   A byte comparison confirms every existing structure, definition, abbreviation,
   the proved `finitePresentation`, and the main theorem signature are unchanged.
   Only proof imports, a private transport proof, and the main theorem body differ.
   The new module adds a new theorem; there is no existing statement change requiring
   a change record. No target or definition used by a target changes.
2. **Proof and axioms: PASS as a decomposition.** Compiled both delivered modules in
   import order with `lcompile.py --all`; no errors or warnings. Read the proof from
   presentation construction through the finite subcover and coefficient normalization.
   Exactly one delivered sorry remains, in the reported named chart-refinement theorem.
   There are no forbidden declarations or hollow definitions. In a removed scratch copy,
   `#print axioms` for the main theorem and the new residual theorem gave only
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`; `finitePresentation`
   gave the three permitted axioms without `sorryAx`. The main theorem is therefore
   proved relative to open dependencies, not absolutely sorry-free. Choices of chart
   witnesses occur inside a theorem proof, never in a definition.
3. **Residual statement: PASS.** Checked the natural-language proof against
   [Stacks 07CP](https://stacks.math.columbia.edu/tag/07CP) and
   [Nakayama 00DV](https://stacks.math.columbia.edu/tag/00DV). The ideal is finite even
   without Noetherianity; quotienting by the selected relations and localizing gives
   a finite module with IM=M. Clearing the annihilator numerator and then the finite
   relation denominators yields the asserted positive power in the quotient. Canonical
   localization equivalences preserve the specified conormal classes and transport the
   differential basis. Checked empty relations, empty E, no variables, a0=0, the zero
   ring, and pi=0 or a unit; positive exponent 1 can be used when no denominators occur.
   For a0=0 the chart is the zero localization, and a=0 with all coefficients zero works.
   The statement concerns one already supplied chart and is strictly smaller than the
   original global finite-presentation preparation, not a renamed restatement.
   Fresh LeanFinder, Loogle, and grep searches with different wording found Nakayama
   and conormal-spanning ingredients, but no exact refinement theorem. Read
   `LocalizedConormalBasisJacobian`; it only gives ideal membership modulo I squared,
   with another interface and its own sorry. It cannot close this residual in a few
   minutes. Existing smooth-prime transport helpers found by rg are private and cannot
   replace this module's elementary private helper.
4. **Route and pruning: PASS after report correction.** The proof uses Mathlib for
   the polynomial presentation, quotient equivalence, Noetherian finite subcover and
   finite sums; the existing conormal chart theorem supplies the required local data.
   The new residual supplies only the remaining chart-clearing step. Both new imports
   of the item are plain proof imports; every public import is required by its interface
   and is unchanged. The new module's public imports provide notions in its statement.
   Checked `dag/units/sk-thm-p1.json` including `realized`: this refinement is below
   the unit level, and no realized statement or step is bypassed. The pruning section
   now names both old direct proof dependencies removed from the parent node.
   Neither is globally pruned: both remain on the residual proof route. Net holes
   closed minus holes added is zero; this delivery is a decomposition.
5. **DAG consistency: PASS.** Compared the existing node diff: changes are confined
   to `proof`, `proof_deps`, and `proof_origin`, and follow the actual Lean argument.
   Each node's proof dependencies equal the union of its steps' uses. The new node has
   its source, self-contained statement, statement dependencies, proof steps, origin,
   searches, split status, worker/group/item metadata, blueprint provenance, matching
   chapter/unit, and verbatim Lean statement in the new module. The source correction
   a0*(a0^N+b) preserves the quotient open; multiplying merely by b in I would not.

Second reading changed only this report: completed the removed-dependency list and
added the independent checks above. The Lean proof and node records needed no repair.

## Second reading by N3

1. **Interface: PASS.** Independently read the complete Lean diff against this
   repository. All existing declaration signatures and definition bodies are byte
   for byte unchanged. The only edits are private proof support, proof imports,
   and the preparation theorem body. The new chart module introduces no alteration
   of an existing statement. No change record or target re-review is required.
2. **Proof: PASS as a decomposition.** Recompiled both delivered modules in import
   order using `lcompile.py --all`: no errors or warnings. Read the presentation,
   quotient-equivalence transport, chart reindexing, finite subcover, and normalized
   relation proofs. A scratch copy printed axioms for the preparation theorem and
   residual theorem: exactly `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`.
   The unchanged `finitePresentation` uses only the three permitted axioms.
   The sole delivered sorry is the reported named residual theorem; no forbidden
   construct or hollow definition occurs. Witness choices are confined to proofs.
3. **Split statement: PASS.** Independently checked the docstring argument against
   [Stacks 07CP](https://stacks.math.columbia.edu/tag/07CP) and
   [Nakayama 00DV](https://stacks.math.columbia.edu/tag/00DV). The finite ideal quotient
   satisfies IM=M after localization, so the determinant trick applies without
   Noetherianity. The numerator of 1+b/a0^N gives a0*(a0^N+b); after taking a common
   positive power and lifting coefficients the exact relations hold modulo pi squared.
   Its image in the quotient remains a positive power of the original chart element.
   Tested empty relations and E, zero variables, zero ring, a0=0, and pi zero or a unit.
   The statement refines one prescribed chart and is strictly smaller than the parent.
   Fresh LeanFinder and Loogle queries using ideal generators and I modulo I squared,
   plus rg searches of Sheaf, WeilConjectures and Mathlib, found ingredients only.
   Read the newly suggested `Algebra.Generators.exists_presentation_of_free_cotangent`:
   it changes the presentation and adds a relation, so does not preserve this selected
   chart and its generators. `LocalizedConormalBasisJacobian` gives membership only
   modulo I squared. Neither closes the residual in a few minutes. Its proof docstring
   and matching DAG node supply a complete takeover brief.
4. **Route and pruning: PASS.** Mathlib supplies finite presentations, Noetherian
   compactness and finite sums; the existing smooth conormal chart declaration is used
   before the residual chart refinement. All proof-only additions are plain imports.
   Public imports support the interfaces and remain unchanged. Checked the old
   proof dependencies against the new route: the report names both removed direct
   dependencies, neither of which is globally pruned. Read `sk-thm-p1.json`, including
   its `realized` entries: no unit statement or step is bypassed. One hole closed and
   one added gives net zero, recorded as decomposition, with no module pruned.
5. **Nodes: PASS.** The existing-node diff changes exactly `proof`, `proof_deps`, and
   `proof_origin`, following the compiled proof. Verified both dependency lists equal
   the union of their step uses. Verified the new node's Lean signature matches the
   source verbatim and its source, searches, creation metadata, split status,
   blueprint provenance, statement dependencies, chapter and unit are present.

Second reading changed only this report, adding the independent checks above.
The Lean proof and node records needed no repair. The scratch axiom probe was removed
before delivery.
