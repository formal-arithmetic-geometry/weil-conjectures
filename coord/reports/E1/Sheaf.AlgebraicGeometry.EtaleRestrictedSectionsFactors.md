## What changed

Proved `AlgebraicGeometry.Etale.etaleRestrictedSections_factors` directly, retaining its
existing signature and docstring. The proof factors each diagonal coprojection through
the degreewise second filtration, assembles these factors using `totalDesc`, and cancels
the monic step inclusions to obtain a chain map. Precomposition with the canonical
finite-diagonal comparison gives the stated sections factorization.

Removed the redundant direct public import of
`Mathlib.CategoryTheory.Subobject.FactorThru`: the retained construction import already
exports its declarations. No definitions or existing statements changed. The import change is recorded in
`coord/changes/EtaleRestrictedSectionsFactorsImports.md`, including all 238 downstream
users and the retained all-public path that preserves their exports.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Etale.etaleRestrictedSections_factors`
(node `lem-weil-pbc-etale-restricted-sections-factors`).

Added zero holes. No `sorry` remains in the delivered module. Removed the first worker's
proposed `AlgebraicGeometry.Etale.etaleRestrictedMappedInclusion_factors` and its new node;
the concrete mapped-total factorization is now proved inside the original theorem.
This is a proof, not a decomposition: one hole closed, none added.

A scratch copy compiled against the shared compiled library without the sandbox overlay.
`#print axioms AlgebraicGeometry.Etale.etaleRestrictedSections_factors` returned exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

Removed direct import `Mathlib.CategoryTheory.Subobject.FactorThru`, which is already
transitively public through `Sheaf.AlgebraicGeometry.EtaleRestrictedTotalConstruction`.
No old proof-dependency node is pruned: the only original dependency,
`def-weil-pbc-etale-restricted-total-construction`, is still used and imported.
No library module becomes unreachable through this redundant import removal.

The proposed new node `lem-weil-pbc-etale-restricted-mapped-inclusion-factors` is not
needed and is not delivered. Identical sandbox copies of dependency source files were
removed from the delivery set; none had changes.

## Where the brief, the DAG or earlier work was wrong

The first worker's reduction compiled but left essentially the original diagonal-image
argument as a new hole, with an incomplete docstring proof and incomplete new-node
search metadata. That hole is unnecessary: the existing totalization and subobject
APIs prove the full factorization. The final node records the concrete proof instead.

The inherited unit attachment is `sk-prop-h2` (the Kummer H² unit). Its `realized`
statement and step lists are empty, and this node is not a realized unit step in any
unit record. This proof changes no unit record or unit route; it discharges the same
restricted-total auxiliary statement using its original construction dependency.

## Second reading by E1

1. Compared every sandbox Lean source with the repository using byte comparison and
   `diff`. All dependency copies were identical and excluded. The sole existing theorem
   signature and its docstring are byte for byte unchanged; there are no changed
   definitions, extra hypotheses, or weakened conclusions. The redundant public-import
   removal has its required import change record.
   Verdict: pass.
2. Compiled the final module, including a separate scratch copy against the shared
   library without `.lbuild`. Both compile cleanly. The module has no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`. The explicit axiom print contains
   only the three permitted axioms. Every chosen factor is a factor through a monic
   inclusion with a proved factorization property, so its value is uniquely determined.
   Verdict: pass.
3. Inspected the proposed mapped-total split and searched by chain-map lifting and
   diagonal-factorization terminology using recorded LeanFinder, Loogle, and Mathlib
   grep searches, plus `rg` over the local library. Existing generic total and subobject
   lemmas suffice; there is no new public statement or split-off hole in the final set.
   Checked arbitrary negative q, n<q (empty filtration interval), r<0, and s<q: the last
   two give zero source summands, and every remaining summand has q≤s≤n.
   Verdict: pass after removing the proposed split.
4. The final proof follows the original plan from the target downward, uses existing
   Mathlib coprojection/image/factorization lemmas, and keeps the original construction
   dependency. Removed the redundant direct import and listed all pruned dependencies
   (none). Checked the unit's `realized` record and searched all unit records for this
   node/module; no realized step or unit route is bypassed. Verdict: pass.
5. Compared the final node with the Lean proof: `proof` describes vanishing summands,
   the finite supremum inequality, totalDesc, monic cancellation, and the final inverse
   comparison; `proof_deps` is exactly the union of its step's uses and retains the
   original construction node; `proof_origin` records the second reader's direct proof.
   No new nodes remain. Verdict: pass.

Second reading changed: closed the proposed mapped-total hole inside the original
proof, removed its declaration and node, removed one redundant import and unchanged
dependency copies, corrected the DAG proof and the report's hole accounting.

## Import change record

`coord/changes/EtaleRestrictedSectionsFactorsImports.md` records only redundant
public-import pruning; every existing declaration signature and definition is unchanged.
The first dry run requested this record; it is now included.
