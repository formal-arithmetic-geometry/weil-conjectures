## What changed

Replaced the sole sorry in `FiniteFlatDiscriminantBranchSupport.lean` by a proof from
`FiniteFlatTraceDiscriminantGluing.lean` and `TraceDiscriminantFibreEtaleCriterion.lean`,
imported privately for the proof. The first provides the glued ideal and a finite free
chart at every point. The main proof derives local principality from the explicit
principal ideal formula. Mathlib's `IdealSheafData.mem_support_iff_of_mem` and
`Scheme.zeroLocus_span` reduce support membership to the local determinant criterion.
The existing statement and all existing definitions and visibility are unchanged.
The node now records this two-part proof.

Read Stacks Project Tag 0BVH, the construction preceding Lemma 49.3.1 and its proof.
The new statements separate construction/gluing from detection of non-etale fibres.
Neither new statement is a renamed version of the original: the construction theorem
has no etaleness conclusion, and the criterion has no ideal-sheaf existence conclusion.
No object is defined by choosing an arbitrary witness from an unproved theorem.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.exists_locallyPrincipal_branch_ideal_of_finite_flat`
(node `lem-sbc-finite-flat-discriminant-branch-support`) by a compiling reduction.
There are no sorries left in the item module. This is a decomposition, not a completed
proof of the underlying discriminant theory: one hole closed, two holes added (net -1).

The two new sorries, each the entire proof of a named public theorem, are:

- `AlgebraicGeometry.Scheme.exists_ideal_locally_eq_trace_discriminant_of_finite_flat`
  (`lem-sbc-finite-flat-trace-discriminant-gluing`).
- `AlgebraicGeometry.Scheme.trace_discriminant_zeroLocus_iff_nonEtale_fibre`
  (`lem-sbc-trace-discriminant-fibre-etale-criterion`).

Each has its source, full natural-language proof and DAG node. The local rank-zero
case has determinant one and empty fibre; both sides of the criterion are false.
An identically zero determinant is permitted (for instance a nonreduced finite
algebra over a field), as required by the original statement. Variable rank is handled
by separate charts; the empty target makes the pointwise conclusions vacuous. No
surjectivity, integrality, reducedness, or generic etaleness has been assumed.

## No longer needed

None of the original imports, nodes or modules are pruned. The original node had no
proof dependencies to discard. Both added proof imports are used. The new gluing module
imports ideal-sheaf basics rather than invertible ideals and does not import etaleness;
the new fibre-criterion module does not import the ideal-sheaf invertibility theory.
No unit step or chapter route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node had one non-elementary paragraph with no proof dependencies. Thus there were
no existing named planned declarations to combine. This delivery splits that paragraph
at its construction/criterion boundary and supplies the Lean composition.
LeanFinder and Loogle returned discriminant and etale-locus tools, but no exact
scheme-level result. LeanSearch returned Internal Server Error, recorded as unavailable.
Blueprint searches for `trace discriminant` and `discriminant` found no matching node.
The inherited blueprint ancestor is retained because the ancestor tool returns None
for the already-created item. No mathematical error in the original statement found.

## New nodes

`lem-sbc-finite-flat-trace-discriminant-gluing`, in
`FiniteFlatTraceDiscriminantGluing.lean`: construction of a quasi-coherent ideal whose
local generators are trace determinants on finite free affine charts. This is precisely
the construction portion of Stacks Tag 0BVH and makes no branch-locus assertion.

`lem-sbc-trace-discriminant-fibre-etale-criterion`, in
`TraceDiscriminantFibreEtaleCriterion.lean`: the pointwise local trace determinant
criterion from the proof of Stacks Tag 0BVH, Lemma 49.3.1. This theorem requires an
already-given chart and basis and constructs no global ideal.

No change record is necessary: no existing interface changed.

## Second reading by F2

1. **Interface preservation — PASS.** Diffed the delivered item against the repository:
   the only Lean changes are two private proof imports and the replacement of `by sorry`.
   The existing theorem signature, docstring, visibility and public imports are byte for
   byte unchanged. The other two modules are new and contain only public named theorems;
   there are no definitions or interface changes requiring a change record. Comparing
   the original node JSON found changes only in `proof`, `proof_deps`, `proof_origin`.
2. **Proof and axioms — PASS as a decomposition.** Independently compiled all three
   modules in import order using lcompile.py, without errors or warnings. Compiled
   scratch copies with explicit `#print axioms` for all three declarations: each uses
   only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` from
   the two reported open theorems. The item itself has no sorry; each new module has
   one whole named public theorem proof `by sorry`. No forbidden construct or hollow
   definition occurs. The existential elimination in the proof stays within Prop;
   no data definition chooses an arbitrary witness from an open existence theorem.
3. **Split statements — PASS.** Read the construction and Lemma 49.3.1 at
   https://stacks.math.columbia.edu/tag/0BVH and both full docstring proofs. The gluing
   theorem supplies charts and a discriminant ideal without an etaleness conclusion;
   the criterion supplies pointwise etaleness detection on a given free chart without
   constructing an ideal. Neither restates the item. Checked rank zero/empty source
   (unit determinant, empty branch support), empty target (vacuous assertions), an
   identity morphism (unit determinant), dual numbers over a field (zero determinant,
   non-etale fibre), and variable rank on disconnected targets. The algebra structure
   in both statements is explicitly induced by f. New independent searches used
   LeanFinder for compatibility of local basis trace determinants with affine
   restriction, Loogle for `Algebra.traceForm`, and grep for base change, units and
   nondegeneracy. Also searched lean/Sheaf and lean/WeilConjectures with `discriminant`
   and exact `discr`, `traceForm`, `traceMatrix` terms. Found ideal restriction tools,
   field-extension trace nondegeneracy and basis discriminant lemmas, but no existing
   scheme-level gluing theorem or pointwise criterion to replace either hole. These
   remaining arguments cannot be closed by a short application of those results.
4. **Route and pruning — PASS.** Read the Lean reduction from its top down: local
   principality follows immediately from the singleton span, and support membership
   follows by the affine support lemma and zeroLocus_span before applying the fibre
   criterion. Both private proof imports are used; every public import of each new
   module supports its statement. Original proof_deps were empty, so `No longer needed`
   is complete. Read sk-prop-input-spreading.json and its realized field (empty statement
   and step lists); the unchanged original node remains on the existing unit route.
   This only subdivides its below-unit discriminant argument, bypassing no unit step.
5. **Nodes — PASS.** Checked all three recorded Lean signatures verbatim against the
   declarations. The item's two proof steps and dependency union match its Lean proof.
   Both new nodes have sources, non-elementary proof paragraphs, search records,
   creation/item/group/date, blueprint ancestry, chapter/unit and complete Lean records.
   Their empty proof_deps reflect that their source arguments remain unsplit holes,
   rather than claims of completed elementary proofs.

Second reading changed only this report, adding the independent checks and verdicts.
No Lean repair was needed. One original hole is closed and two strictly simpler holes
are added: this remains a decomposition with net holes closed minus added of -1, not
an axiom-free proof of the discriminant result. No module or node is pruned.
