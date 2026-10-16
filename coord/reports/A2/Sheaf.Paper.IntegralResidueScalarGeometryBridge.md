## What changed

The independent second reader rejected the original new theorem
`integralResidue_tensorGeometry_model_comp`: postcomposing the entire assigned
identity with an invertible model target is an equivalent restatement, not a
strictly smaller obligation. That module, node and change record are withdrawn
from the delivery.

The unchanged statement of
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry_component`
is now reduced to the existing `integralResidue_tensorRoute_model` and two
separate identities. `Sheaf.Paper.IntegralResidueTensorPullCounitModel` normalizes
only the tensor-pull presentation on X, with its coefficient, by its defining
counit. `Sheaf.Paper.IntegralResidueScalarCounitModel` computes the scalar mate
followed by that normalized counit. These statements do not contain the full
original square under another name. Each has its own source, complete proof in
words, explicit constructions in its signature, and matching DAG node.

The bridge's new imports are proof-only. Its two original public imports stay.
No existing statement, definition, visibility, or data construction changes.
The original `hP` binder is retained byte for byte, although this reduction only
uses `hFP`; a declaration-scoped unused-variable linter option accounts for it.

## Proved and sorry left

This is a decomposition, not an axiom-free proof or a net hole reduction.

Closed one of one assigned holes:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorGeometry_component`
(node `new-integral-residue-scalar-geometry-component`). Its module has no sorry.

Added two holes, each exactly `:= by sorry` in a public named theorem:

- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorPullCounit_model`,
  node `new-integral-residue-tensor-pull-counit-model`.
- `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarCounit_model`,
  node `new-integral-residue-scalar-counit-model`.

The source-level change is one hole closed and two added (net minus one).
The existing tensor-route theorem is an upstream open dependency; it is neither
changed nor counted as newly proved. The ledger determines closure-wide counts.
There are no holed definitions and no witnesses chosen from unproved existence.

## No longer needed

Removed direct imports from the bridge:
`Sheaf.Paper.IntegralResidueOrdinaryMonoidal`,
`Sheaf.Paper.IntegralResiduePullSquare`, and
`Sheaf.Paper.IntegralResidueTensorPresentation`.

Of the repository node's old proof_deps, the direct edges to
`new-integral-residue-tensor-presentation`,
`new-integral-residue-derived-pull-square`, and
`new-integral-residue-ordinary-monoidal` are replaced by the explicit normalization
lemmas. Those modules remain transitive dependencies of the normalization lemmas;
no module is claimed pruned from the targets' import closure. The old direct
edges to derived-monoidal and tensor-pull-presentation remain. Added direct
edges are tensor-model, tensor-route-model, and the two new normalization nodes.
No maintainer tool_uses approvals are removed. No unit realization is removed.

The unlanded equivalent-restatement node/module
`new-integral-residue-scalar-geometry-model-comp` /
`Sheaf.Paper.IntegralResidueScalarGeometryModelComp` is not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker called an equivalent postcomposed equality “strictly weaker”.
Cancellation was available under exactly its hypotheses, so this was not a
valid decomposition. The replacement divides the actual argument into a
presentation/counit calculation and a scalar-mate/ordinary-model calculation.

The shared scalar-route theorem already imports this bridge. Using that theorem
here would create a cycle; reversing its proved dependency would merely undo
an earlier reduction. Neither is done. The tensor-route formula is independent
of this bridge and is used directly.

The paper's proof of Lemma 6.5.9(5) gives the pullback/tensor identity on printed
page 51 (the lemma starts on page 50). New docstrings give the precise page and
identify the formal normalization as an explicit calculation, not a separately
stated theorem of the paper. The original statement and its node's source field
are preserved.

## New nodes

`new-integral-residue-tensor-pull-counit-model` records only normalization of
`residueExchangeTensorPullIso` followed by its target model comparison. It has
no scalar pull mate and no derived oplax pullback comparison. Its right side
retains both the exact-pullback and tensor-presentation counits as maps; it does
not assert their invertibility. Its new module is
`Sheaf.Paper.IntegralResidueTensorPullCounitModel`.

`new-integral-residue-scalar-counit-model` records only the scalar mate followed
by the normalized tensor counit and ordinary coefficient identification. It
contains neither `residueExchangeTensorPullIso` nor the model target nor the
derived oplax comparison. Its new module is
`Sheaf.Paper.IntegralResidueScalarCounitModel`.

No change record is required: existing signatures and definitions are unchanged.
The former change record for the rejected unlanded statement is not delivered.

## Second reading by A2

1. Compared all delivered modules against repository sources. The bridge's
   existing declaration signature, including all binders and let instances,
   is byte for byte identical. The other two modules are new. No existing
   definition or dependent module is changed. Verdict: preserved interface.

2. Compiled every delivered module through lcompile.py. Checked the bridge
   and the two lower declarations with #print axioms in a scratch copy: only
   propext, Classical.choice, Quot.sound and sorryAx occur. The latter is
   expected from the two recorded lower holes and upstream open statements.
   Scanned for forbidden declarations/attributes and inspected every inline
   let proof: these are just definitional conversions of constructed maps.
   No definition contains a sorry or uses an arbitrary existential witness.
   Verdict: the reduction is checked; the two lower proofs remain open.

3. Read each new statement independently of the parent. The tensor statement
   concerns just one presentation and its coefficient/counit compatibility.
   The scalar statement concerns the mate followed by the explicit ordinary
   tensor counit. Neither compares the two full original routes. Checked
   identity pullback, degree-zero/zero complexes, and the empty-site case in
   the proof in words: the identities become the corresponding counit/unit
   identities or zero maps. No coefficient flatness or cancellation of a
   noninvertible counit is needed. Actual msearch runs (leanfinder, loogle,
   grep, leansearch) are logged and recorded in each node; direct repo searches
   found the relevant constructions and generic mate/counit APIs, not these
   two normalized identities. The existing scalar-route formula is circular
   here. The existing residueExchangePull_flatModel has extra resolving-class
   hypotheses and computes the scalar pull mate, without the tensor-presentation
   coefficient/model calculation needed here. Verdict: true, necessary, distinct
   parts of the argument.

4. Read the reduction from the top. It first uses the existing tensor-route
   formula, computes the scalar side via the two lower identities, then
   cancels only the target proved invertible by hFP. Proof-only imports stay
   private. The No longer needed list accounts for every removed old direct
   proof dependency, while distinguishing direct edges from global pruning.
   The realized statement and all three steps of sk-thm-properbasechange
   are unchanged; these lower identities bypass no unit realization.
   Verdict: the route is kept and the hole accounting is explicit.

5. Matched each node's Lean statement verbatim, its source, proof steps,
   dependency union, provenance, status and blueprint link. Updated the parent
   proof/proof_deps/proof_origin to the actual cancellation and the three
   formulas used. The new nodes point back through the component and scalar
   route to nt-target-proetale-e; their source explicitly separates the paper
   identity from the formal counit calculation. Verdict: DAG agrees with Lean.

Second reading changed: removed the equivalent restatement and its misleading
report/change record; wrote the real two-part reduction and its lower nodes;
minimized imports; preserved the original signature; corrected provenance and
reported the result as a decomposition with two new holes.
