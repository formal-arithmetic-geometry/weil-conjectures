## What changed

Replaced the sorry in `AlgebraicGeometry.smoothProper_dualizing_tensor_evaluation`
with a complete Lean composition of two strictly smaller statements. The proof constructs
Noetherian instances for X and the fibre product, uses standard derived localizations only
for the auxiliary fibre product and its opens, and chooses a diagonal right adjoint from
`noetherian_schemeDerivedDirectImage_has_rightAdjoint`. A proved private helper
`qc_single` places the single structure sheaf in the quasi-coherent full subcategory.
The smooth diagonal theorem supplies the perfectness hypothesis. The final line tensors
the inverse determinant isomorphism with the identity and composes with evaluation.
The original statement, including its independent derived universes and specified
functor, comparison, adjunction and structure object, is unchanged.

Added `PerfectDiagonalDualizingEvaluation` and `SmoothDiagonalDualizingDeterminant`,
one public theorem per module, each with its source, proof in words and node. Updated
the original node's proof, proof_deps and proof_origin to match the reduction.

## Proved and sorry left

Closed the original body hole in
`AlgebraicGeometry.smoothProper_dualizing_tensor_evaluation`
(node `lem-sc-smooth-proper-dualizing-tensor-evaluation`). No sorry remains in the item module.
The private helper `qc_single` is proved without holes.

Two new holes remain:

- `AlgebraicGeometry.perfectDiagonal_dualizing_evaluation`, node
  `lem-sc-perfect-diagonal-dualizing-evaluation`: the first three equalities of Tag 0BRT,
  under flatness and a perfect diagonal; no smoothness or determinant occurs here.
- `AlgebraicGeometry.smoothDiagonal_dualizing_determinant`, node
  `lem-sc-smooth-diagonal-dualizing-determinant`: the diagonal right adjoint's value on
  the structure sheaf, using Koszul duality and constant rank; no right adjoint of f
  or tensor evaluation occurs here.

This is a decomposition, not a sorry-free proof of the mathematical theorem: one upper
hole is replaced by two lower holes, net +1. The parent combines their different
conclusions by a checked tensor isomorphism and constructs all their additional data.
Existing imported declarations with sorry are unchanged and remain downstream work.

## No longer needed

Removed these direct proof imports from the repository version of the item module:

- `Sheaf.AlgebraicGeometry.DiagonalConormalDifferentials`
- `Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure`
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing`
- `Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula`

The removed direct proof dependency nodes are:

- `lem-sc-smooth-proper-diagonal-conormal-differentials`
- `lem-sc-smooth-proper-diagonal-pushforward-structure`
- `lem-sc-smooth-proper-diagonal-koszul-dual`
- `lem-sc-smooth-proper-diagonal-tensor-formula`
- `lem-sc-smooth-omega-finite-locally-free`

The finite-locally-free theorem is supplied by the existing public import
`WeilConjectures.AlgebraicGeometry.Modules.Differentials` in the determinant module.
The redundant added proof import `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
was also removed during second reading; this module is already publicly imported by
that differentials module. It was not an import of the repository version.

Their corresponding nodes are now dependencies of the appropriate new intermediate node;
they are still needed transitively. No mathematical branch or module is globally pruned.
The conormal, Koszul-dual and finite-locally-free steps are retained in the determinant
intermediate; the counit and perfect tensor formula are retained in the evaluation
intermediate. The unit `sk-thm-picard-duality` route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The old node's last step compresses substantial glue:
extracting an isomorphism from the tensor-formula mate, comparing chosen right adjoints,
transporting across derived universes, and normalizing the rank-stratified complex.
The two new statements isolate that work rather than treating it as a one-line rewrite.

The local Stacks source files are absent in this checkout. The source was read at the
primary URLs [Tag 0BRT](https://stacks.math.columbia.edu/tag/0BRT),
[Tag 0BR0](https://stacks.math.columbia.edu/tag/0BR0), and
[Tag 0E2Q](https://stacks.math.columbia.edu/tag/0E2Q). The displayed evaluation chain
splits exactly at c(O_P), before determinant cancellation.

Edge cases checked mathematically: empty X, relative dimension zero (e.g. a finite etale
map), and the identity morphism. The determinant statement gives the structure object
in degree zero for d=0. Flatness alone does not imply the diagonal is perfect, so the
evaluation lemma explicitly requires the perfect single pushforward complex. This
hypothesis is supplied by the existing smooth-diagonal theorem in the parent proof.
Both intermediate statements preserve arbitrary choices of adjoints and structure
objects. The determinant lemma permits different X/P derived universes; evaluation
permits different X/S/P universes.

LeanFinder and Loogle returned only ordinary sheaf adjunctions and general adjoint
uniqueness, not either needed result. Mathlib grep found no match. LeanSearch returned
HTTP 500 for both new statements and is recorded as unavailable. The whole blueprint
was searched for diagonal statements; the other dualizing-diagonal results use etale
coefficients, rather than derived O-modules, and are not duplicate statements.

## New nodes

`lem-sc-perfect-diagonal-dualizing-evaluation`, in
`dag/nodes/sec-picard-framework/lem-sc-perfect-diagonal-dualizing-evaluation.json`,
records the perfect-diagonal evaluation chain of Tags 0E2Q and 0A9U, with the
functorial pullback identity and transport for specified adjoints and derived universes.
Its module is `Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation`.

`lem-sc-smooth-diagonal-dualizing-determinant`, in
`dag/nodes/sec-picard-framework/lem-sc-smooth-diagonal-dualizing-determinant.json`,
records the constant-rank specialization of diagonal Koszul duality through the
conormal/differentials isomorphism. Its module is
`Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant`.

No existing statement or definition changed; no change record is required.


## Second reading by Q3

1. **Public contract: pass.** Compared every delivered module with the repository.
   The two intermediate modules are new. The original theorem signature is byte for
   byte unchanged, including independent derived universes, R, comparison, adjunction,
   and specified structure object. Its existing docstring is unchanged. There are no
   altered definitions or existing statements and no change record is required.
2. **Lean and axioms: pass, with the reported open dependencies.** Compiled all three
   files using lcompile.py. Scratch copies with #print axioms show only propext,
   Classical.choice, Quot.sound, and sorryAx for the three public theorems. The proved
   private qc_single uses only the three allowed axioms. There is no sorry in the
   item module, no hollow definition, and no forbidden axiom, unsafe, opaque,
   implemented_by, or extern construct. The only added holes are the two named public
   intermediate theorems, each with an exact by-sorry body, proof docstring, and node.
3. **Intermediate statements: pass as a decomposition.** Read Stacks Tags 0BRT,
   0E2Q, 0A9U, and 0BR0 directly. Evaluation is the chain before identifying c(OP);
   it requires flatness and perfection of the diagonal pushforward, without a
   determinant conclusion. Determinant identification is the constant-rank case of
   Koszul duality, without a or any tensor-evaluation conclusion. Neither restates
   the original theorem. Properness supplies closed diagonals and Noetherian fibre
   products. Adjunction uniqueness and localization equivalences justify arbitrary
   adjoints and independent universes. Checked empty X, identity maps, and dimension
   zero finite etale maps: the determinant is the structure object in degree zero,
   and evaluation agrees with the diagonal identity. Both remaining proofs require
   substantial comparison/gluing work and cannot be closed in a few minutes.
   Independent LeanFinder searches for “Grothendieck duality flat proper diagonal
   shriek tensor relative dualizing complex is unit” and “exceptional inverse image
   regular closed immersion normal bundle exterior power shift Koszul” found only
   ordinary adjunction/immersion results. Loogle adjunction/isomorphism search found
   generic adjunction transport, and Mathlib grep for locallyRankedExterior,
   dualizing, and normal determinants found no counterpart. Repository searches
   found the existing ingredient theorems, not either intermediate conclusion.
4. **Route and pruning: pass after report repair.** Read the original dependency
   declarations and checked the tensor-isomorphism direction: n inverse takes the
   displayed determinant to c(OP), then e takes the tensor to the unit. The explicit
   Noetherian instances, chosen diagonal adjunction, and proved quasi-coherence
   witness supply the intermediate hypotheses. The proof follows the original
   diagonal/Koszul route; sk-thm-picard-duality.realized is unchanged. The five old
   direct dependency nodes no longer used by the parent are now enumerated above;
   they remain needed transitively, so no module is globally pruned. Public imports
   support the signatures; proof dependencies use plain imports. Removed the
   redundant added Smooth proof import, and verified the resulting module compiles.
5. **DAG: pass.** The parent changes only proof, proof_deps, and proof_origin.
   Its statement and lean record are unchanged. For all three nodes, proof_deps
   equals the union of the step uses. The new nodes' Lean statements match the
   declarations verbatim after whitespace normalization; all dependencies exist,
   and source, searches, status, creation, blueprint, chapter, unit, and lean fields
   are present and agree with their modules. One original hole is closed and two
   lower holes are added: the hole count increases by one (ledger net -1 closed
   minus added), not a sorry-free mathematical proof.

Second reading changed only the redundant Smooth proof import and the report's
explicit pruning/dependency accounting. The existing proof and new statements were
retained.
