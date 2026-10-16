## What changed

Replaced the body of
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_kernels` by a complete
Lean reduction to a single local pivot chart. Its signature and visibility are unchanged.
The new proof uses proof-only imports of the existing finite-presentation, local splitting,
field local-triviality, and scalar-extension APIs, plus the new pivot module.

The parent module proves the kernel and cokernel identities for a pivot block, transports
rational local freeness through pullback and scalar extension, and performs strong induction
on the number of source generators. It also proves both exact cokernel calculations needed
to handle arbitrary finitely presented source and target modules, including torsion, and
then glues along their constructible stratifications. The original node's proof and proof
edges now describe this route.

Validation: the final parent compiled locally without profiler output or warnings in
41.0 seconds, and the pivot module in 6.5 seconds. The first delivery dry run passed
compilation and axiom checks. After the metadata repairs, the required dry run printed
`OK (dry run)`, passing preflight except for the second-reading
section, which the assigned second reader writes. Nothing was pushed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralConstructible_kernels`.
The item module has no remaining `sorry`.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralMatrix_pivot_cover`, in
`lean/Sheaf/Paper/IntegralMatrixPivotCover.lean`, node
`lem-weil-pbc-integral-matrix-pivot-cover`.
This is a decomposition: one original hole closed and one strictly smaller hole added,
not a net decrease in holes. The new theorem asserts only one zero-or-pivot chart; it
asserts neither kernel finiteness nor constructibility. Strong induction and the passage
from free matrices to arbitrary constructible modules are actual proved Lean code.

The existing
`AlgebraicGeometry.ProEtale.exists_finiteFree_cover_of_condensedField_lfp`
is used as a stated dependency, rather than reproved or duplicated. Its existing proof
obligation is not a hole added by this delivery.

## No longer needed

No whole module or DAG node is withdrawn, and no original dependency import is removed.
The import of `Sheaf.Paper.ConstructibleCokernelsExtensions` is retained as `import all`
to use its already proved private presentation and cokernel helpers.

The original node's full finite-integral-model comparison, specialization invariance of
all Smith invariants, and complete continuous Smith diagonalization are not needed.
Those were prose steps, not separately attached Lean modules or nodes. The proof only
needs one integral pivot with an invertible rational image; it proves the remaining
induction itself. In particular it does not import a separate integral model-classification
or Smith-form module. Scalar-function and basis experiments not used by the delivered
proof remain outside the Lean delivery.

## Where the brief, the DAG or earlier work was wrong

No existing statement or definition is changed or disputed. The original route was longer
than necessary: rational local freeness of the cokernel supplies the rank control needed
for a single pivot. It is essential to keep that hypothesis. For a continuous scalar with
a non-open zero locus, unconditional local freeness of the sheaf kernel would be false.

Second reading corrected the pivot citation: Lemma 6.8.7 itself reduces to Corollary
6.8.5 and does not write out a matrix argument. The pivot docstring and new node now
identify their continuous-function proof as an agent reduction in the integral coefficient
framework of Definition 6.8.10 and Proposition 6.8.11(1).

The blueprint ancestor helper returns `None` for the existing item because its
`created.item` is a module name. For the new node, the explicit ancestry pointers were
followed through `nt-target-proetale-e` to the actual blueprint node
`thm-weil-pbc-finite-extension`; no existing blueprint fields were altered.

## New nodes

`lem-weil-pbc-integral-matrix-pivot-cover` states a one-pivot covering for a finite free
integral matrix whose rational cokernel is already locally free. It gives either a zero
matrix or a block `((p,r p),(c,d))` with monic integral pivot `p`, invertible rational pivot,
and strictly smaller complementary source rank. What remains is to identify finite free
matrix entries with continuous coefficient functions compatibly with pullback; use exact
geometric-field evaluation of the supplied free rational cokernel to obtain its constant
pointwise matrix rank, including the rank-zero neighborhoods; and assemble maximal-norm
pivots, integral continuous quotients and coordinate permutations into the displayed chart.
The docstring and node give the complete argument. Edge cases checked include empty
schemes, zero source or target rank, zero matrices, and positive-rank pieces.

Change record: `coord/changes/integral-constructible-kernel-proof-commands.md`. The static
interface checker flags the added proof commands; the record documents them and the
unchanged public signature. No downstream module is adapted.

Further local proof experiments are retained in the sandbox's `scratchpad/` for the
second reader, rather than added as unused library modules. `ContinuousPivot.lean`
compiles the integral quotient, ultrametric pivot neighborhood, constant-rank zero-matrix
argument and finite-family quotient construction. `RegularContinuous.lean` compiles the
continuous-function description of regular endomorphisms, their monicity for nowhere-zero
functions, the matrix-entry equivalence and invertibility over a field.
`FreePivotBasis.lean` compiles the finite-free successor splitting.
`InternalEvaluation.lean` compiles exact geometric-field internal-module evaluation.
`AbInternalModule.lean` builds the ordinary-module realization of internal modules in Ab
and proves finite-colimit preservation. These experiments are not imports or new
obligations in this delivery; the named remaining theorem still needs their compatible
coefficient transport and assembly.

## Second reading by H2

1. **Signatures and accidental changes.** I compared the item module with the repository
   version. The public declaration `integralConstructible_kernels` has the same signature
   and visibility; the additional declarations are private except for the new split-off
   theorem. The pivot node records that new statement and its module. Verdict: passed.

2. **Proof and axioms.** I compiled both delivered modules with `lcompile.py`, then
   compiled the sandbox in import order. The item has no `sorry`; the only remaining
   `sorry` is the named theorem `integralMatrix_pivot_cover`, with a source, complete
   proof sketch, and matching DAG node. No `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declaration was added. Explicit `#print axioms` checks of both
   public theorems show exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The latter remains because the pivot and imported obligations are open. Import-order
   compilation completed cleanly in 24.4 s for the pivot and 54.1 s for the parent.
   Verdict: passed subject to the recorded pivot split.

3. **Statements and searches.** I checked the pivot theorem's zero-rank, zero-map, and
   nonzero-pivot branches against its hypotheses, and searched the repository and the
   recorded Mathlib searches for an existing declaration. Additional second-reader searches
   for continuous valuation-ring matrices and local Gaussian elimination found ordinary
   field-matrix transvection results, not the needed integral sheaf chart. The split-off statement is
   strictly narrower than the parent: it supplies one local matrix chart and does not
   claim kernel finiteness or constructibility. Verdict: passed.

4. **Pruning and route.** The parent proof uses the existing finite-presentation,
   scalar-extension, local-splitting, constructible-Serre, and coefficient declarations;
   the old prose-only Smith-invariant route is not imported. The unit remains
   `sk-thm-properbasechange`; none of its `realized` statement or step nodes is removed
   or bypassed. The parent node's proof and `proof_deps` were updated to match the Lean
   route. Verdict: passed.

5. **DAG agreement.** I checked the parent and pivot nodes, including their Lean records,
   proof steps, proof dependencies, origins, and blueprint ancestry. The parent node
   names the pivot split and the pivot node names every unresolved ingredient. Verdict:
   passed.

I corrected the source attribution in the new pivot docstring and node, and added this
review and validation evidence to the report. No Lean proof, statement, definition,
import, or change record required repair.
