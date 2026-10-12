## What changed

Replaced the sorry in `CategoryTheory.complex_spectral_sequence_comparison`
with a complete Lean reduction. Its original signature and all public imports
are unchanged. Two proof-only imports supply finite-page comparison and finite
filtered-colimit comparison. The proof constructs the comparison cocone at
`N p q`, proves its colimit descent is an isomorphism, composes with the target
convergence isomorphism, and verifies both graded compatibility equations.
For each abutment degree n it sets p=n-q and rewrites n-q+q=n.

Added three modules, each with one public theorem:
`SpectralSequenceFinitePageComparison`, `FiniteFilteredColimitModel`, and
`FiniteFilteredColimitComparison`. The last is proved from the colimit model and
the existing `FilteredObject.finite_filtration_induction`. Four proved private
helpers verify the projection equations and functoriality of restriction and
gradedMap, using monic inclusions and epimorphic cokernel projections. Every new
statement was checked against empty diagrams, zero objects, one-object constant
diagrams, and reversed bounds U<L (which force zero objects).

The original node copy now records the actual proof route. Each new theorem has
a complete node, a source, a proof in words, and actual Mathlib search records.
Sources were read online because this read-only clone has no Stacks TeX checkout:
[Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM),
[Stacks 00DB](https://stacks.math.columbia.edu/tag/00DB), and
[Stacks 0127](https://stacks.math.columbia.edu/tag/0127).
The omitted comparison details are explicitly marked as worker expansions.

## Proved and sorry left

Proved `CategoryTheory.complex_spectral_sequence_comparison` (the item's one
original sorry), by the reduction described above. Also proved
`CategoryTheory.finite_filtered_colimit_comparison`, node
`lem-weil-pbc-finite-filtered-colimit-comparison`.

No sorry remains in the item's module or in `FiniteFilteredColimitComparison`.
Exactly two new sorry declarations remain:

- `CategoryTheory.spectral_sequence_finite_page_comparison`, in
  `lean/Sheaf/CategoryTheory/SpectralSequenceFinitePageComparison.lean`, node
  `lem-weil-pbc-spectral-sequence-finite-page-comparison`: induction on finite
  pages using directed-colimit exactness and page-to-page homology isomorphisms.
- `CategoryTheory.finite_filtered_colimit_model`, in
  `lean/Sheaf/CategoryTheory/FiniteFilteredColimitModel.lean`, node
  `lem-weil-pbc-finite-filtered-colimit-model`: induced finite filtration on
  the colimit, its graded colimit isomorphisms, and filtered descent.

These are strictly separate parts of the argument: the first has no abutment or
filtration data, and the second has no spectral sequence or comparison conclusion.
Existing sorry-bearing dependencies are used intentionally: `exists_gradedMap`
and `finite_filtration_induction` in node `lem-sp-finite-filtration-induction`.
The original theorem is therefore reduced, not certified axiom-free independently
of the remaining nodes.

Local compilation of all four modules succeeds without warnings.

## No longer needed

No original module import is removed: they provide the objects, colimits,
spectral sequences, filtrations and gradedMap used in the unchanged signature.
No unused proof-only import was added.

The original parent's direct dependency `lem-weil-pbc-five-lemma` is no longer
needed by this route. The proof uses the existing finite-filtration induction,
whose route uses the short five lemma instead. Directed-colimit exactness remains
needed below the two new open nodes; it was not globally pruned. The spectral
sequence definition remains needed in the finite-page node and the statement.
No separate uniform-stabilization lemma or module is needed: the supplied finite
pages `N p q` already have compatible convergence isomorphisms to graded pieces.
No claim is made that any of these modules is unreachable from other targets.

The never-delivered restatement node
`lem-weil-pbc-complex-spectral-sequence-comparison-at` and its declaration from the
previous sandbox attempt were removed. The unused private colimit-uniqueness
helper from that attempt was also removed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox attempt's `complex_spectral_sequence_comparison_at` had
exactly the original hypotheses and conclusion, including the quantifier over n.
Applying it after introducing n merely moved the sorry and was not a reduction.
Its report's assertion that this was a genuine fixed-degree step was incorrect.
This delivery replaces it with independent mathematical steps and real Lean glue.

The parent's planned stabilization calculation is unnecessary for its actual Lean
signature: conv and conv' already identify a specified finite page with each
graded piece. Finite-page comparison applies directly there. The hypotheses
hstable, hstable', hvanish and hvanish' remain unchanged but are unused. A scoped
unusedVariables linter option documents this redundancy without renaming binders
or changing the theorem type.

`IsDirected I` does not require I to be nonempty. Both new open nodes explicitly
include the empty case in their proof plans, rather than silently adding Nonempty.
The original unit `sk-prop-h2` has no realized node entry for this auxiliary result;
no unit statement, step, or prescribed route was changed.

LeanSearch was actually attempted for every new statement and returned Internal
Server Error. This unavailability is recorded, without claiming a search verdict;
LeanFinder, Loogle, and source grep were used as well. No available theorem supplied
the required graded-colimit or finite-page comparison compatibility directly.

## New nodes

`lem-weil-pbc-spectral-sequence-finite-page-comparison` states the finite-page
induction from page one, independently of convergence. Its new module has one
public theorem, left sorry with the complete induction and empty-case proof plan.

`lem-weil-pbc-finite-filtered-colimit-model` states the construction of a finite
filtration on colimit A, filtered cocone legs, compatible graded colimit
isomorphisms, and filtered descent. Its new module has one public theorem, left
sorry with the short-exact-sequence construction and edge cases spelled out.

`lem-weil-pbc-finite-filtered-colimit-comparison` is proved. It combines the model,
the supplied graded comparisons and the existing finite-filtration induction;
the graded-map functoriality and colimit comparison equations are proved in Lean.
No definition or existing statement was changed; no change record is required.

## Second reading by S2

1. Compared the delivered item module with the repository version. The theorem
   signature and existing declarations are unchanged; only proof text, proof-only
   imports, and explanatory documentation differ.
2. Compiled all four modules with `lcompile.py --all`; they compile without errors
   or warnings. The two remaining `sorry`s are named split-off theorems with
   docstrings and matching DAG nodes; no definitions contain `sorry`.
3. Checked each split-off statement against the finite-page and finite-filtration
   arguments and their empty-diagram and reversed-bound edge cases. They are
   strictly smaller than the parent comparison and no duplicate library result
   was found by repository search.
4. Checked the proof route and pruning. The parent now uses the finite-page and
   finite-filtered-colimit comparison nodes; the former direct five-lemma
   dependency is removed from its DAG proof dependencies, while the unit route
   through the comparison and filtration induction remains represented.
5. Checked all node `proof`, `proof_deps`, `proof_origin`, Lean records, and report
   details against the actual declarations. The DAG records agree with the code.

No further repair was needed in this second reading.
