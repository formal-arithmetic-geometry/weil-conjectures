## What changed

Proved `AlgebraicGeometry.Compactification.exists_common_dense_refinement` in
`Sheaf.Compactification.CommonDenseRefinement` with its signature unchanged. The pairwise
construction, density and cartesian open squares are already proved in the imported upstream
`WeilConjectures.Compactification.CommonRefinement`. Two proved private helpers translate
those squares into equalities of inverse-image opens. A finite-subset induction constructs
a dense common refinement and composes the boundary equalities explicitly.

Updated the existing node's proof, proof dependencies and proof origin to record this
realization of the same graph-image construction and finite-family route. No definitions,
public signatures, public imports or other modules changed. No change record is needed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Compactification.exists_common_dense_refinement`
(node `det-nagata-refinement-common-dense`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. Both private preimage helpers are proved.
The module compiles without warnings, and a separate `#print axioms` check for the full
theorem reports only `propext`, `Classical.choice` and `Quot.sound`. The required delivery
dry run compiled the file and passed the stage-3 preflight.

The finite-family proof does not assume dense inputs. Its empty-subset seed is the already
available `inf c₁ c₁`, and the insertion step retains density by taking another `inf`.
It uses no arbitrary witness from a holed existence theorem. Equality of opens also fixes
all their restricted structure sheaves. The proof applies to empty schemes, non-dense
singletons, additional proper components, and independently sized finite index types.

## No longer needed

No imports removed: the existing imports expose the constructions and predicates in the
unchanged public statement. No library modules withdrawn or pruned.

The proof uses the already proved upstream pairwise construction and its pullback theorems,
so it does not separately invoke the following former low-level proof dependencies:
- `def-weil-quasi-separated-morphism`
- `lem-pc-quasi-compact-base-change`
- `lem-weil-pbc-closed-immersion-base-change`
- `lem-weil-pbc-closed-immersion-proper`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-weil-pbc-proper-base-change`
- `lem-weil-pbc-proper-composition`
- `lemma-nagata-immersion-open-in-scheme-image`

These nodes were removed from this node's direct `proof_deps`; their underlying geometric
facts are already encapsulated by the proved upstream construction. No additional
`Sheaf` modules for them need importing or proving for this item. In particular no new
proof of the graph-immersion factorization or closed-graph kernel argument is necessary.
The unit's graph-image construction and finite-family induction are retained.

The holed `boundaryRefinementProperty_isMultiplicative` in the statement import is not used:
composition of boundary identities is proved directly with `Scheme.Hom.comp_preimage`.

## Where the brief, the DAG or earlier work was wrong

No false statement or tool defect found. The source library now proves the pairwise
construction, density and both open pullback squares, so the planned seven-step geometric
proof need not be repeated. The existing hypotheses are stronger than what this proof
needs, and remain unchanged. No new nodes or forced adaptations.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
