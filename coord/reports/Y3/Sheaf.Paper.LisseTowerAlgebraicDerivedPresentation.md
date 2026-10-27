## What changed

Filled `AlgebraicGeometry.Scheme.lisse_tower_algebraic_derived_presentation` without
changing its mathematical statement or public imports. The two unused nested proof
binders `hφ` and `hβ` are prefixed with underscores for a clean compile. The proof obtains a local normalized
finite algebra diagram, proves the completion quotients finite using the existing kernel
and evaluation construction, forms its algebraic homotopy limit, proves pseudo-coherence
and both cohomology bounds, and uses the actual reduction adjunctions and their unit
compatibility to descend its reductions.

The private reconstruction helper now retains pseudo-coherence, interval vanishing and
projection compatibility directly. No bounded termwise representative is needed here.
The public statement is unchanged, and there are no shared interface or definition changes.
The existing main-node proof fields now describe this argument. The full sandbox compiled
with both modules under the per-file limit (7.5 seconds for the new statement and
18.9 seconds for the item in delivery validation). The two unused internal proof-binder
names are underscored to satisfy the warning-free delivery check.

Added `Sheaf.Paper.LisseTowerLocalAlgebraicReductionDiagram`. Its theorem isolates the
finite local geometry and the functorial realization comparison: it constructs only a
normalized finite algebra tower with finite cohomology and transfer of zero cohomology.
It assumes separate bounds at each finite level, and asserts no completed algebraic object,
no pseudo-coherence and no bounds for a completed object. Given an algebraic object with
specified compatible reductions, it compares their actual realization with the local
geometric tower. The main proof supplies this input by its separate homotopy-limit argument.

Mathlib searches (LeanFinder, Loogle and grep), together with searches of Sheaf and the
adopted source library, found no theorem that directly closes the local geometric step.
The existing normalized algebraic reconstruction, finite-group Mittag--Leffler, countable
product and derived scalar-adjunction declarations are used directly.

## Proved and sorry left

Closed the one original body of
`AlgebraicGeometry.Scheme.lisse_tower_algebraic_derived_presentation` by a complete Lean
proof from the retained declarations and the new finite-diagram lemma. The item module
has zero remaining `sorry` bodies.

Added one hole:
`AlgebraicGeometry.Scheme.lisse_tower_local_algebraic_reduction_diagram`, in the new module,
with node `lem-weil-pbc-lisse-tower-local-algebraic-reduction-diagram`. Its proof is exactly
`by sorry`; its docstring and node give the source and complete natural-language proof.
This is a decomposition (one upper hole closed, one strictly smaller geometric obligation
added), not a net hole closure. It does not move algebraic reconstruction or its cohomology
interval argument into the new obligation.

Edge cases checked in the new statement: empty strata admit the empty covering sieve;
zero quotient rings give zero finite levels; zero cohomology transfers degree by degree;
bounds may vary with the level; realization is quantified over every specified scalar map,
exactness witness, left adjoint and compatible reduction isomorphism. The statement does
not assume finite Tor dimension or surjectivity of isomorphism-sheaf transition maps.

## No longer needed

Removed the item's proof import of `Sheaf.Paper.BoundedFinitePseudoCoherentModel` and its
proof dependency `lem-weil-pbc-bounded-finite-pseudocoherent-model`: the main theorem
requires an algebraic derived object and bounds, not a bounded termwise model. Other
consumers still need that module; this delivery does not withdraw it or claim global pruning.

Removed unused private helpers `transport_normalization_in_image`,
`transport_normalization`, `universal_arrow_iff_bijective`,
`completionQuotientEquiv_mk`, `completion_eval_factor`, and
`completionQuotientEquiv_factor`. The completion evaluation kernel and quotient-equivalence
helpers remain and are used to prove the completion quotient rings finite.

The geometric dependencies formerly listed directly by the main node are retained below
the new local finite-diagram node. They are delegated, not globally pruned. No adopted
WeilConjectures declaration or public import is changed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The former private helper produced an unnecessary bounded finite representative instead
of retaining its already proved pseudo-coherence and vanishing. The main statement does
not require that representative. Its elimination removes that dependency at this node.
The local geometric argument needs only separate finite-level bounds; the common interval
is used in the algebraic homotopy-limit argument. An auxiliary full-DAG walk encounters the pre-existing exchange cycle
`lemma-weil-pbc-derived-exchange-replacement` →
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-bounded-comparison` → the first node. The original
item already reaches it through its existing geometric dependencies. The same walk finds the pre-existing missing dependency
`def-weil-pbc-localization-universal-property`. This delivery
does not alter those nodes or introduce a cycle through either edited node.
No statement is disputed, and no unit
statement or unit proof step is bypassed. The original module's existing helpers compiled
in 13 seconds before editing.

## New nodes

`lem-weil-pbc-lisse-tower-local-algebraic-reduction-diagram` records the finite geometric
subargument of Tag 09BV and the finite tensor-realization comparison, before Tag 09AV
algebraic reconstruction. It supplies a normalized finite diagram, transfer of vanishing,
and realization of explicitly specified compatible reductions; it contains no existence
assertion for the completed algebraic object. No change record or forced adaptation is
needed because all edits are in the item, its own node, and the new module and node.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
