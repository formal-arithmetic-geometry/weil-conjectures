## What changed

Proved `CochainComplex.FiniteFiltered.filteredDerivedHomCalculusIn` by transporting
the existing canonical-coefficient calculus along the exact universe-lift functor
on abelian groups. The public structures, existing public import, and theorem
signature are verbatim unchanged. All added imports in the assigned module are
private proof imports.

Added `Sheaf.Algebra.Homology.ExactFilteredCoefficientChange`. Its theorem is fully
proved: it constructs the mapped finite filtration using images, compares the
steps and cokernel quotients, descends through localization, and proves both
normalized inclusion and grade-zero projection equations. Naturality of the
representative high comparison uses the existing universal truncation Hom
bijection. Every new data definition has a concrete construction and no hole.

The enlargement proof transports homology and its naturality, the ordinary
Hom-complex model through the double-ULift isomorphism, and the finite-support
graded bicone through an additive functor. The latter is proved by restricting to
the finite support, preserving its biproduct, and extending over zero summands;
empty support is included. The last two structure fields follow from the two
normalized coefficient-change squares after taking H⁰.

Recorded the existing base calculus separately from the enlarged interface in
the DAG, and redirected the truncation-data node's infrastructure citation to
that base. This changes no Lean consumer. The combined dependency closure of the
four delivered node records is acyclic (334 nodes in the local audit).

Validation: `lcompile.py --all` compiles both files without warnings (14.6 s
and 18.4 s in the audit run). The public structures and theorem signature were
compared verbatim with the shared source. The required delivery preflight is
responsible for the final packet checks.

## Proved and sorry left

Original holes: 1. Holes closed: 1. Holes added: 0. Holes left in delivered Lean
files: 0. No split-off holes.

- Closed: `CochainComplex.FiniteFiltered.filteredDerivedHomCalculusIn`
  (`lem-trf-filtered-derived-hom-calculus`).
- Also proved the new theorem
  `CochainComplex.FiniteFiltered.exactFilteredCoefficientChange`
  (`lem-trf-exact-filtered-coefficient-change`). All its private helpers are proved.

The unchanged existing declarations `filteredDerivedHomCalculus` and
`filteredTruncationTriangle` remain intentional proof dependencies. Their
existing holes are not copied, moved, or added by this packet. Thus this is the
stage-3 proof from stated dependencies, not a claim that the whole target closure
is already axiom-free. The compiler's axiom audit inherits `sorryAx` from the
existing dependency proofs, along with the standard logical axioms.

## No longer needed

No module or node is withdrawn or pruned. The original seven-step construction
and its dependencies remain needed by the existing canonical-coefficient
calculus; they are retained in its new base node. The enlarged interface now
uses that existing theorem and exact coefficient transport directly, instead of
repeating the construction in a larger universe.

During proof development, removed redundant imports of
`Mathlib.CategoryTheory.Preadditive.Biproducts` and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts`: both are already
provided by the retained additive-functor import. No import from the current
shared item source was removed.

## Where the brief, the DAG or earlier work was wrong

The source had already been restored and accepted after the previous quarantine
repair. This packet proves its remaining hole; it is not a restoration no-op.
The old DAG proof plan describes the canonical-coefficient calculus already
stated in the base module. Lean universes do not permit simply instantiating that
theorem at larger object universes while retaining the same category A. Exact
coefficient transport supplies the missing independent-universe argument.

The definition node for universal truncation data cited the enlarged Hom node
for infrastructure actually defined in the base module. Splitting the existing
base attachment and redirecting only this citation prevents an artificial cycle.
The definition statement's mathematical clauses, its Lean signature, and every
consumer stay unchanged. Its sole DAG citer, the truncation triangle, was audited.
See `coord/changes/T2-filtered-hom-universe-coefficients.md`.

## New nodes

`lem-trf-filtered-derived-hom-calculus-base` records the **already-existing**
canonical-coefficient theorem and infrastructure in
`Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`, with the old seven-step proof
plan. It adds no theorem, duplicate Lean declaration, or hole. Its Lean record
therefore has `existing: true`; this is attachment bookkeeping for an existing
library dependency, not a newly stated lemma in an existing module.

`lem-trf-exact-filtered-coefficient-change` records the fully proved generic exact
coefficient-change theorem, its data structure, image/cokernel construction,
localization descent, and the two normalized squares. It is a separate
homological-algebra result, rather than a restatement of the assigned enlarged
Hom calculus.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
