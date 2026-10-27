## What changed

Proved `AlgebraicGeometry.Etale.orderedTateCoefficientComposition` with its exact
original signature and docstring. The argument reuses, locally and with attribution,
the complete private `coefficient_comp` calculation in
`Sheaf.Paper.OrderedTateExactOpenComposition` (groups Q1 and H4).
No shared module or definition is changed.

The private helpers identify the normalized roots comparison with the canonical
roots map, prove line composition through the sheafification/scalar-extension
adjunctions, and transport that equation through degree-zero embeddings and shifts.
The public proof is induction on the ordered tensor degree, using
`ordinaryFiniteUnitPullback_comp` at zero and the proved source-library tensor
composition and naturality equations at a successor. It retains the order of factors.
Empty schemes, degree zero, zero coefficients and arbitrary natural exponents are
included; no extra hypothesis is introduced.

Added private proof imports for the constant-unit composition law, canonical roots
pullback, derived single-functor coherence, tensor composition, shift coherence and
whiskered adjunctions. The original public import is unchanged. Updated only the
item node's proof, proof dependencies and proof origin to record this calculation.

Searches: LeanFinder returned generic homological-complex and tensor comparisons,
Loogle found `Functor.map_comp`, and Mathlib grep found no exact Tate-composition
lemma. Project `rg` found the complete private proof above, which is reused.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.orderedTateCoefficientComposition`
(node `lem-pur-ordered-tate-coefficient-composition`).

Holes closed: 1. Holes added: 0. Holes left in delivered modules: 0.
Every private helper has a complete proof or an explicit construction.
This is a proof, with no split-off obligations.

The final import-cleaned proof compiled cleanly on the server in 21.5 seconds
(receipt `7349f2f7d70071b19fa6c50d`). The delivery probe checks the axioms of every
added declaration.

## No longer needed

The general existence/package theorem `etaleFiniteTwistPullback`
(node `lem-asd-etale-finite-twist-pullback`) is not needed as a proof dependency:
the given `OrdinaryFiniteTwistTransport` supplies exactly its two normalizations,
and their composition is proved directly. Its module remains available through
the unchanged public statement import; this delivery claims no module withdrawal.

No original import is removed. Compared with the private proof's source module,
this proof needs neither `Sheaf.Paper.DegreeZeroDerivedMapGluing` nor
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The initial draft's `LowerShriekBaseChangeShift` import is replaced by the narrower
`CategoryTheory.DerivedCategory.Shift.ExactFunctor` import. The exact-coordinate
conjugation and nested-open gluing part of the source module is unnecessary for
this arbitrary-map coefficient equation and is not copied.

No node or module is withdrawn, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and proof plan are correct. The previous node search
already noted the private composition calculation but treated its private visibility
as preventing reuse. Copying its proved local helpers into this module closes the
obligation without another split or an interface change to a shared module.
The old single proof dependency was too coarse: the actual proof uses the given
transport normalizations, the existing constant-unit composition theorem, and
proved source-library degree-zero, shift and tensor comparison equations.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
