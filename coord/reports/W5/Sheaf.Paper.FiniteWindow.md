## What changed

Proved `AlgebraicGeometry.ProEtale.finiteWindow` and
`AlgebraicGeometry.ProEtale.finiteWindow_padicAlgCl` in `Sheaf.Paper.FiniteWindow`,
without changing their signatures or `FiniteWindowAssertions`.

The proof follows all four existing DAG steps. Private proved helpers construct the zero
constant model, use representable Hom exactness on a triangle and its rotations to obtain
bijections, and remove the invertible signs introduced by shifting triangles. The shared
abelian-category argument obtains the upper bijection by t-structure orthogonality and the
lower bijection from the existing unbounded lower-tail theorem. It constructs the additive
equivalence as the lower bijection composed with the inverse upper bijection, proves its
canonical-map equation, and derives naturality from the two truncation naturality squares.
The coefficient theorems supply the existing lower-tail statements separately.

`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty` supplies the
already proved truncation and shift closure facts. There are no new public declarations.
Single-file server compilation passed with no errors or warnings in 6.0 seconds.
The unchanged sole direct consumer, `Sheaf.Paper.ConstructibleCompactness`, compiled against
the delivered module in the same sandbox in 3.5 seconds. The delivery preflight also checks
all declaration axioms. Empty schemes, zero source or target, d_C=0, arbitrary
integer m and complexes unbounded in both directions need no exceptional case.

## Proved and sorry left

Closed both original holes:
- `AlgebraicGeometry.ProEtale.finiteWindow` (node `sk-lem-finite-window`).
- `AlgebraicGeometry.ProEtale.finiteWindow_padicAlgCl` (node `sk-lem-finite-window`).

Holes closed: 2 of 2. Holes added: 0. No sorry remains in the delivered module.
The proof uses the existing, separately assigned `finiteWindow_unbounded` and
`finiteWindow_unbounded_padicAlgCl`; their existing holes are unchanged.

## No longer needed

Removed the proof import `Sheaf.Paper.UniformConstructibleExt`: its uniform Ext bound
is already an explicit hypothesis, so no existence theorem for that bound is needed here.
Removed the public import `Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`:
the proof uses the canonical t-structure truncation API directly and needs no sequential
homotopy colimit predicate or its additional dependencies. The truncation, t-structure,
Hom-exactness and unbounded-tail nodes of the existing proof remain needed.
The zero-model argument is proved locally, avoiding an import of
`Sheaf.Paper.AmbientIndDerivedTriangulated` with its stronger geometric hypotheses.
No existing node or module is withdrawn; `det-finite-window-reduction` is not imported,
as the main node already specifies the direct two-triangle argument.

## Where the brief, the DAG or earlier work was wrong

The retained earlier sandbox had both original holes and no report; its scratch attempt
handled shifted triangle signs incorrectly. The completed proof treats multiplication by
(-1)^m as an invertible action on Hom. The mathematical four-step DAG plan and the two
public statements are correct and are retained. The zero constant model construction is
adapted from the proved private helpers of `AmbientIndDerivedTriangulated`, with the
pullback's additivity supplied explicitly using its existing composite adjunction.

Change record: `coord/changes/W5-finite-window-prune-public-import.md` records removal of
the unused public import and the consumer check.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
