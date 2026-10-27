## What changed

Proved `AlgebraicGeometry.ProEtale.finite_constructible_complex_heart_cohomology_vanishes`
from the existing supported three-term estimate, a common local-model tree, and finite
extension reconstruction. The statement and all original public imports are unchanged.
Only the three terms of `K.sc 0` are used; the finite-support hypothesis remains in the
signature. Exact pullback identifies the homology on each leaf, and the homological
functor given by derived sections and degree-q cohomology propagates vanishing through
distinguished triangles without changing the bound.

Added `Sheaf.Paper.FiniteConstantLocalModelTree` for the remaining geometric common-tree
step, and `Sheaf.Paper.QcqsTreeFiniteExtensions` for the coefficient-independent interface
to the existing proved private `LatticeTree.tree_reconstruct` helper. Updated the item's
DAG proof route and added matching nodes. No source-library declaration was changed.

## Proved and sorry left

Closed 1 of 1 original holes, by a decomposition:
`AlgebraicGeometry.ProEtale.finite_constructible_complex_heart_cohomology_vanishes`
(node `lem-sfb-finite-constructible-complex-heart-cd`).

Proved `AlgebraicGeometry.ProEtale.qcqs_tree_finite_extensions`
(node `lem-sfb-qcqs-tree-finite-extensions`) from the existing general reconstruction helper.

Added 1 hole, split off as
`AlgebraicGeometry.ProEtale.exists_finite_constant_local_model_tree`
(node `lem-sfb-finite-constant-local-model-tree`). It has a complete natural-language proof
in its docstring. This is the purely geometric common-refinement step: it has no admissible
coefficient assumption, complex, torsion bound, or cohomological conclusion. No hole remains
in the item module or the reconstruction interface. Net holes closed minus added: 0.
The existing `supported_three_term_scalar_cohomology_vanishes` remains an open dependency
outside this packet; it is used exactly as stated and no duplicate is introduced.

## No longer needed

Removed these direct private imports from the item:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`

The geometric refinement, coefficient pullback and exactness inputs remain dependencies of
the new geometric statement or the existing reconstruction theorem. This does not request
withdrawal of those modules. Exact-functor homology comparison is still used transitively.

The separate delta-functor comparison is unnecessary for the assembly proof: nodes
`lem-weil-pbc-right-derived-universal-delta-functor`,
`lem-sp-grothendieck-enough-injectives`, and
`lem-weil-pbc-bounded-below-injectives-kinjective` are removed from this item's proof route.
The first two corresponding obsolete top-level `tool_uses` approvals are removed. The proof
uses the existing triangulated unbounded right-derived functor directly. No module is
withdrawn, since these dependencies can remain needed elsewhere or transitively.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is valid. The numbered refinement supplied by
`exists_finite_open_closed_refinement` and the recursive `QcqsOpenClosedTree` are different
interfaces. Conversion requires reverse induction on increasing child indices and root
normalization by an isomorphism as an open edge with empty closed complement. The geometric
proof attempt elaborates but times out in kernel checking (about seven seconds of
elaboration, then the 60-second kernel-check limit); an attempted private structure
for the needed refinement data also did not meet the limit. The remaining geometric step
is therefore delivered as a named public theorem at this delivery round, rather than an
unfinished proof or a timeout presented as a tool failure.

The public lattice-tree reconstruction theorem has extra coefficient and lattice hypotheses,
but its proved private general helper has none. The new reconstruction interface reuses
that helper. Empty leaves are treated by the empty pro-etale covering family.

## New nodes

`lem-sfb-finite-constant-local-model-tree`: the geometric common-refinement step for an
arbitrary finite family of constructible modules over any commutative condensed ring.
Its proof is the existing finite constructible refinement, pullback of local models, and
conversion of the numbered tree to the recursive tree. The declaration is the one new hole.

`lem-sfb-qcqs-tree-finite-extensions`: coefficient-independent finite-tree reconstruction
under an arbitrary additive exact functor, proved by the existing private
`LatticeTree.tree_reconstruct` helper. It has no analytic vanishing assertion or new hole.
No change record is necessary: no existing signature or definition changes.

Validation: `lcompile.py --all` compiled all three delivered modules in import order;
the final delivery repeats the required compile and declaration/axiom checks.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
