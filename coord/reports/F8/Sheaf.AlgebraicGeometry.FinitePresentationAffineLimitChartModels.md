## What changed

Completed `AlgebraicGeometry.exists_finitePresentation_affine_limit_chart_models`
without changing its statement or either public definition. Added the proved module
`Sheaf.AlgebraicGeometry.FiniteAffineRefinementExistence`, which constructs the finite
labelled affine cover, pair covers, pair-chart overlap covers and subordinate triple
covers on any quasi-compact quasi-separated scheme.

The proof descends all labelled opens, stabilizes every needed equation using a finite
type of open expressions, constructs independent affine sheaf models using the existing
preorder ring-colimit descent theorem, and transports them to one common stage. It
constructs the canonical ring colimit and the section comparison, including the exact
formula using the actual `tensorPullbackSection`. The auxiliary algebra and geometry
arguments are proved private helpers. The item node now follows this implementation;
the new existence theorem has its own node and complete proof description.

All writes are confined to this sandbox. Existing public imports and interfaces are
preserved; no existing module other than the item is changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_finitePresentation_affine_limit_chart_models`
(`lem-trf-fp-affine-limit-chart-models`).

Also proved the new theorem
`AlgebraicGeometry.exists_finiteAffineRefinementCollection`
(`lem-trf-finite-affine-refinement-existence`).

Holes closed: 1. Holes added: 0. Split-off holes: 0. No `sorry` remains in either
submitted module. Imported declarations retain their existing proof status; no claim
is made that this closes all holes in their transitive dependencies.

Validation: server `lcompile.py --all` compiled both modules without errors or
warnings: finite refinement existence in 8.2 s and the item in 41.0 s, both below
the 60 s limit. Delivery preflight is run by the required delivery command.

## No longer needed

Removed these redundant private imports from the item:

- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`: Mathlib already gives
  affine limit projections, `isLimitOpensCone`, and preservation of affine limits by
  global sections. The proof does not construct another ambient limit.
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`: the proof uses the defining
  Mathlib `QuasiSeparatedSpace.inter_isCompact` criterion directly.
- `WeilConjectures.Algebra.FinitePresentationColimit`: its needed object clause is
  supplied through the existing, proved preorder wrapper
  `WeilConjectures.Algebra.Homology.FinitePresentationPreorderColimitModel`.

The item no longer directly depends on `lem-weil-pbc-limit-affine-transition` or
`lem-pc-fp-module-map-descent-affine`: the Mathlib limit-cone leaf and the preorder
object-model theorem replace those direct uses. The latter algebraic lemma remains
needed by the preorder wrapper. The finite-cover preparation is implemented in the
new proved existence lemma. Other former cover-preparation dependencies are recorded
there or supplied directly by Mathlib. No library module or declaration is withdrawn,
and no claim is made that one becomes globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The stated algebraic descent theorem assumes a partial
order, while this item permits a preorder and its restricted diagram is indexed by an
over category. The library's existing preorder wrapper, after a thin-skeleton
reindexing, handles this difference without strengthening the hypotheses.

The canonical section formula requires care: the affine-sections theorem uses the
chosen tensor-pullback adjunction. Its existing theorem explicitly fixes its unit to
the actual tensor section, so the normalization is proved, rather than assumed. The
`appLE` versus `appTop` ring maps are rewritten before transporting tensor products.

Edge cases were checked in the argument: empty schemes and empty main/pair/overlap/
triple covers; a zero-sized label set; zero modules and zero rings; and distinct
preorder indices which are isomorphic. Finite types may be empty throughout. The
common-stage choice explicitly includes the geometric stage even when there are no
module labels. No unit statement or unit proof step is bypassed.

## New nodes

`lem-trf-finite-affine-refinement-existence`, in
`dag/nodes/sec-trace-formula/lem-trf-finite-affine-refinement-existence.json`, states
and proves only the finite-cover preparation from Step 2 of the item's original
proof. Its Lean declaration is
`AlgebraicGeometry.exists_finiteAffineRefinementCollection` in
`Sheaf.AlgebraicGeometry.FiniteAffineRefinementExistence`. It introduces no proof hole.
LeanSearch, LeanFinder, local Mathlib/DAG searches and the blueprint search found
individual finite-cover results but no existing theorem packaging this collection.
No change record is needed: existing statements, definitions, attributes and public
imports are unchanged.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
