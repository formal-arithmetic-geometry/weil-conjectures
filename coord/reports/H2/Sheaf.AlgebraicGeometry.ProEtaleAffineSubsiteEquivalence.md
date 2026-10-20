## What changed

Proved `AlgebraicGeometry.Scheme.ProEt.affineWeaklyEtale_sheafEquivalence` in
`Sheaf.AlgebraicGeometry.ProEtaleAffineSubsiteEquivalence`, with every existing
statement and definition unchanged. Five proved private helpers establish affine
pullback closure, cover-density, finite affine refinement, continuity, and equality
with the induced topology. Mathlib's dense-subsite equivalence then gives the
required equivalence and its natural isomorphism with restriction, for exactly
`Type (max (u + 1) v)`.

The proof follows Stacks 098W/098E via its dense-subsite formulation. It uses only
Mathlib proof constants; it does not use the narrower source-library AffineProEt
site or its ind-etale presentation condition. The six-step DAG proof and its
dependencies now record the actual argument. There are no new nodes.

Added private imports of
`Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology` and
`Mathlib.AlgebraicGeometry.Cover.QuasiCompact`.
The public-import change is recorded in
`coord/changes/proetale-affine-subsite-public-import.md`.

Repair of return C-e17cd (reviewed head e17cd4f1b): the mathematical review passed;
the landing failed while reading the unrelated quarantined module
`Sheaf.AlgebraicGeometry.PicardRightCechCupGenerators`. Its source is now restored
on current `sheaf-dag`. This packet retains the reviewed proof and dependency
pruning, preserves every current node field outside the stage-3 owned fields,
and is rebuilt on current `sheaf-dag` by deliver3.py. No Picard module or
quarantine archive is changed by this delivery.

Fresh server validation via lcompile.py on 2026-10-21 compiled the final item
and the current, unchanged direct consumer
`Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints` together in import order, without
errors or warnings (2.6 s and 3.0 s). The consumer was used only for validation
and is not included in the packet. The earlier separate `#print axioms` check
reported exactly `propext`, `Classical.choice`, and `Quot.sound`; deliver3.py
rechecks the axiom probe before delivery. All delivered Lean lines have at most
100 characters.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.ProEt.affineWeaklyEtale_sheafEquivalence`
(node `lem-sfb-proetale-affine-subsite-equivalence`).

Added holes: 0. Split off: 0. Holes remaining in the delivered module: 0.
The five private helper theorems are fully proved.

## No longer needed

Removed private imports:

- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`
- `Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence`
- `Sheaf.AlgebraicGeometry.EtaleComparison`
- `Sheaf.AlgebraicGeometry.WeaklyEtaleStability`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`

Removed public import `Sheaf.CategoryTheory.SiteCoveringAxioms`; the existing
site definitions need only their original Mathlib public imports. The geometric
Mathlib files listed above are already supplied by Proetale and AffineScheme.
Their mathematical facts remain used, and their geometric DAG leaves remain.

The following old proof dependencies are unnecessary on this edge:

- `def-weil-pbc-special-cocontinuous-functor`: fullness, cover-density, and the
  induced-topology criterion directly establish Mathlib's dense-subsite predicate.
- `lem-weil-pbc-special-cocontinuous-sheaf-equivalence`: replaced with the already
  existing Mathlib leaf `lem-cbc-local-dense-ordinary-sheaves`, which supports the
  actual object/hom and coefficient universes without enlarging hom types.
- `det-pe-morphisms-etale-comparison`: only its etale-to-weakly-etale clause was
  relevant; Mathlib's direct instance suffices.
- `sk-lem-pe-weakly-etale-stability`: replaced by Mathlib's direct composition and
  base-change instances recorded in the existing leaf
  `lem-weil-pbc-weakly-etale-composition-base-change`. None of its ind-etale clauses
  is needed.
- `def-weil-pbc-sites-and-cohomology`: no proof dependency on its custom covering
  predicate is needed; its original statement-dependency entry is preserved.

Removed the obsolete top-level tool-use approvals for the comparison and stability
nodes just listed. Retained all other approvals in their original order. These
are dependency removals from this item, not withdrawal of any upstream declaration
or a claim that these modules have no other consumers. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original six-step route is valid, but the
custom special-cocontinuous theorem is needlessly restrictive for this proof's
universes. The dense-subsite form is already explicitly allowed by the original
step 6 and theorem docstring, and its exact Mathlib leaf already exists.

Finite covering presieves must use bind composition in a pretopology. The proof
constructs the finite pretopology explicitly; it does not assert the stronger
Precoverage.IsStableUnderComposition for finite presieves, which would fail for
arbitrarily repeated indexed covers.

The affine refinement is built with the actual morphism of covers from
QuasiCompactCover.exists_hom. The equations of that morphism prove the required
factorizations, rather than asserting them. Empty schemes and empty finite covers
are admitted by that theorem and by Pretopology.finite; no nonemptiness,
quasi-compactness or quasi-separatedness assumption on X is introduced.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
