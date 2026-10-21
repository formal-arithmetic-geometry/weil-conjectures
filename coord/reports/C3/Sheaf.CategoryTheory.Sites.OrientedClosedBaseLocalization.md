## What changed

Completed `CategoryTheory.oriented_closed_base_localization` in
`Sheaf.CategoryTheory.Sites.OrientedClosedBaseLocalization`, with fully proved private
helpers. All existing public statements and definitions are unchanged.

The topological clause constructs the inverse-image complement from the existing
complement factorization theorem and verifies its universal property, including
bijections on direct-image natural transformations. The module clause uses the
normalized lift's compatibility with the actual adjunction units and conservative
forgetful functors. This gives supported essential image, the actual unit and counit,
full faithfulness, and preservation of finite limits and colimits. The scheme clause
proves the open-support comparison sectionwise on the small etale site, then lifts
the actual scheme direct image to an equivalence with the closed full subcategory.

Added proof-only imports `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale` (subcanonicity), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Small` (continuity). Updated the
existing node's proof and proof origin to describe the implemented argument.
No other library module is changed; there are no consumer adaptations.

Validation: the complete module compiled through `lcompile.py` in 22.6 seconds.
Checked that all original public imports, data declarations, and the theorem signature
are unchanged, that no `sorry` remains, and that Lean lines stay within 100 characters.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.oriented_closed_base_localization`
(node `lem-trf-oriented-closed-base-localization`). All three conjuncts have complete
Lean proofs from the existing declared dependencies. Added zero holes, split off zero
statements, and left zero holes in the item. Every added helper is private and proved.

The proof still uses the existing statements
`CategoryTheory.topos_complement_factorization` and
`AlgebraicGeometry.etaleClosedComplementSets`, as intended by this stage; this delivery
does not claim their remaining holes are closed. It also uses the proved normalized
constant-module inverse-image interface. No arbitrary witness is used to define data,
and no public definition or target signature changes.

## No longer needed

Removed the unused proof import `Sheaf.CategoryTheory.RingedToposMorphism`.
All three declared proof-dependency nodes remain needed. No node or module is
withdrawn. In the module proof, explicit descent of addition and scalar multiplication
is unnecessary: the already normalized lift and its unit compatibility equations
supply a shorter argument. The scheme clause uses the etale set-image theorem directly
and proves its open-support bridge without an additional complement-factorization call.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's module proof planned
explicit descent of algebraic operations; the normalized lift's existing actual-unit
compatibility makes this unnecessary. Its finite-cokernel argument is implemented more
generally by creation of finite colimits in the supported essential image. The node now
records these arguments and the sectionwise etale comparison. The unit route is kept.
The proofs impose no nonemptiness, nonzero-ring, or nonempty-complement hypothesis,
so they include empty/full opens, the zero coefficient ring, and empty schemes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
