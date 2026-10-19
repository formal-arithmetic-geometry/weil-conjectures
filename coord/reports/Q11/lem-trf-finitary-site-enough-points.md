## Worker report

The module `lean/Sheaf/Paper/FinitarySiteEnoughPoints.lean` states
`CategoryTheory.finitarySite_enoughPoints` with proof `sorry`.  It uses the existing
site presentation `Precoverage C`, the recorded `IsSiteForCoverings` declaration,
and the recorded `GeometricMorphism` structure.  The size convention is represented
by explicit universe parameters `u`, `v`, and `w`; the point family is indexed by
`ι : Type (max u w)` and the sheaf values are in `Type (max u w)` (maintainer fix; delivered as `Type w`).

The Lean rendering of each hypothesis and conclusion is as follows.

* `C : Type u` with `[SmallCategory C]` renders the small underlying category.
* `[HasFiniteLimits C]` renders the finite-limit hypothesis.
* `J : Precoverage C` and `hJ : J.IsSiteForCoverings` render the site and its
  covering axioms (`CategoryTheory.Precoverage.IsSiteForCoverings`).
* `hfinite` quantifies every covering family represented by
  `Presieve.ofArrows U f`, with `I : Type (max u v)`.  It supplies a finite index
  type `K : Type (max u v)` (`Finite K`), a covering family `g : V k ⟶ X`, an
  indexing map `r : K → I`, and factorization arrows `q` satisfying
  `q ≫ f (r k) = g k`; the refined family is itself in `J X`.  Thus every
  covering family has a finite covering refinement subordinate to it.
* The conclusion supplies `ι : Type (max u w)` and a family
  `p : ι → GeometricMorphism (Type (max u w)) (Sheaf J.toGrothendieck (Type (max u w)))`
  (maintainer fix; delivered as `Type w`).
  For every sheaf morphism `a : F ⟶ G`, the hypothesis
  `∀ i, Function.Bijective ((p i).inverse.map a)` says all inverse-image maps are
  bijections, and the conclusion `IsIso a` says that the family jointly reflects
  isomorphisms.

Dependency declarations used:

* `CategoryTheory.Precoverage.IsSiteForCoverings`, module
  `Sheaf.CategoryTheory.SiteCoveringAxioms`.  Its declaration has the required
  isomorphism, bind-composition, and covering-pullback clauses for the site's
  presieves.
* `CategoryTheory.GeometricMorphism`, module
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`.  Its fields are inverse and direct
  functors, an adjunction, and preservation of finite limits by the inverse image.
* `def-weil-size-convention` has no Lean declaration (`existing: true` convention
  record), so its universe content is rendered directly by the explicit universe
  binders in the theorem.

The proof-dependency nodes `lem-trf-inverse-system-site-point`,
`lem-trf-point-family-conservative`, and `lem-trf-point-system-refine-all` currently
have no recorded Lean declarations, so there is no module to import for them at this
stage; their proof route is recorded in the theorem docstring and DAG proof field.

Edge cases checked: `K` may be empty (finite index, including an empty covering),
`I` may be empty, and no nonemptiness hypothesis was added.  Empty or degenerate
sites are therefore covered by the same statement.  The finite-limit assumption
includes the terminal object and binary pullbacks.  The refinement equation has the
orientation `q ≫ f (r k) = g k`, so each refined arrow factors through an original
covering arrow.  The theorem allows an empty point index type in a degenerate topos.

Searches made:

* `msearch.py ... leanfinder "finite-cover sites with finite limits have enough points"`:
  returned finite-precoverage and coherent-topology infrastructure, but no criterion
  for enough points.
* `msearch.py ... loogle "HasEnoughPoints, enough points, geometric morphism"`:
  unknown identifier/no usable match.
* `msearch.py ... grep "HasEnoughPoints|enough points|criterion_points" CategoryTheory`:
  found Mathlib's generic `HasEnoughPoints` class and point infrastructure, but no
  finite-cover criterion.
* `rg` over `lean/Sheaf` and `WeilConjectures/` for `finitarySite_enoughPoints`,
  finite-cover criteria, and geometric-morphism point criteria found no duplicate.
* The recorded declarations' full source and docstrings were read in
  `SiteCoveringAxioms.lean` and `Sites/GeometricMorphism.lean`.

The file compiles cleanly with `scompile.py`; the only expected diagnostic is the
postponed `sorry` proof.

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Maintainer fix (stage-2 review)

The delivered conclusion used sheaves with values in `Type w` and an index `ι : Type w`
for an arbitrary `w`, independent of the site universe `u`. For `w < u` the statement is
false: take `u = w+1`, `C` the meet-semilattice with top, bottom and an antichain indexed
by `Type w` (finite limits = top and meets), and the precoverage of families containing an
isomorphism (it satisfies `IsSiteForCoverings` and `hfinite`, and its sheaves are all
presheaves). A left-exact inverse image sending `↓a_x` and `↓a_y` (x ≠ y) to nonempty sets
sends their product `↓⊥` to a nonempty set, so each point separates `↓⊥ ⊂ ↓a_x` for at most
one `x`; a conservative family would give an injection `Type w → ι` with `ι : Type w`.
In the source the site is a set and the sheaves take values in all sets, so the values
must lie in a universe containing `u`. The fix takes values and index in
`Type (max u w)`; the theorem docstring now carries the node's three proof steps, with
Step 3 indexing the points by the inverse systems of `C` (a set in universe `u`) instead
of by tuples of sheaves, which do not form a set in the value universe.
