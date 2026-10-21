## Worker report

The new module `Sheaf.CategoryTheory.DerivedCategory.BoundedBifunctorDevissage` states
`DerivedCategory.bounded_bifunctor_devissage`, with its sole theorem proof `sorry`.
No definition, auxiliary theorem, dependency repair, or statement correction is needed.
The node copy changes only `lean`.

Source read: `literature/stacks-project/derived.tex`, Remark 08J5, especially the
successive-cohomology triangle with a=q-1. The node supplies the two finite inductions;
08J5 supplies their triangles rather than stating the bifunctor result verbatim.
The theorem docstring carries all five proof steps, including zero preservation,
cohomological endpoints, the successive triangle, induction in the second variable,
and then induction in the first variable.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- Abelian categories A and B: `(A : Type uA) [Category.{vA} A] [Abelian A]` and the
  corresponding binders for B. Each has its independently sized chosen derived category
  through `[HasDerivedCategory.{wA} A]` and `[HasDerivedCategory.{wB} B]`.
  All eight universes are explicitly bound; no equality of sizes is imposed.
- Standard t-structures: `DerivedCategory.TStructure.t (C := A)` and the analogous
  term for B are Mathlib's standard t-structures, not arbitrary t-structures.
- The triangulated category T: the explicit `Category`, `Preadditive`, `HasZeroObject`,
  `HasShift T ℤ`, additive shifts, `Pretriangulated`, and `IsTriangulated` instances
  are the data and axioms of the recorded Mathlib interface.
- The strictly full triangulated subcategory S: `S : ObjectProperty T`,
  `[S.IsTriangulated]`, and `[S.IsClosedUnderIsomorphisms]`. The last binder implements
  the item's strict fullness; Mathlib's triangulated property alone only supplies
  extension closure up to isomorphism. No thickness or direct-summand closure is assumed.
- The bifunctor named B in the prose is named F in Lean to avoid clashing with category B:
  `F : DerivedCategory A ⥤ DerivedCategory B ⥤ T`. This is the usual curried form of
  a functor from the product; functoriality in both variables is part of its data.
- Exactness with the first variable fixed: for every K,
  `(F.obj K).CommShift ℤ` and `(F.obj K).IsTriangulated`.
- Exactness with the second variable fixed: for every M,
  `(F.flip.obj M).CommShift ℤ` and `(F.flip.obj M).IsTriangulated`.
  The recorded exact-functor definition gives precisely shift compatibility and
  preservation of distinguished triangles; additivity follows, so it is not added
  as a further assumption. No compatibility between the two shift structures is imposed.
- Object classes: `A₀ : ObjectProperty A` and `B₀ : ObjectProperty B` are arbitrary
  predicates, without nonemptiness, zero membership, or isomorphism-closure assumptions.
- The degree-zero hypothesis is `h₀`: for every X and Y, `A₀ X → B₀ Y →`
  `S ((F.obj ((singleFunctor A 0).obj X)).obj ((singleFunctor B 0).obj Y))`.
  The single functors insert objects in degree zero in the actual derived categories.
- All bounded K and M: the binders range over the entire derived categories, followed
  by `hK : (TStructure.t (C := A)).bounded K` and the analogous `hM`.
  Mathlib defines `bounded` as the intersection of its plus and minus properties;
  these assert existence of a lower and an upper integer cohomological bound.
- Cohomology in the respective class only when nonzero: `hKA` and `hMB` quantify over
  every integer q and use `¬ IsZero ((homologyFunctor ... q).obj ...) →` membership
  in the corresponding predicate. They do not require the zero cohomology objects
  to belong to the classes.
- The conclusion is exactly `S ((F.obj K).obj M)`.
- The final sentence on zero objects and arbitrary finite intervals is retained by
  these binders: no positivity, nonzero input, nonempty class, or fixed interval is used.

Recorded dependency interfaces read and used:

- `def-sbc-standard-tstructure-derived-category`: `DerivedCategory.TStructure.t` in
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure`; its `isLE_iff` and `isGE_iff`
  identify the bounds with cohomology vanishing. `TStructure.bounded` is defined in
  `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`.
- `def-weil-triangulated-subcategory`: `CategoryTheory.ObjectProperty.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Subcategory`, supplemented by Mathlib's
  `ObjectProperty.IsClosedUnderIsomorphisms` for the item's strict fullness.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  `DerivedCategory.singleFunctor` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`,
  and `DerivedCategory.homologyFunctor` in its `HomologySequence` module. These are
  publicly available through the imported standard-t-structure module.
- `def-weil-triangulated-category`: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Triangulated`, and
  `CategoryTheory.Functor.IsTriangulated` in `Mathlib.CategoryTheory.Triangulated.Functor`,
  all available from the Mathlib imports. Exactness uses `Functor.CommShift ℤ` as
  required by this dependency's `mathlib_match`.
- Proof-only import `Sheaf.CategoryTheory.TruncationDescends` provides the recorded
  `DerivedCategory.truncation_descends` (lem-weil-pbc-truncation-descends).
- Proof-only import `WeilConjectures.CategoryTheory.TruncationTriangle` provides the
  recorded `DerivedCategory.truncation_triangle` (lem-weil-pbc-truncation-triangle).
  Both declarations and their proof docstrings were read. These imports implement the
  node's proof dependencies without adding them to the public statement interface.

Edge cases checked before writing:

- If either class is empty, the corresponding cohomology hypothesis forces every
  cohomology object to be zero. That derived object is zero, and exactness takes
  the pair to zero in S. The Lean condition is vacuous at zero cohomology.
- Zero and arbitrary acyclic inputs are allowed. No zero-membership assumption on
  either class is present, and S contains zero and is closed under isomorphisms.
- Single-degree cohomology in any integer degree follows by shifts from h₀.
- Support intervals may be entirely negative, cross zero, or start arbitrarily far
  in either direction. `bounded` only asks for some lower and upper integers.
- Gaps in either support invoke the zero case in the finite induction, not membership
  of zero in A₀ or B₀. No infinite tower or coproduct is required.
- A₀ and B₀ need not be isomorphism closed: the hypothesis uses the actual selected
  cohomology objects, while S absorbs the canonical comparison isomorphisms.

Searches (all through the prescribed msearch wrapper when a service is named):

- LeanFinder: “An exact bifunctor on derived categories lands in a triangulated
  subcategory on bounded pairs if it does so on pairs of their nonzero cohomology
  objects”. Eight hits: `Functor.map_distinguished_exact`, triangulated derived-functor
  instances, `Functor.isHomological_of_localization`, `Functor.IsHomological.exact`,
  the opposite distinguished-exactness lemma, `DerivedCategory.instIsTriangulated`,
  and `DerivedCategory.TStructure.t`. All are infrastructure, not this theorem.
- Loogle: `"IsTriangulated", "bounded"`. One hit:
  `CategoryTheory.Triangulated.TStructure.instIsTriangulatedBounded`. It says that
  bounded objects form a triangulated subcategory, not this two-variable result.
- Mathlib grep: `(bifunctor|Bifunctor).*(bounded|trunc)|(bounded|trunc).*(bifunctor|Bifunctor)`.
  Zero hits.
- LeanSearch: “A triangulated bifunctor sends bounded complexes to a triangulated
  subcategory if it sends every pair of their nonzero cohomology objects to that
  subcategory”. Eight hits, all exact-functor infrastructure: `Functor.IsTriangulated`
  and its constructor, projection, cases and additive instance, `Functor.map_distinguished`,
  and exact-functor triangulated instances. None is the requested bounded dévissage.
- The same regex was searched with rg in `lean/WeilConjectures` and `lean/Sheaf`.
  The hits concern tensor acyclicity, derived tensor, and bounded flat resolutions,
  not this abstract two-variable assertion. The existing
  `DerivedCategory.exists_iteratedExtensions_of_bounded` was also read: it assumes
  isomorphism closure of its coefficient predicate and all cohomology in that class,
  and does not state the bifunctor result.
- rg for the node id in `lean/WeilConjectures` gave zero hits. Searches for
  `bifunctor.*devissage|bounded_bifunctor|bifunctor_devissage` in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` gave zero hits.

Validation: scompile.py compiled both the isolated sandbox check and the actual
`Sheaf.CategoryTheory.DerivedCategory.BoundedBifunctorDevissage` module on the server
cleanly (1.8 s and 2.0 s respectively). There are no lines over 100 characters,
no auxiliary proofs, no auto-bound variables, and no warning or statement dispute.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
