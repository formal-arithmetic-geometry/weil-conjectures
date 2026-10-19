## Worker report

The delivery states `AlgebraicGeometry.schemeTheoreticImage_reduced` in
`Sheaf.TraceFormula.ReducedSchemeImage`.  It uses Mathlib's canonical
scheme-theoretic image `f.image` and closed immersion `f.imageι`.

The item hypotheses and clauses are rendered as follows.  The schemes and
morphism are `(U X : Scheme.{u}) (f : U ⟶ X)`, and reducedness of the source is
the typeclass hypothesis `[IsReduced U]`.  The phrase “scheme-theoretic image”
is rendered by `f.imageι` together with `IsClosedImmersion f.imageι`.  The
assertion that the image is reduced is `IsReduced f.image`.  The assertion
that its closed subscheme structure is the reduced induced structure on the
closure is the ideal-sheaf equality
`f.ker = vanishingIdeal (TopologicalSpace.Closeds.mk (closure (Set.range f))
isClosed_closure)`.  The underlying topological support clause is
`Set.range f.imageι = closure (Set.range f)`.  Finally, for every closed
immersion `i : Z ⟶ X`, a factorization `∃ g : U ⟶ Z, g ≫ i = f` implies the
unique factorization `∃! h : f.image ⟶ Z, h ≫ i = f.imageι`; this is the
minimality clause in the definition of scheme-theoretic image.

The statement imports and uses these dependency declarations:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom` from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-reduced-scheme`: Mathlib class `AlgebraicGeometry.IsReduced` from
  `Mathlib.AlgebraicGeometry.Properties`.
- `def-weil-closed-immersion`: Mathlib class
  `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`
  from `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`.

The proof plan also uses the recorded declaration
`AlgebraicGeometry.reduced_source_factors_through_closed_subscheme` from
`Sheaf.Paper.ReducedSourceFactors`, corresponding to the proof dependency
`lem-weil-pbc-reduced-source-factors-through-closed-subscheme`.  The module is
imported so stage 3 has the planned factorization interface available.

Edge cases checked before writing the statement were an empty reduced source
(the range and its closure are empty), a constant map (the closure is the
single image point), a closed reduced immersion (the image is already closed),
and a dense open immersion (the closure is the whole target).  The universal
factorization clause also covers an empty image and the identity closed
immersion.  No quasi-compactness hypothesis was added, since Tag 056B states
the result for an arbitrary morphism of schemes.

Searches made:

- `msearch.py Q43 lem-trf-reduced-scheme-image leanfinder` with the plain
  statement “The scheme theoretic image of a morphism from a reduced scheme is
  the reduced induced closed subscheme on the closure of its image”: no exact
  match; hits concerned `Scheme.Hom.image`, normalization, and reducedness.
- `msearch.py ... loogle` for `AlgebraicGeometry.IsReduced,
  AlgebraicGeometry.Scheme.Hom.image`: no exact match.
- `msearch.py ... grep` for image/reducedness combinations in
  `AlgebraicGeometry/IdealSheaf`: no theorem stating this result.
- `rg` over Mathlib and `WeilConjectures/` for scheme-theoretic-image and
  reduced-image names: only Mathlib's canonical `Hom.image`, `Hom.imageι`,
  and support lemmas were found; no duplicate project theorem exists.
- `rg` over `lean/Sheaf` for the item id and reduced scheme image: no existing
  stage-2 declaration was found.

No statement correction or new node was needed.  The prior Q25 commit was only
the stage-1 split and had no `lean` record; the live node remained `status:
split`, so this is the first stage-2 statement delivery.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
