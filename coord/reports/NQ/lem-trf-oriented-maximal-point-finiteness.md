## Worker report

The module `lean/Sheaf/Paper/OrientedMaximalPointFiniteness.lean` states
`AlgebraicGeometry.OrientedNearbyCycles.oriented_maximal_point_finiteness`.
It imports `Sheaf.Paper.OrientedNearbyCycles` for `VanishingTopos` and
`Sheaf.CategoryTheory.Sites.GeometricMorphism` for geometric morphisms. The
hypotheses render the node's Noetherian base as `[IsLocallyNoetherian S]`
and `[CompactSpace S]`, and its finite-presentation morphism as
`[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
The conclusion gives a finite type `ι` and representatives
`m : ι → GeometricMorphism (Type 0) (VanishingTopos f)`. For every `m i`,
any direct-image 2-morphism `q.direct ⟶ (m i).direct` has an inverse
isomorphism, expressing maximality on isomorphism classes. Every point `p`
has an index with a direct-image morphism `(m i).direct ⟶ p.direct`, which is
the inverse-image mate of the required 2-morphism from the maximal
representative to `p`. The existential finite type permits `ι = Empty`, so
the empty vanishing topos is covered. The proof is `sorry` as required for
stage 2, with the source and finite-poset argument recorded in the theorem
docstring.

Dependency declarations used:

- `AlgebraicGeometry.IsLocallyNoetherian` from Mathlib's
  `Mathlib.AlgebraicGeometry.Noetherian` (the `pqf-def-locnoeth` record).
- `CompactSpace` from `Mathlib.Topology.Defs.Filter` (the
  `def-weil-pbc-quasi-compact-scheme` record).
- The scheme and finite-presentation conventions are represented by the
  Mathlib classes `Scheme`, `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated`, as specified by `def-weil-pbc-scheme-conventions`.
- `AlgebraicGeometry.OrientedNearbyCycles.VanishingTopos` and its related
  construction from `Sheaf.Paper.OrientedNearbyCycles`.
- `CategoryTheory.GeometricMorphism` from
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`.

Edge cases checked: the empty vanishing topos is represented by an empty
finite index type; a singleton finite family gives the expected case where
there is one maximal class; repeated representatives are allowed by the
statement but maximality is explicitly only up to isomorphism; and the
2-morphism direction was checked against `GeometricMorphism.inverseMate`.

Searches for an existing declaration or definition found no exact match:

- `msearch.py ... leanfinder "The vanishing topos ... finitely many maximal points ..."` returned only ordinary Noetherian-space and generic-point declarations.
- `msearch.py ... loogle "Topos, Point"` returned no hits.
- `msearch.py ... grep "vanishing.?topos|oriented.?product|maximal.*topos"` returned no hits in Mathlib.
- `rg` over `WeilConjectures` and shared `lean/Sheaf` found only the oriented vanishing-topos construction and no maximal-point finiteness theorem.

No `STATEMENT-DISPUTED` issue or node fault remains.

## Second reading by NQ

I independently reread the copied node, its statement dependencies, and the
Lean file. The base hypotheses match the node clause by clause. The Lean
`Finite ι` records finiteness of the family of maximal representatives; the
first quantified clause says any point above a representative is isomorphic
to it, exactly the maximal-isomorphism-class condition. The second clause
supplies a representative above every point, and its direct-image arrow has
the required orientation because `inverseMate` reverses the direction. No
extra excellence, finite-type, or geometric-field choice hypothesis was
introduced, and the empty case is valid. I found no mismatch and made no
further changes.
