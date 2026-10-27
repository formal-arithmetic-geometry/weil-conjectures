## Worker report

States `AlgebraicGeometry.exists_smooth_open_neighborhood_of_regular_stalkMap` in
`Sheaf.AlgebraicGeometry.RegularStalkSmoothNeighborhood`, with its sole proof `sorry`.
The node statement, dependencies, proof and other existing fields are unchanged; only
`lean` is recorded. There are no new definitions or dependency repairs.

Clause-by-clause comparison with the node:

- Schemes and morphism `f : X → Y`: `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`.
- Both schemes locally Noetherian: `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian Y]`, each explicit even though local finite presentation
  over the second also implies the first.
- The morphism locally of finite presentation: `[LocallyOfFinitePresentation f]`.
- An arbitrary point of the source: `(x : X)`.
- The point `y = f(x)` and the induced local homomorphism are rendered together by
  `f.stalkMap x : Y.presheaf.stalk (f x) ⟶ X.presheaf.stalk x`.
  Its `.hom` is the actual ring homomorphism; locality follows from the scheme
  morphism structure and is not replaced by an arbitrary map.
- Regularity of that homomorphism: `(hregular : (f.stalkMap x).hom.IsRegular)`.
  This uses the recorded definition: flatness plus Noetherian geometrically
  regular residue-field fibres, not regularity of the source or target ring alone.
- An open subscheme of X exists: `∃ U : X.Opens`.
- It contains x: `x ∈ U`.
- The restricted morphism to the original target is smooth:
  `Smooth (U.ι ≫ f)`, using the canonical open immersion `U.ι : U.toScheme ⟶ X`.
  The conclusion asks for neither an affine U nor a simultaneous smaller target.

Dependency declarations read and reused (full signatures and docstrings inspected):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Scheme.Hom.stalkMap`, and
  `AlgebraicGeometry.Scheme.Opens`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`:
  `AlgebraicGeometry.LocallyRingedSpace.Hom`, whose `prop` gives locality on stalks.
- `WeilConjectures.RingTheory.GRing`: `RingHom.IsRegular` and its component
  `Algebra.IsGeometricallyRegular`. This is the recorded upstream module, not
  the retired Sheaf twin.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  This is the current name in the pinned sources; remote semantic search results
  sometimes still call it `IsSmooth`.

Statement dependencies have public imports. Available proof dependencies have ordinary
imports: `Sheaf.AlgebraicGeometry.FibreStalkQuotient` (the canonical fibre stalk map
and `Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`),
`Mathlib.RingTheory.LocalRing.ResidueField.Fiber` (`Ideal.Fiber.algEquivAux₁`,
`Ideal.Fiber.algEquivQuotient`), `Mathlib.AlgebraicGeometry.Pullbacks`
(`Scheme.pullback_map_isOpenImmersion`, `pullbackSpecIso`, and the range formula
from its PullbackCarrier import), `Mathlib.RingTheory.FiniteStability`
(`Algebra.FinitePresentation.baseChange` and `Algebra.FinitePresentation.trans`),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`LocallyOfFiniteType`), and
`Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion`
(`smooth_at_point_iff_smooth_fibre_at_point`).
The proof-only node `lem-per-geometrically-regular-stalk-smooth-over-field` has no
recorded Lean module yet, so there is no module to import for that step. It is
named in the theorem's complete five-step proof docstring. Its statement is not
needed to elaborate this item's statement, so no duplicate or extra assumption
is introduced.

Source checks: read `morphisms.tex`, `lemma-smooth-at-point` (Tag 01V9), including
its flat-stalk plus smooth-fibre equivalence, and `varieties.tex`,
`lemma-geometrically-regular-at-point` and `lemma-geometrically-regular-smooth`
(Tags 038U and 038X). These agree with the node's proof and conclusion.

Edge cases checked before writing:

- The empty scheme has no point x; the point binder correctly makes this case
  vacuous. For an inhabited source, `x ∈ U` prevents choosing an empty U.
- No perfectness, characteristic, closed-point, residue-field separability,
  irreducibility, reducedness or positive-dimensional hypothesis is imposed.
- The stalk rings at actual scheme points are local rings, with their natural
  nontriviality; no artificial nonzero hypothesis is added.
- Identity morphisms and open immersions permit the expected whole-source
  neighbourhood. For a regular stalk map there is no assertion of regularity or
  flatness of every stalk on X: the hypothesis concerns this one x.
- The conclusion keeps Y as target. No quasi-compactness, separatedness,
  global finite presentation, or affine neighbourhood requirement is added.
- The common `Scheme.{u}` universe is the category's native universe convention,
  with explicitly bound `u`, X, Y, f and x. There is no independent test-object
  universe or hidden auto-implicit variable.

Searches for an existing exact declaration (2026-10-24):

- `msearch.py`, LeanFinder: “A locally finitely presented morphism of locally
  Noetherian schemes with regular local ring homomorphism at a point is smooth
  on a neighborhood of that point”. Eight results, including `isSmooth_iff`,
  standard smooth charts and stability properties; no regular-stalk criterion.
- `msearch.py`, LeanSearch: “A locally finitely presented morphism is smooth near
  a point if the homomorphism of local rings at the point is regular”. Eight
  results: smoothness definitions, local finite presentation, and ring-map
  smoothness. None states the item.
- `msearch.py`, Loogle: `AlgebraicGeometry.IsSmooth, RingHom.IsRegular` returned
  no results (its service did not know `AlgebraicGeometry.IsSmooth`). Repeated
  with the current pinned-source name `AlgebraicGeometry.Smooth`: twelve
  results defining smoothness or expressing composition/base-change/open-immersion
  stability, with no regular-stalk theorem.
- `msearch.py`, grep in `AlgebraicGeometry/Morphisms`:
  `regular.*smooth|smooth.*regular|IsRegular`: no hits.
- Local `rg` in Mathlib, `lean/WeilConjectures` and `lean/Sheaf`:
  `stalkMap.*IsRegular|RingHom.IsRegular.*stalkMap|exists_smooth.*regular|smooth.*of_regular_stalk`.
  Only a regular-pullback predicate and its converse characterization in
  `RegularPullbackUnresolvedStrata` mention regular stalk maps; neither gives this
  locally-finitely-presented smooth-neighbourhood implication. Broader searches
  for regularity and smoothness found existing ascent, field, and formal-geometry
  material, with different hypotheses and conclusions.
- Exact blueprint-id search in `lean/WeilConjectures`: no hits.

No statement dispute or source correction was necessary. Compilation and delivery
preflight are run using the prescribed wrappers; only expected sorry warnings
are accepted.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
