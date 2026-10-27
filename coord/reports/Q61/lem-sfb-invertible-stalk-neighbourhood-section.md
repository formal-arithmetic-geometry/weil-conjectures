## Worker report

The new module `Sheaf.AlgebraicGeometry.InvertibleStalkNeighbourhoodSection` states
`AlgebraicGeometry.Scheme.exists_neighbourhood_section_of_isIso_stalkMap`, with its proof
left as `sorry`. It defines no new notion. The node is unchanged except for `lean`.

The source was read in `literature/stacks-project/varieties.tex`,
`lemma-modification-normal-iso-over-codimension-1`, proof (4) (Tag 0BFP), and
`literature/stacks-project/morphisms.tex`, `lemma-morphism-defined-local-ring`, (2)(c)
(Tag 0BX6). The first source explicitly constructs the section inducing the given local
isomorphism; the second supplies spreading under exactly the hypotheses of this node.

Every hypothesis and clause has the following rendering:

- Schemes X and Y: `{X Y : Scheme.{u}}`, with the universe explicitly bound by `universe u`.
- Locally Noetherian base: `[IsLocallyNoetherian X]`.
- Morphism from Y to X: `(f : Y ⟶ X)`.
- Locally of finite type: `[LocallyOfFiniteType f]`; no quasi-compactness is assumed.
- Point y and x = f(y): `(y : Y)`, writing `f y` everywhere for x.
- The induced local ring map is an isomorphism: `[IsIso (f.stalkMap y)]`.
  Scheme morphisms already induce local ring homomorphisms, so no additional locality
  hypothesis is introduced.
- An open neighbourhood of x: `∃ (W : X.Opens) (hx : f y ∈ W)`.
- A morphism s from that open to Y: `(s : W.toScheme ⟶ Y)`.
- The section goes through y: `(hy : s ⟨f y, hx⟩ = y)`. This is an existential proof
  binder, needed to transport the source of its stalk map; it is not a hypothesis on f.
- Composition with f is the inclusion: `s ≫ f = W.ι`.
- The stalk map is precisely the inverse, under the canonical identification:
  `(Y.presheaf.stalkCongr (Inseparable.of_eq hy)).inv ≫
  s.stalkMap ⟨f y, hx⟩ ≫ (W.stalkIso ⟨f y, hx⟩).hom = inv (f.stalkMap y)`.
  The first factor has source O_{Y,y} and target O_{Y,s(x)} and merely transports the
  point equality hy. The last factor is Mathlib's canonical O_{W,x} ≅ O_{X,x}.
  Both sides therefore map O_{Y,y} to O_{X,x}, with no arbitrary ring identification.
- The equivalent section of the restriction is exhibited for this same s:
  `∃ t : W.toScheme ⟶ (f ⁻¹ᵁ W).toScheme,
  t ≫ (f ⁻¹ᵁ W).ι = s ∧ t ≫ (f ∣_ W) = 𝟙 W.toScheme`.
  Thus the factorization is tied to s, and its projection to W is the identity.

The four statement-dependency records and the full signatures/docstrings were read:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian` (the every-affine-open form, equivalent to the
  affine-cover formulation in the node).
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` (only the locally-finite-type clause is used).
- `def-weil-locally-ringed-space-morphism`:
  `Mathlib.Geometry.RingedSpace.LocallyRingedSpace`,
  `AlgebraicGeometry.LocallyRingedSpace.Hom`; the stalk map is the inherited
  `AlgebraicGeometry.Scheme.Hom.stalkMap` in `Mathlib.AlgebraicGeometry.Scheme`.

`Mathlib.AlgebraicGeometry.Restrict` additionally provides `Scheme.Opens.stalkIso`,
`Scheme.Opens.ι` and `morphismRestrict` for the canonical objects in the conclusion;
no new definition is needed. `TopCat.Presheaf.stalkCongr` is Mathlib's canonical
isomorphism on inseparable points, here applied only to equal points.

All stated proof dependencies are imported: `SpecToEquivOfLocalRing` from
`Mathlib.AlgebraicGeometry.Stalk`; `Scheme.fromSpecStalk_local_properties` from
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`;
`Scheme.Hom.stalkMap_comp` and `Scheme.Hom.germ_stalkMap` from
`Mathlib.AlgebraicGeometry.Scheme`; `spread_out_of_isGermInjective'` from
`Mathlib.AlgebraicGeometry.SpreadingOut`; `CategoryTheory.Limits.pullback` and its
projections from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
`AlgebraicGeometry.isPullback_morphismRestrict` from
`Mathlib.AlgebraicGeometry.Restrict`. Imports needed in the statement are public;
remaining proof imports are plain imports. The docstring reproduces all three proof
steps, including construction of the local inverse and the equivalent factorization.

Edge cases checked before writing: the empty source scheme is covered vacuously by the
point binder, and a target with a point f(y) cannot be empty; hx ensures W is nonempty.
For an identity morphism take the whole scheme and its identity section, with stalk
maps transported by the canonical open-stalk isomorphism. For an open immersion take
an open neighbourhood inside its image. Other points can lie above x, so neither
uniqueness of the fibre point nor uniqueness of the section is asserted. No separation,
properness, reducedness, normality, global Noetherianness, characteristic, or finite-type
(rather than locally-finite-type) assumption has been added. No independent test-object
universe is introduced: these are morphisms in the usual category of u-small schemes.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder`: query "An isomorphism on stalks for a locally finite type
  morphism over a locally Noetherian scheme extends to a neighbourhood section with
  inverse stalk map". Eight hits, led by `spread_out_of_isGermInjective'` and
  `spread_out_of_isGermInjective`. Their complete signatures were read; they assume
  a compatible local map or a map from Spec of a stalk and conclude its spreading,
  rather than the full inverse-stalk section statement with the specified point.
- `msearch.py ... leansearch`: query "A locally finite type scheme morphism with an
  isomorphism on a stalk has a section through that point on an open neighbourhood of
  its image". Eight hits: the unprimed spreading theorem, stalk isomorphisms for open
  immersions and restrictions, and local-isomorphism predicates. No full match.
- `msearch.py ... loogle`: query `"AlgebraicGeometry.Scheme.Hom.stalkMap", "IsIso"`.
  Zero hits.
- `msearch.py ... grep`: query `spread|exists.*[Ss]ection|stalkMap.*[Ii]so` in
  `AlgebraicGeometry`. Twenty-five hits including `SpreadingOut.lean`, `Stalk.lean`,
  `Restrict.lean`, and `OpenImmersion.lean`; none states the entire node.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and for
  `exists.*[Ss]ection|stalkMap.*[Ii]so`, then the narrower patterns
  `section.*[Ii]so.*stalk|[Ii]so.*stalk.*section`, found no matching statement.
  Nearby section results concern torsors, sheaves, or affine smooth coordinates.
- `rg` of Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the proposed full declaration's short name found
  no collision. The recorded CompactObject example was read: it is now a withdrawn
  module, so the current module-mode conventions in the standing brief were followed.

No disputed statement, corrected statement, new node, or dependency repair was needed.

## Second reading by Q61

A separate pass by the same worker reread the node and the complete file. No other
agent was started, as the dispatcher brief requires; independent maintainer review is
still required. This pass checked all binders and conclusions: local Noetherianness
is on X, local finite type is on f, the point is in Y, and IsIso refers to f's stalk
map at that exact point. The existential hx defines the point in the open subscheme.
The existential hy points from s(x) to y, so the inverse of stalkCongr has exactly the
source O_{Y,y} required for the inverse formula. W.stalkIso points from the open stalk
to the ambient stalk; its hom, not its inv, belongs at the end. The two resulting
maps have the same source and target as inv (f.stalkMap y). The final factorization
uses the same W and s and is a section of the actual restriction of f. Every clause
of the node is present, with no additional mathematical assumption. No mismatch was
found on this pass, and no statement change was made.
