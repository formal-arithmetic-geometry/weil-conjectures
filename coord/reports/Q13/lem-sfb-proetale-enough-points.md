## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints` states
`AlgebraicGeometry.proEtale_enoughPoints`, with its proof postponed by `sorry`.
The node is unchanged except for its `lean` field. No definitions, auxiliary
theorems, dependency repairs, or new nodes are needed.

Hypotheses and conclusions, clause by clause:

- Any scheme X: `(X : Scheme.{u})`, with no quasi-compactness, separatedness,
  nonemptiness, affineness, or field hypothesis.
- Its small pro-etale site: `Scheme.ProEt.topology X`, on Mathlib's `X.ProEt`.
  Objects have universe `u + 1`, and morphisms have universe `u`. The sheaves
  have values in `Type (max (u + 1) v)`, so their universe contains the site's
  object universe, for every additional universe `v`. This implements the
  node's compatible-universe convention without equating the site universes.
  The category is small at this larger level and a skeleton may be chosen
  there; working on the equivalent full site does not require choosing one
  as additional data.
- A set-indexed family: `∃ (ι : Type (max (u + 1) v)) (p : ι → ...)`.
  There is no `Nonempty ι` requirement.
- Points from Set to the sheaf topos:
  `GeometricMorphism (Type (max (u + 1) v))
  (Sheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v)))`.
  The recorded geometric-morphism structure supplies inverse image, direct
  image, their adjunction, and preservation of finite limits by inverse image.
- Every morphism of sheaves of sets: the implicit binders `F G : Sheaf ...`
  and the explicit binder `(a : F ⟶ G)`.
- Bijectivity of each inverse image: `∀ i, Function.Bijective
  ((p i).inverse.map a)`.
- Joint reflection of isomorphisms: the preceding condition implies
  `IsIso a`. Since functors preserve isomorphisms and isomorphisms of types
  are bijections, this is also the usual conservative-family criterion.
- Arbitrary topos points, with no assertion that they are geometric points
  of X: `p` ranges over the recorded geometric-morphism structure; neither
  a field-valued point nor a scheme-stalk construction is imposed.

Statement dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`, re-exported by the pro-etale-site import.
  Read the structure, local affine condition, and morphism signature.
- `def-weil-pbc-proetale-site`: its repaired record names
  `AlgebraicGeometry.Scheme.ProEt`, from
  `Mathlib.AlgebraicGeometry.Sites.Proetale`; its topology is `Scheme.ProEt.topology`.
  Read the full definition and its weakly-etale/fpqc precoverage definitions.
- `def-trf-geometric-morphism`: `CategoryTheory.GeometricMorphism`, from
  `Sheaf.CategoryTheory.Sites.GeometricMorphism`. Read all four fields and
  the source docstring, as well as its composite construction. This is used
  directly, with the source and target categories in the node's direction.

The module docstring reproduces all five proof steps from the node, naming
their dependencies. Available proof dependencies are imported without `public`:
the affine fibre-product module, the terminal/pullback finite-limit criterion,
sheafification, site-covering axioms, and ind-etale stability. Scheme, spectrum,
pullbacks, weakly-etale-between-objects and the site are already covered by these
imports. The two new proof-only dependencies
`lem-sfb-proetale-affine-subsite-equivalence` and
`lem-sfb-site-finitary-slice-enough-points` have no recorded Lean modules yet;
their imports can be added when they are stated. Neither is required to type
this statement, and no cyclic or invented import is introduced.

Sources read: Stacks `proetale.tex`, `lemma-points-proetale` (0992), which
asserts enough points for the small site for every scheme; and
`lemma-alternative` (098W), used by its proof. The extra warning in the node
about ordinary geometric points is respected by quantifying arbitrary
geometric morphisms.

Edge cases checked before writing:

- The empty scheme is admitted. Its sheaf topos is degenerate; the empty
  family is allowed, and all of its sheaf morphisms are isomorphisms.
- Non-quasi-compact and nonseparated schemes are admitted; the proof works
  on affine slices and does not ask X itself to be affine or coherent.
- Empty covering families and empty point-index types are not excluded.
- Sheaf values never lie in a universe below the site's object universe.
- A type-valued inverse-image map is a function, so bijectivity has exactly
  the meaning in the node. No additive or module coefficients are substituted.

Searches made with the prescribed tools:

- `msearch.py leanfinder`: “For every scheme its small pro-etale topos has a
  set indexed conservative family of geometric points”. Eight hits, all
  ordinary etale-site definitions/instances; no matching pro-etale theorem.
- `msearch.py leansearch`: “The small pro-etale topos of every scheme has
  enough points”. Eight hits, ordinary etale-site and scheme infrastructure;
  no matching theorem.
- `msearch.py loogle`: `GrothendieckTopology.Point, Sheaf`. No hits; the
  service reports the identifier `GrothendieckTopology.Point` unknown.
- `msearch.py grep`: `EnoughPoints|enough.points|ProEt.*Point`, restricted to
  `AlgebraicGeometry/Sites`. One hit, the enough-points instance for the
  ordinary small etale topology in `EtalePoint.lean`; it does not state the item.
- Direct `rg` over the source project's `WeilConjectures` and the side
  project's `lean/Sheaf` for enough points and pro-etale points: no matching
  statement. The existing `finitarySite_enoughPoints` in
  `Sheaf.Paper.FinitarySiteEnoughPoints` is a generic finite-limit/finite-cover
  site criterion, not the assertion for arbitrary schemes' pro-etale sites.
  Existing geometric-stalk conservativity files concern different points
  or restricted coefficients and are not this arbitrary-topos-point theorem.
- Direct `grep -rn` for this node id in source `WeilConjectures`: no hits.
- Direct `rg` of the side-only upstream framework and upstream declaration
  index for the enough-points theorem: no matching declaration.

No mathematical statement fault or disputed clause was found. The previous
worker's report concerned a refusal to re-split a reviewed stage-1 node. This
delivery retains that split and only supplies its stage-2 Lean statement.

## Second reading by Q13

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
