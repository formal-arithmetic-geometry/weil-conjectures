## Worker report

The module `Sheaf.AlgebraicGeometry.QcSpaceAffineEtaleAtlas` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_atlas_of_compactSpace`.
Its sole theorem has proof `by sorry`; it introduces no definitions or extra theorems.

Source read: `literature/stacks-project/spaces-properties.tex`, lines 747–773,
Tag 03H6, `lemma-quasi-compact-affine-cover`, forward implication. The source's
statement says étale surjective. Its proof's last sentence says “finite surjective”,
a typo already identified in the node's accepted split; this delivery follows the
statement and does not claim finiteness. The existing accepted statement is unchanged.

Clause-by-clause rendering:

- An arbitrary scheme `S` is `{S : Scheme.{u}}`. An algebraic space over it is
  `(X : AlgebraicSpace S)`, using the recorded fppf-sheaf full subcategory, with
  representable diagonal and a representable surjective étale scheme atlas.
- The size convention is explicit `universe u`: schemes, fields, and sheaf values
  are at level `u`, while the existing `Point X.obj.obj` lives in `Type (u + 1)`.
  There is no independent smaller universe for field-valued tests or extra bound.
- The stipulated field-valued point classes are exactly `Point X.obj.obj`, using
  `PointRepresentative.Rel` and `Quot` from the recorded point-class interface.
- Their topology is the existing `pointTopologicalSpace` instance, imported
  publicly from `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`. This is the
  final topology for all representable étale scheme maps, and agrees with the
  quotient topology of any surjective étale atlas. In the cover theorem, the
  supplied quotient topology makes every scheme-source point map continuous;
  it therefore equals this final topology. No arbitrary topology or atlas is a
  new hypothesis. The existing node `def-a1-space-point-topology` was added to
  `stmt_deps` under the rule permitting added landed statement dependencies.
- Quasi-compactness of this topology is `(hX : CompactSpace (Point X.obj.obj))`.
  Mathlib compactness means finite subcovers of arbitrary open covers; it adds
  no Hausdorff condition. The explicit proof argument is the sole finiteness
  hypothesis on `X`.
- The sought scheme over `S` is `∃ (W : Over S)`. Its underlying scheme is
  `W.left` and its structural morphism is `W.hom`.
- The map `h_W → X` is `(p : yoneda.obj W ⟶ X.obj.obj)` on the category `Over S`.
  It is therefore a morphism over the given base, not an arbitrary absolute map.
- Absolute affineness is `IsAffine W.left`, not affineness of `W.hom`. Mathlib's
  class supplies `W.left.isoSpec : W.left ≅ Spec Γ(W.left, ⊤)`; conversely a
  scheme isomorphic to a spectrum has this class.
- Representability, surjectivity, and étaleness are respectively
  `IsRepresentable p ∧ IsSurjective p ∧ IsEtale p`, exactly the recorded predicates
  defined by representing every scheme test pullback and checking its projection.
- There is no separatedness, quasi-separatedness, noetherianity, nonemptiness,
  affineness of `S`, or relative-affineness assumption. There is no extra conclusion.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphism
  structure `AlgebraicGeometry.Scheme.Hom` (lines 35–46 and 71–75).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, `IsSurjective`, and
  `IsEtale`; their full definitions and source docstrings were read. The étale
  predicate uses `AlgebraicGeometry.Etale` on each representing projection.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`,
  its docstring and complete class signature (lines 37–44).
- `def-weil-size-convention` is a convention record with no declaration, rendered
  through explicit universe polymorphism, as its record instructs.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `PointRepresentative`,
  `PointRepresentative.Rel`, `Point`, and `schemePointMap`, all read in full.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`, read in full with
  its final/atlas-topology docstring. This is an existing landed definition node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover`:
  `AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_cover_and_point_topology`.
  Its full signature and proof docstring supply proof step 1 and the stipulated
  point topology; it is a public import because it is also a statement dependency.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFiniteAffineSubatlas`:
  `AlgebraicGeometry.AlgebraicSpace.exists_finite_affine_subatlas`, read in full.
  Its compactness hypothesis uses the same point topology, and its finite open
  component union gives proof step 2. This is an ordinary proof-only import.
- `Mathlib.AlgebraicGeometry.Limits`: `AlgebraicGeometry.sigmaSpec`,
  `AlgebraicGeometry.ι_sigmaSpec`, and the finite-index `IsIso (sigmaSpec R)`
  instance (lines 604–647), read for the Mathlib proof-dependency node
  `lem-weil-pbc-finite-affine-coproduct-spectrum`. Ordinary proof-only import.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffine` and
  `AlgebraicGeometry.Scheme.isoSpec` (lines 58–70), giving exactly absolute
  affineness. No private copy of any notion is introduced.

The theorem's docstring reproduces the three accepted proof steps: choose the
existing disjoint-affine atlas, select a finite component subatlas using compactness,
and identify that finite coproduct with the spectrum of a product ring. All stated
proof dependencies are imported. No proof dependency interface needed repair.

Edge cases checked before writing:

- Empty `X`: no `Nonempty` hypothesis occurs. The finite component family can be
  empty, giving the empty scheme `Spec 0` with its unique structure morphism to `S`.
- The zero ring is allowed; neither the statement nor `IsAffine` requires a domain
  or a nontrivial ring. Empty affine components cause no restriction.
- An infinite initial atlas is allowed; only a finite selected subfamily is used.
- Arbitrary nonseparated or non-quasi-separated spaces and arbitrary bases remain
  in scope: neither the signature nor the three proof steps uses intersections
  of affine opens or a separatedness class.
- When `X` is already affine, its identity atlas witnesses the conclusion. The
  assertion concerns compactness of the point space, not compactness of an
  identity scheme morphism or an arbitrary map predicate.

Searches actually run for existing notions/statements:

- `msearch.py ... leanfinder "A quasi compact algebraic space over a scheme admits
  a surjective etale morphism from an affine scheme"`: 8 results. The closest,
  `Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`, has a scheme target;
  `compactSpace_iff_exists` also has a scheme target and does not assert étaleness.
  Read their signatures in `Morphisms/Descent.lean:48–59` and
  `Morphisms/QuasiCompact.lean:196–201`. They do not state this node.
- `msearch.py ... loogle '"IsAffine", "CompactSpace"'`: 2 results,
  `Scheme.compactSpace_of_isAffine` and an affine-transition-limit instance;
  neither provides an algebraic-space atlas.
- `msearch.py ... grep 'AlgebraicSpace|affine.*[ée]tale.*atlas|quasi.compact.*affine.*cover'
  AlgebraicGeometry`: 3 description hits in scheme covering/site files, no match.
- `msearch.py ... leansearch "A quasi compact algebraic space has a representable
  surjective etale atlas from an affine scheme"`: 8 results, all scheme
  compactness/quasi-separatedness statements, no algebraic-space atlas assertion.
- `rg` of `lean/WeilConjectures` and `dag/lean_names_upstream.json` for
  `AlgebraicSpace`, the item id, and the proposed declaration name found no match.
- `rg` of `lean/Sheaf/AlgebraicGeometry` for `CompactSpace (Point`, affine-atlas
  names, and affine atlas-source clauses found the existing point-space interfaces
  used here. Read `AlgebraicSpaceEtaleOpenImage.points_compactSpace_iff`: it gives
  a compact scheme atlas, not an affine one. Read
  `AlgebraicSpaceAffineAtlasOpenCover.exists_affine_atlas_open_cover`: it gives
  a family of open subspaces with affine atlases, not one affine atlas of a compact
  target. The disjoint-affine atlas and finite-subatlas declarations likewise
  do not already state the requested absolute-affine conclusion.
- The proposed full declaration name was also checked in Mathlib/project source
  searches. The retired example `Sheaf.CategoryTheory.CompactObject` contains no
  declarations; its node now points to `WeilConjectures.CategoryTheory.CompactObject`,
  whose header, docstring and universe-polymorphic signature were read instead.

No disputed statement, statement correction, new definition node, or dependency
module is needed. Only the item's `lean` and the added landed topology dependency
change; the accepted statement, proof, and remaining node fields are preserved.

Validation: the prescribed `scompile.py Q151 lem-sfb-qc-space-affine-etale-atlas`
compiled the delivered module both as a sandbox probe (15.8 s) and under its actual
library module name (5.1 s), with no errors or unexpected warnings. `autoImplicit`
is explicitly disabled. Every variable and universe is bound, and every line of
the delivered Lean file is at most 100 characters. Delivery dry-run results follow.

The prescribed `deliver2.py ... --no-push` completed successfully:
`OK (dry run): commit ef0777e674b passes the preflight and compiles; nothing pushed`.
The delivery wrapper provides the independent-review placeholder; the worker did
not fabricate a second-reader report or start other agents.

## Second reading by Q151

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
