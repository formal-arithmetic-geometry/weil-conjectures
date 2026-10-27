## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUnramifiedRadicialParameterOpen` states
`AlgebraicGeometry.AlgebraicSpace.exists_openSubspace_unramified_radicial_parameter`.
Its only theorem has the prescribed `sorry` proof. Two auxiliary definitions contain
real data: `parameterBaseChange` bundles the existing sheaf fibre product using its
proved-property interface, and `parameterBaseChangeMap` is the categorical
`pullback.map` with components f and the identity on the parameter. These are helpers
for the map explicitly mentioned in this node, not independently assumed maps or new
mathematical notions. All three declarations are in `lean.declarations`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; A, C, B and every parameter are `AlgebraicSpace S`
  in that same scheme universe, following the recorded algebraic-space convention.
  There is no independent, potentially smaller universe of tests.
- The three maps are `p : A ⟶ B`, `q : C ⟶ B`, `f : A ⟶ C`; commutativity is
  `w : f ≫ q = p` (categorical composition is written left-to-right).
- Local finite type of p is exactly `MapIsLocally (@LocallyOfFiniteType) p`, the
  recorded all-compatible-etale-chart test, without quasi-compactness.
- Closedness of p is `IsClosedMap (mapPoint p.hom.hom)`.
- Closedness of p2 is
  `IsClosedMap (mapPoint ((pullback.fst f.hom f.hom) ≫ p.hom).hom)`.
  This is the first projection from the sheaf square A ×_C A followed by p.
  Neither closedness hypothesis is strengthened to universal closedness.
- The required open is `∃ V : OpenSubspace B`, the recorded representably open
  subfunctor. No separate choice of a point subset substitutes for this subspace.
- The universal property binds `∀ (T : AlgebraicSpace S) (h : T ⟶ B)`.
- Its canonical f_T is `parameterBaseChangeMap p q f w h`, between the bundled
  sheaf pullbacks A ×_B T and C ×_B T.
- Unramifiedness is `MapIsLocally (@IsUnramified)` of that exact map. The dependency's
  `IsUnramified` is locally finite type plus its scheme open diagonal.
- Universal injectivity is expanded directly: for every algebraic space Y and map
  `g : Y ⟶ parameterBaseChange q h`, the point map of the second projection from
  the pullback of f_T along g is `Function.Injective`. This includes arbitrary Y,
  the identity test, and empty tests. It is not sectionwise injectivity or only a
  scheme-target test.
- The conjunction of those properties is equivalent to
  `∃ l : T.obj.obj ⟶ V.val.toFunctor, l ≫ V.val.ι = h.hom.hom`.
  These are the same natural transformations as morphisms of the full subcategory;
  an open subfunctor is automatically a space. The node only asks for factorization,
  so no extra uniqueness or representability clause is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace` and its fppf-sheaf,
  representable-diagonal and etale-atlas definition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, used to bundle the actual sheaf pullback.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`;
  `mapPoint` comes through the morphism-properties module from
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `IsUnramified`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `def-weil-size-convention` is metatheoretic; explicit `universe u` and the recorded
  scheme and algebraic-space categories implement it.

Already stated proof dependencies are imported without `public`:
`AlgebraicSpaceOpenFactorSchemeTests`, `SpaceInvariantOpenQuotient`, and
`AlgebraicSpacePointOpenCalculus`. The fibre-product and open-subspace proof dependencies
are already public statement imports. The two proof-only nodes
`lem-sfb-space-closed-source-unramified-base-open` and
`lem-sfb-space-unramified-diagonal-open` have no recorded Lean module in the read snapshot,
so no fictional import is supplied. They are named in the complete six-step proof
in the theorem docstring. No missing notion or dependency repair was required.

Source check: read `literature/stacks-project/spaces-more-morphisms.tex`,
`lemma-where-unramified-universally-injective` (Tag 05X9), lines 11565–11640.
All three hypotheses and arbitrary algebraic-space parameter changes agree. The node's
six-step proof is included in the declaration docstring, including the open restriction
of a closed map and the point-surjective-diagonal criterion.

Edge cases checked before writing: empty A (the represented condition is everywhere);
empty B (all spaces mapping to B are empty); empty T (both properties and factorization
hold); identity f (the represented condition is everywhere); nontrivial finite separable
field extension (unramified need not be universally injective, so the second conjunct
cannot be dropped); closed maps that are not universally closed (no extra base-change
closedness was imposed). There are no characteristic, separation, nonemptiness, finite
presentation or quasi-compactness assumptions.

Searches for an existing statement and canonical helpers:

- `msearch.py ... leanfinder` query: “An open subset of an algebraic space base
  represents simultaneous unramifiedness and universal injectivity after arbitrary
  parameter change”. Eight results, including scheme `UniversallyInjective`,
  `FormallyUnramified`, `IsEtale`, `Scheme.Etale`; none gives this space parameter open.
- `msearch.py ... leansearch` query: “An open locus in an algebraic space parameterizes
  unramified and universally injective base changes”. Eight results, affine ring
  `unramifiedLocus` and scheme `FormallyUnramified`/`UniversallyInjective`; no match.
- `msearch.py ... loogle` query:
  `AlgebraicGeometry.UniversallyInjective, AlgebraicGeometry.IsUnramified`.
  No hits, unknown identifier `AlgebraicGeometry.IsUnramified` in the search service;
  the actual project declaration was read in `UnramifiedMorphism.lean` and used.
- `msearch.py ... grep` query `AlgebraicSpace|where.*[Uu]nramified|[Rr]adicial`,
  subdirectory `AlgebraicGeometry`: zero Mathlib hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `parameterBaseChange`, `MapIsUniversallyInjective`, `MapIsUnramified`,
  `unramified_radicial_parameter`, `where_unramified`, and unramified/universally
  combinations: no duplicate general-space theorem or helper. The existing
  `UniversalUnramifiedRadicialOpen.lean` theorem was opened and is only for schemes.
  `SpaceMapIsUnramified` in `OpenModuliSubstack` has a scheme target, so the general
  `MapIsLocally` interface is used here. The existing universal-isomorphism-open
  theorem also uses the same canonical `pullback.map` formula.
- Searched the item's exact id in `lean/WeilConjectures`: no declaration.

No statement correction, disputed statement, new node, or dependency module.

## Second reading by Q02

A second sequential reading of the finished file against the node checked the actual
signatures and bodies of the two helper definitions and all clauses listed above.
The dispatcher expressly prohibits starting another agent; this section records the
worker's cross-check and does not claim an independent reviewer. The maintainer's
independent review remains the delivery review.

The check confirmed the order of the triangle equality, the first projection in p2,
the second projection in every universal-injectivity test, the target C ×_B T of the
canonical f_T, and equality with h after the open inclusion. Both closedness assumptions
are ordinary closedness. Universally injective quantifies over spaces over the same S,
not over a smaller test universe. Every hypothesis and both conclusions match the node;
no mismatch or change to the node's statement was needed. The sole postponed theorem
is exactly the assigned DAG node. The helper definitions have no postponed data or new
proof obligations.
