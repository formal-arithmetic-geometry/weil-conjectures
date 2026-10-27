## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineLimits` states
`AlgebraicGeometry.AlgebraicSpace.exists_affine_limit_eventually_schematic`.
Its only theorem has proof `sorry`. No definitions, helper theorems, dependency repairs,
or statement corrections are introduced.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`.
- The small nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Its universe agrees with that of the schemes;
  no antisymmetry or extra size equality is assumed.
- The inverse system of algebraic spaces over S is `D : Iᵒᵖ ⥤ AlgebraicSpace S`.
- Affine transitions are `haff : ∀ {i j} (a : i ⟶ j), MapIsAffine (D.map a)`.
  This is the existing affine-scheme-test predicate, including the representing
  pullback square. Representability on arbitrary scheme tests follows by gluing their
  affine open restrictions; it imposes exactly the node's affine condition.
- The algebraic-space limit is the apex of `∃ c : Cone D`. The clause
  `Nonempty (IsLimit ((ObjectProperty.ι IsAlgebraicSpace).mapCone c))` asserts the
  universal property in fppf sheaves. Thus this is not merely a limit in the full
  subcategory of algebraic spaces.
- Each projection is affine: `∀ i : Iᵒᵖ, MapIsAffine (c.π.app i)`.
- The node's quasi-compactness definition is expressed literally in the antecedent:
  for every i there are `U : Over S` and `a : yoneda.obj U ⟶ (D.obj i).obj.obj`
  with `CompactSpace U.left ∧ IsEtale a ∧ IsSurjective a`.
- The node's quasi-separatedness is `∀ i, IsAbsolutelyQuasiSeparated (D.obj i)`.
  This existing predicate uses the equivalent affine-pair test for the absolute
  diagonal (Stacks 0AHR). It does not impose quasi-separatedness of S and does not
  mistakenly replace the absolute diagonal by the diagonal relative to S.
- Only the two eventual conclusions are under the qcqs antecedent. Limit existence,
  affine projections, and arbitrary base change have no qcqs assumption.
- Being a scheme is `c.pt.obj.obj.IsRepresentable`: representability in `Over S`,
  the same scheme objects and Yoneda presheaves as the recorded space definition.
  The conclusion `∃ i, ∀ j, i ≤ j → (D.obj (op j)).obj.obj.IsRepresentable` gives a
  schematic stage and every later stage (including j=i).
- Being an affine scheme is `∃ U : Over S, IsAffine U.left ∧
  Nonempty (yoneda.obj U ≅ c.pt.obj.obj)`. The second eventual implication repeats
  this exact predicate at every j ≥ i. There is no finite-type condition on U.
- Base change quantifies over every `i`, every algebraic space `W`, and every
  `f : W ⟶ D.obj (op i)`, with no representability or finiteness assumption on f.
  `Over (op i)` indexes precisely arrows j → i of Iᵒᵖ, i.e. stages j ≥ i.
  `Over.post (D ⋙ ObjectProperty.ι IsAlgebraicSpace)` sends such an arrow to its
  actual sheaf map Z_j → Z_i. `Over.pullback f.hom ⋙ Over.forget W.obj` is the
  actual diagram of sheaf fibre products Z_j ×_{Z_i} W, with their canonical maps.
  The cone b is limiting and its apex is isomorphic, by e, to Z ×_{Z_i} W.
  The two displayed equations specify compatibility with the maps to Z_j and W;
  the isomorphism is the canonical comparison, not an unspecified object bijection.
  The sheaf pullbacks are algebraic spaces by the existing fibre-product theorem.

Dependency declarations used for the statement:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`, declarations
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsAlgebraicSpace`,
  `AlgebraicSpace.IsEtale`, `AlgebraicSpace.IsSurjective`; the full subcategory's
  objects are the recorded fppf sheaves and arrows are their natural transformations.
- Gained landed node `def-sfb-space-affine-quasifinite-properties`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`,
  `AlgebraicGeometry.AlgebraicSpace.MapIsAffine` (only its affine notion is used).
- Gained landed node `def-sfb-space-absolute-quasi-separated`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`,
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated`.

The recorded source signatures and docstrings were read. Other public machinery is
Mathlib's `Over.post`, `Over.pullback`, `Over.forget`, `Cone`, `IsLimit`, Yoneda
representability and `ObjectProperty.ι`. The available recorded proof modules are
imported without `public`: fibre products, chartwise étale permanence, scheme affine
limits, étale relation quotients, global-section continuity, étale-algebra descent,
surjectivity descent, scheme lfp/affine permanence, the affine-target adjunction and
the scheme representability criterion. Unstated proof dependencies (affine locality,
finite affine atlas refinement, space section continuity, representable-isomorphism
and open-cover descent) have no module to import; their complete roles remain in the
theorem's ten-step proof docstring. No import cycle is introduced.

Source checked directly: `literature/stacks-project/spaces-limits.tex`,
`lemma-directed-inverse-system-has-limit` (07SF), `situation-descent` (084R),
`lemma-limit-is-affine` (07SQ), and `lemma-limit-is-scheme` (07SR).

Edge cases checked before writing and again after compilation:

- The directed set is nonempty, as 07SF requires, but need not have a least element
  or be antisymmetric. The tail is encoded by its actual arrows, including identities.
- A singleton or constant system gives the expected limit and eventual statements.
- Empty spaces and the zero ring are permitted. The finite-cover proof explicitly
  handles the empty cover, giving an empty stage represented by Spec 0.
- S need not be qcqs. Absolute quasi-separatedness is used for the spaces themselves.
- Non-qcqs systems still receive the limit, affine projections and base-change clause.
- Transition maps need not be surjective; W and f are wholly arbitrary.
- No choice of an arbitrary comparison map or extra cone is a hypothesis. All cones,
  isomorphisms and comparison equations occur in the conclusion.

Searches for existing statements/notions:

- `msearch.py ... leanfinder`, query: “Inverse limits of algebraic spaces with affine
  transitions exist with affine projections and are eventually schemes or affine
  schemes when the qcqs limit is such”. Eight hits, all scheme-only affine-transition
  limit results, notably `Scheme.exists_isAffine_of_isLimit`, `isAffineHom_π_app` and
  affine-scheme limits. None asserts existence/eventual schematicity for spaces.
- `msearch.py ... leansearch`, query: “An inverse system of algebraic spaces with
  affine transition morphisms has a limit and eventually schematic stages”. Eight
  hits, again scheme limits and the unrelated `InverseSystem.limit`; no exact match.
- `msearch.py ... loogle`, query: `"AlgebraicSpace", "IsAffine"`: zero hits.
- `msearch.py ... grep`, query: `AlgebraicSpace|exists_isAffine_of_isLimit`, restricted
  to Mathlib/AlgebraicGeometry: two hits in AffineTransitionLimit, both scheme-only.
- `rg` in `lean/WeilConjectures` for the item id: no hits. Searches there for affine
  and schematic space-limit declarations found no existing version.
- `rg` in `lean/Sheaf/AlgebraicGeometry` for affine/limit, affine predicates and
  quasi-separatedness found existing consumers, `MapIsAffine` and
  `IsAbsolutelyQuasiSeparated`. Both definitions are reused through their landed
  nodes, which were located by `rg` in `dag/nodes`; no duplicate is introduced.
- `rg` over project sources for `exists_affine_limit_eventually_schematic` found no
  existing declaration before writing.

Validation: prescribed `scompile.py` compiled both its sandbox probe and the library
module cleanly. The delivery dry run and delivery checks are recorded below when run.
No statement dispute or mathematical node fault was found.

## Second reading by Q12

This is a second pass by the delivery author; the dispatcher assigns the independent
review to the maintainer. I reopened the node and the completed module and checked the
correspondence above. In particular, I checked that the limiting cone is tested in
fppf sheaves, the qcqs condition scopes over both eventual clauses only, the two scheme
predicates mean representability by schemes over S, and the base-change diagram uses
all j ≥ i and the actual transition maps. The equations for both pullback projections
prevent an arbitrary isomorphism from replacing the canonical comparison. Nonempty I,
preorders, empty schemes, arbitrary S and arbitrary W are all retained. The only
follow-up edit was adding the direct public import of the recorded scheme dependency.
No hypothesis or conclusion mismatch was found. No new nodes or dependency modules
require a separate reading.
