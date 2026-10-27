## Worker report

The module `Sheaf.AlgebraicGeometry.GroupSpaceUnramifiedIdentityTest` states
`AlgebraicGeometry.AlgebraicSpace.groupSpace_unramified_iff_identity` with its proof
postponed by `sorry`. It introduces no definitions. The mathematical statement and
proof of the DAG node are unchanged.

Hypothesis and clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; B and G are `AlgebraicSpace S`; the structural
  morphism is `q : G ⟶ B`. These are the recorded scheme and algebraic-space notions.
- The given group algebraic-space structure over B is the parameter `group :
  @GrpObj (Over B.obj) inferInstance (Over.cartesianMonoidalCategory B.obj)
  (Over.mk q.hom)`. Mathlib's chosen cartesian structure on `Over B.obj` uses actual
  sheaf pullbacks and the terminal object `Over.mk (𝟙 B.obj)`. Thus `group.mul` is
  multiplication G ×_B G → G, `group.one.left` is the identity B → G (its over
  condition says q e = id), and `group.inv` is inversion. The associativity, identity
  and inverse fields express exactly the group identities, hence on every scheme
  test. There is no commutativity, smoothness, separatedness or representability
  hypothesis on q. The group operations are supplied data, not arbitrary maps.
- `hq : MapIsLocally (@LocallyOfFiniteType) q` states local finite type on all
  compatible representable etale scheme charts on source and target.
- The left hand side is `MapIsLocally (@AlgebraicGeometry.IsUnramified) q`, using
  exactly the recorded scheme unramified predicate in the same chart test.
- `∀ b : Point B.obj.obj` quantifies over the specified common-field-extension
  classes, and `mapPoint group.one.left.hom b` is precisely e(b).
- The right hand side existentially supplies an algebraic space V and inclusion
  i : V → G. `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) i.hom.hom`
  says that every scheme base change is an open immersion, exactly the node's
  definition of open subspace. Membership in `pointImage i.hom.hom` says this
  neighbourhood contains e(b). Finally `MapIsLocally ... (i ≫ q)` says its restriction
  is unramified. This is the stated definition of unramified at a point, expanded
  inline, with no replacement by formal unramifiedness or a field-fibre condition.

Dependencies used, with their full signatures and docstrings read in the read clone:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsRepresentableWith`
  and the representable etale test `IsEtale` used by the chart predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`,
  the conjunction of local finite type and an open-immersion diagonal.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  imported for the stated dependency and its point/fibre-product framework.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`;
  its already-landed owning node `def-sfb-space-morphism-properties` was added to
  stmt_deps to cite the existing interface, rather than recreate it.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`: `Point`,
  `PointRepresentative`, its relation and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `PointRepresentative.map`. Its landed owner `def-a1-space-point-topology` was
  added to stmt_deps. The existing `mapPoint` construction in
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` is exposed by the morphism-properties
  import and maps these same quotient classes, with no new point notion.
- Mathlib `CategoryTheory.GrpObj`, `MonObj` and
  `Over.cartesianMonoidalCategory`, read in Monoidal/Grp, Monoidal/Mon and
  Monoidal/Cartesian/Over. The cartesian structure is passed explicitly, avoiding
  an extra local instance or an import of a quotient theorem just for its instance.

The proof dependency `lem-sfb-space-unramified-locus-base-change` has no Lean record
in the read clone and is not imported. Its role is fully explained in the theorem
proof docstring; it is not needed to type this statement. No dependency module is
required to state the item.

Source checked directly: `literature/stacks-project/spaces-groupoids.tex`,
`lemma-group-scheme-unramified-or-lqf` (Tag 0DSI), including its proof. Its unramified
clause is precisely the present equivalence and local-finite-type hypothesis.

Edge cases checked: empty B gives an empty group space and vacuous point condition;
the trivial group is included; etale constant groups satisfy both sides; G_a over a
field fails the identity test, as does mu_p in characteristic p. Noncommutative groups
are permitted. Neither geometric connectedness nor algebraic closedness is required.
All schemes and test fields use the established universe u; `Point` itself lives in
u+1, with no artificial equality or restriction of the point universe. No rational
point hypothesis is imposed.

Searches actually run:

- msearch.py leanfinder: "A locally finite type group algebraic space is unramified
  if and only if it is unramified at every point of its identity section". Eight
  hits concerned ring unramified loci and scheme formal unramifiedness; none states
  this theorem.
- msearch.py loogle: "GrpObj, IsUnramified". Zero hits; service reported unknown
  identifier GrpObj. Direct source inspection found the Mathlib internal group API.
- msearch.py grep: "unramified.*identity|identity.*unramified|UnramifiedAt|class
  GrpObj". Twenty-five hits concerned ring/arithmetic unramifiedness, not this theorem.
- Direct rg searches over lean/WeilConjectures and lean/Sheaf for group spaces,
  UnramifiedAt, unramifiedAt and identity criteria found no exact theorem. The item
  id has no hit under lean/WeilConjectures. These searches located the existing
  MapIsLocally and point interfaces, as well as GrpObj usage by the free-flat-group
  quotient theorem; the latter is not imported or duplicated.
- Direct exact-name search over Mathlib/project declarations and
  dag/lean_names_upstream.json found no groupSpace_unramified_iff_identity.

No statement dispute, correction or hollow definition is involved.

## Second reading by Q111

A separate pass by this worker (the dispatcher prohibits starting another agent)
compared the node and final signature clause by clause. It checked that the group
structure is over B rather than S, that the terminal sheaf of the slice is B, and
that `group.one.left` therefore has exactly domain B and codomain G. It checked
that MapIsLocally tests both source and target etale charts, and that the open
neighbourhood is a genuine algebraic space with all scheme base changes open,
contains the specified quotient point, and has unramified composite to B. The
finite-type hypothesis is present separately and the conclusion is an iff. No
mathematical mismatch was found. No independent-reader claim is made; the
maintainer's independent review remains required by the dispatcher workflow.
