## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.OneDimensionalUnipotentAdditive`
states `AlgebraicGeometry.oneDimensionalUnipotent_additive`. Its only proof is `sorry`;
there are no new definitions or auxiliary postponed theorems. The node's mathematical
statement and proof remain unchanged. Its `stmt_deps` gains the already landed
`def-sfb-solvable-group-structure`, which owns the existing unipotence predicate.

Hypothesis and conclusion correspondence:

- The algebraically closed field F is `(F : Type u) [Field F] [IsAlgClosed F]`.
  No characteristic instance or perfectness hypothesis is imposed.
- The F-group scheme U is `(U : Grp (Over (Spec (.of F))))`. The underlying over-object
  is `U.X`, its scheme is `U.X.left`, and its structure map is `U.X.hom`.
  A bundled group-object isomorphism in the conclusion preserves the base and group laws.
- Smoothness is `[Smooth U.X.hom]`; connectedness is `[ConnectedSpace U.X.left]`.
  ConnectedSpace includes nonemptiness, exactly as the dependency defines it.
- Affineness is `[IsAffine U.X.left]`. Finite type is the pair
  `[LocallyOfFiniteType U.X.hom] [QuasiCompact U.X.hom]`, as the recorded
  def-weil-finite-type-morphism interface specifies.
- Geometric unipotence is `(hU : SolvableGroupStructure.IsUnipotent U)`. Reading its
  definition shows that it supplies a closed faithful representation in GL_n and
  positive-power nilpotence of r(x)-1 for every algebraically closed field extension.
  Its smoothness conjunct repeats an existing hypothesis and introduces no restriction.
- The one-dimensional tangent hypothesis is
  `(hdim : Module.finrank F (GrpObj.Lie U.X) = 1)`. This is the F-vector space at the
  identity: `GrpObj.lieIdentityTangentEquiv U.X`, read in full, is a proved F-linear
  equivalence to `schemeTangentSpace F U.X.left U.X.hom` at the image of the closed
  point under the unit section. The target F-action is precisely scalar restriction
  along the structural residue map. Thus this uses the recorded scheme tangent-space
  notion, without assuming a residue-field equality or adding a hypothesis.
  Smooth finite type groups have finite-dimensional Lie modules, so finrank = 1
  expresses dimension one and does not admit any infinite-dimensional case.
- The conclusion `Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U)` says
  there exists an F-group scheme isomorphism Ga → U in the requested direction.
  The recorded additive group is Spec F[y] with its actual specified Hopf maps.

Dependencies and declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (line 62); this is the
  algebraically-closed-field component of def-weil-algebraic-closure. No chosen
  algebraic closure is needed in the theorem's binders.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, and the
  group-object homomorphism category, as def-sc-group-scheme records.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme` and
  `IsClosedSubgroupScheme`; these are used inside the imported unipotence predicate
  and in the proof plan, rather than duplicated in the statement.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (lines 62–65).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (lines 705–707).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` (line 43).
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact` (line 43).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `additive` and `additiveGroup`.
  I read the definitions and the coordinate maps additiveComul, additiveCounit,
  additiveAntipode: y ↦ y⊗1+1⊗y, 0, and -y.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`,
  `schemeTangentSpaceAddCommGroup`, `schemeTangentSpaceModule`, `schemeTangentMap`.
  This recorded module is publicly imported through the existing identity-tangent
  equivalence module. `GroupScheme.Lie.Basic` defines the Lie module; `Lie.Ring`
  provides its base-ring action; the proved `GrpObj.lieIdentityTangentEquiv`
  in `GroupScheme.LieIdentityTangentEquiv` identifies it with that tangent space.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsUnipotent`, source
  Milne Corollary 14.12. Its owning existing definition node is added to stmt_deps.
- Plain proof import `Sheaf.AlgebraicGeometry.RationalTangentCotangentDuality`:
  `rational_tangent_cotangent_duality`, the recorded proof dependency.
  The two other theorem proof dependencies, lem-sfb-unipotent-central-additive-subgroup
  and lem-sfb-smooth-subgroup-tangent-generation, have no Lean record in the current
  DAG and hence no module to import. They are not needed to type this statement.
  Their full intended use, along with the dual-number calculations and the tangent
  duality bridge, is recorded step by step in the theorem docstring.

Sources checked directly: Milne PDF printed pp.297–298 (PDF pages 309–310), including
Corollary 14.55 and paragraph 14.58, and printed p.18 (PDF page 30), Proposition 1.37.
Paragraph 14.58 gives precisely the smooth connected unipotent dimension-one
classification over a perfect field; Proposition 1.37 equates tangent and geometric
dimension for smooth groups. Algebraic closedness supplies perfectness in our node.
No statement correction or disputed statement is needed.

Edge cases: all characteristics, including 2, are allowed; Ga satisfies the expected
hypotheses. The trivial group has Lie dimension zero and is excluded by hdim. Gm has
one-dimensional Lie algebra but fails geometric unipotence. Alpha_p has one-dimensional
tangent space but fails smoothness. Smooth finite constant nontrivial groups fail
connectedness and tangent dimension one. Imperfect-field wound forms are excluded
by algebraic closedness, not by an extra assumption. Empty schemes cannot carry the
required identity section. The zero-dimensional faithful representation is permitted
by the shared predicate but cannot satisfy hdim for such a group. Universe u is explicit
and arbitrary; the test fields in the existing predicate live in the base universe,
so the identity extension and algebraic closure are present and the condition is not
vacuous. No extra universe equality is imposed.

Searches actually run:

- msearch leanfinder: "A smooth connected unipotent algebraic group whose Lie algebra
  has dimension one over an algebraically closed field is isomorphic to Ga". Eight
  hits on smooth algebras, Lie groups and Lie algebras, including
  SpecialLinearGroup.subsingleton_of_finrank_eq_one; no algebraic-group classification.
- msearch leansearch: "One dimensional smooth connected unipotent algebraic group is
  isomorphic to the additive group scheme". Eight unrelated Lie-group and abstract
  additive-automorphism hits; no match.
- msearch loogle: `"Unipotent", "IsIso"`. Zero hits.
- msearch grep: `unipotent|oneDimensional.*[Gg]roup`, Mathlib AlgebraicGeometry.
  Zero hits.
- rg on lean/WeilConjectures and lean/Sheaf for unipotent and oneDimensional group
  patterns: found SolvableGroupStructure.IsUnipotent and root-subgroup consumers,
  but no classification declaration. Exact item-id search in WeilConjectures
  found no declaration. Exact proposed name search in Mathlib and both project
  roots found no collision.
- blueprint_refs.py search "one-dimensional unipotent": zero blueprint-node matches.
  The item is a supporting lemma rather than the unit's own statement.

## Second reading by Q24

A separate checking pass reopened the node and the complete module and matched every
binder and conclusion as itemized above. The dispatcher explicitly forbids starting
other agents; this is a second pass by this worker, not a claim of independent agent
review. The maintainer's independent review remains required.

The key checks were that Grp is over Spec F, that the conclusion is an isomorphism in
Grp rather than an underlying-scheme isomorphism, that the additive Hopf group law is
the recorded one, that Lie is F-linear-equivalent to the recorded dual-number tangent
space rather than an unrelated analytic Lie algebra, and that no characteristic or
perfectness binder was added. Reusing the landed unipotence definition required adding
its owning node to stmt_deps; no mathematical statement changed. The module contains
one theorem and no new data, with all variables and universes explicitly bound.
