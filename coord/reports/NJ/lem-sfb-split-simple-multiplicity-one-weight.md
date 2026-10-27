## Worker report

The delivery states `AlgebraicGeometry.RationalHighestWeight.split_simple_multiplicity_one_weight`
in `Sheaf.AlgebraicGeometry.GroupScheme.SplitSimpleMultiplicityOneWeight`. Its only postponed
proof is that theorem, with the five DAG proof steps in its docstring. No definition is added.
The source was read in Milne, Algebraic Groups (2017), Theorem 22.2, pp.463--464,
and Proposition 22.17 and Theorem 22.18(b), p.467. The latter explicitly says the primitive
weight of a simple module has multiplicity one; its proof uses the split Borel and cyclicity.
There is no characteristic, algebraic-closedness, or simply-connectedness restriction.

Clause-by-clause rendering:

- The arbitrary field is `{k : Type u} [Field k]`.
- The group schemes are `G T : Grp (Over (Spec (.of k)))`, using `CategoryTheory.GrpObj`
  inside the standard bundled `Grp`. Their homomorphism is `iT : T ⟶ G`.
- Smoothness is `[Smooth G.X.hom]`, connectedness `[ConnectedSpace G.X.left]`, and
  affineness `[IsAffine G.X.left]`. Finite type is the standard pair
  `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`.
- Geometric semisimplicity is `hG : IsSemisimpleGroupScheme` of the actual base change
  of G to `AlgebraicClosure k`. The existing predicate includes the absence of any
  nontrivial smooth connected solvable normal closed subgroup. Its solvability is
  termination of the actual commutator-derived series, not abstract rational-point
  solvability. Its other geometric properties follow from the already stated base
  properties (connectedness uses the identity point), so no geometric restriction is added.
- The torus is closed by `hclosed : IsClosedSubgroupScheme iT.hom.hom`.
  `hsplit : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)` is an actual
  group-scheme isomorphism over k with a finite product of G_m, including rank zero.
  `hmax` applies the existing `IsMaximalTorus` to the base-changed inclusion over the
  algebraic closure, precisely geometric maximality. It does not replace geometric
  maximality by maximality over k alone.
- `[IsAffine T.X.left]` exposes an automatic property required by the existing coordinate
  API: a closed subscheme of affine G is affine. More explicitly,
  `IsClosedSubgroupScheme.isClosedImmersion` gives the closed immersion, its
  `IsAffineHom` instance is in Mathlib Morphisms/ClosedImmersion, and
  `AlgebraicGeometry.isAffine_of_isAffineHom iT.hom.hom.left` gives this affineness.
  Thus this binder excludes no instance of the node.
- The vector space is `{V : Type v} [AddCommGroup V] [Module k V]` with
  `[FiniteDimensional k V]`. The independent universe v allows arbitrary vector spaces;
  finite-dimensional spaces can be transported to k's universe for the action dictionary.
- The rational representation is `c : V →ₗ[k] V ⊗[k] coordinateAlgebra G` with the recorded
  `HopfAction.Coassociative` and `HopfAction.Counital` identities. The coordinate algebra
  is the actual global-section Hopf algebra. Milne's dictionary identifies these with
  rational group-scheme representations, not just representations of G(k).
- Nonzero and simple are exactly `hsimple : RationalHighestWeight.IsSimple c`: it includes
  `Nontrivial V`, and every stable submodule is bottom or top. `IsStable c N` means
  c(N) lies in the image of N tensor k[G]. Evaluating at all algebra-valued points makes
  N stable under every extended action; conversely evaluation at the universal point
  recovers the coaction condition. This is the node's rational-subrepresentation meaning.
- The existential character is `lam : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative k)`.
  Thus it is a group-scheme character defined over k, not a Lie character or just a
  character of the group T(k).
- Its character space is
  `LinearMap.eqLocus ((coordinateMap iT).toLinearMap.lTensor V ∘ₗ c)
    ((TensorProduct.mk k V (coordinateAlgebra T)).flip (characterElement lam))`.
  The first map is restriction of the coaction to T. The second is
  v ↦ v tensor lam*(t). The equalizer condition evaluates to
  t(1 tensor v)=lam(t)(1 tensor v) on every k-algebra. Conversely its universal-point
  case is exactly the equalizer identity. Tensor symmetry converts the node's
  A tensor V action convention to the right-coordinate coaction V tensor k[T].
- The only conclusion is `Module.finrank k (that equalizer) = 1`. No dominant-weight,
  cyclicity, highest-line, or absolute-simplicity conclusion is added.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field`.
- `def-sc-group-scheme`: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, `Grp`, with the
  upstream WeilConjectures.AlgebraicGeometry.GroupScheme.Defs subgroup interface.
- `def-wf-algebraic-representations`: read `standardRepresentation` in
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie and
  `RationalHom.representation` in GeneralLinear.Representation, as well as the general
  `RationalHom` and `RationalHom.points` in GeneralLinear.Lie. The former two are actions
  on k-points, not an arbitrary-field simplicity interface. They are not redefined.
  Their recorded module is imported. The existing coaction dictionary gives the
  equivalent general rational representation needed here.
- Added landed statement dependencies: `def-sfb-rational-highest-weight-data`, module
  Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData, using `coordinateAlgebra`,
  `coordinateHopf`, `coordinateMap`, `IsStable`, `IsSimple`, and `characterElement`;
  `def-sfb-semisimple-group-scheme`, module GroupScheme.Semisimple, using
  `IsSemisimpleGroupScheme` and its derived-series notion;
  `def-sfb-reductive-torus-centralizer-terminology`, module
  Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology, `IsMaximalTorus`;
  `def-sfb-tori-multiplicative-type`, module Sheaf.AlgebraicGeometry.ToriMultiplicativeType,
  `baseChange` and `splitTorus`. Their complete signatures/docstrings and DAG statements
  were read. Only the allowed addition of landed statement-dependency IDs was needed.
- All currently recorded proof dependencies are plain imports: the rational/comodule
  dictionary, reductive Borel structure, relative torus bundle weights, geometric
  connectedness, smooth ring-map base change/composition, and algebraic closure.
  Unstated proof nodes are left for stage 3; they are not statement prerequisites.

Edge cases checked before writing: V=0 is excluded exactly by IsSimple. For G=1 and
rank-zero T, all subspaces are stable, so a nonzero simple module is one-dimensional
and the trivial character works. A trivial one-dimensional representation of any G
has its entire space as the trivial-character space. Positive characteristic (including
2), finite fields, imperfect fields, and groups with a nontrivial finite central kernel
are retained. No test-algebra reducedness is used. The character space is an actual
submodule; finite-dimensionality passes to it, so finrank=1 has its intended meaning.

Searches actually run:

- msearch.py leansearch: "Highest weight multiplicity one for irreducible rational
  representations of split reductive algebraic groups": eight hits, Lie root spaces,
  generic multiplicity, and Lie/Weyl-group weights; no exact statement.
- msearch.py leanfinder: "A nonzero simple rational representation of a split semisimple
  algebraic group has a torus character weight space of dimension one": eight hits,
  all Lie root-space/weight-chain/rank results, no rational algebraic-group result.
- msearch.py loogle: `"weightSpace", "finrank"`: one hit,
  `LieModule.zero_lt_finrank_genWeightSpace`, not this statement.
- msearch.py grep, RepresentationTheory:
  `highest.?weight|weightSpace.*(finrank|rank)|finrank.*weightSpace`: zero hits.
- rg in lean/WeilConjectures by the item ID: no occurrence. Keyword searches in
  GroupScheme found RationalHom and characteristic-zero point-representation APIs,
  not this arbitrary-field theorem. Searched dag/lean_names_upstream.json as well.
- rg in lean/Sheaf for semisimple group predicates, maximal torus, rational simplicity
  and weightSpace found the four landed definition interfaces above. The existing
  SimpleModuleDualHighestWeight theorem assumes algebraic closedness, a Borel,
  positive roots and a longest representative, and is not this statement. Existing
  TorusCharacterTangent.weightSpace concerns tangent representations, and the
  RelativeTorusBundleWeights weightSpace uses a chosen group-algebra coordinate;
  neither is a replacement for the present general representation's equalizer.

No statement correction, new node, dependency repair, or STATEMENT-DISPUTED flag.

## Second reading by NJ

The dispatcher requested no other agents; this is the author's clause-by-clause reread,
not a claim of independent review. Independent review belongs to the maintainer.
Reopened the node and Lean signature: geometric semisimplicity and maximality use
AlgebraicClosure k, splitness uses an isomorphism over k, simplicity is scheme-theoretic,
and the conclusion uses the actual character pullback. The explicit affine T interface
is automatic from hclosed. The zero and rank-zero cases agree as described above.
No source statement is changed. No new independent definition is introduced.

Validation: scompile.py checked the sandbox and final module against the published
library successfully (final module 18.3 seconds), with no errors or unexpected warnings.
