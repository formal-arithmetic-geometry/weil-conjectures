## Worker report

The module `Sheaf.AlgebraicGeometry.GaloisDescentAffineSubgroups` states all clauses
of `lem-sfb-galois-descent-affine-subgroups` in four named theorems, each with
`sorry` as its entire proof. It adds no definitions, nodes, or dependency repairs.
The accepted stage-1 statement and split are unchanged. The inherited previous
stage-1 BLOCKED ending is superseded by the current stage-2 handoff instruction in
coord/brief-stage2.md §0: recording a reviewed split's Lean statement is permitted.

Source read: Milne, Algebraic Groups (2017), 1.51 and 1.54(a)-(b), printed pp.21-22;
A.64-A.66, printed pp.580-581. The source includes infinite Galois extensions and
ideal-sheaf invariance, without assuming smoothness or schematic density. The node
only mentions smoothness and connectedness as vocabulary; neither is a hypothesis
of any assertion. No statement correction or disputed statement is needed.

Hypotheses and clauses, matched against the node:

* The base field is `(k : Type u) [Field k]`. The Galois field extension is
  `(L : Type u) [Field L] [Algebra k L] [IsGalois k L]`. Mathlib's IsGalois means
  normal and separable, and its separable field extensions are algebraic. There
  is no finite-dimensionality or finite-degree assumption. Arbitrary detection
  extensions use `[Field K] [Algebra k K]` and no Galois assumption.
* A group scheme J over k is `J : Over (Spec (.of k))` with `[GrpObj J]`.
  `[IsAffine J.left]` gives affineness; `[LocallyOfFiniteType J.hom]` and
  `[QuasiCompact J.hom]` give finite type, precisely the recorded dependency's
  conjunction. V has these same properties over L. Closed subgroups N,M in the
  detection statements are automatically affine and of finite type, because their
  closed embeddings have affine finite-type target J; no extra restriction on
  their group schemes is imposed.
* The chosen scalar extension J_L is
  `(Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj J`.
  Its group structure is the canonical image under the monoidal pullback functor,
  via `Functor.grpObjObj`, enabled by `open scoped CategoryTheory.Obj`. This is a
  scoped upstream instance, not a new or file-local instance.
* The supplied closed subgroup V of J_L is the map `j` with
  `[IsClosedSubgroupScheme j]`. This reuses the recorded subgroup predicate,
  including its compatibility with group laws and injectivity on all algebra
  points. The defining ideal is `RingHom.ker j.left.appTop.hom` in the coordinate
  ring of J_L.
* The canonical semilinear action is the map on global sections of
  `baseChangeMap J.hom (specAlgEquivOver σ)`. These existing definitions are the
  pullback map with components identity on J and Spec σ on Spec L. Consequently
  its coordinate-ring map is exactly a tensor λ ↦ a tensor σ(λ), with no chosen
  arbitrary action or coordinate isomorphism. `hstable` says its inverse image of
  the defining ideal equals that ideal for every `σ : L ≃ₐ[k] L`. Because these
  maps are automorphisms, this is equivalent to stability of the ideal under
  the action. Using kernels retains all nilpotent defining equations.
* `galois_descent_affine_subgroups` produces N, its group-object structure gN,
  and its embedding i into J. The explicit `@IsClosedSubgroupScheme ... gN ... i`
  ensures this really is a closed subgroup with this group structure. The next
  three conjuncts give affineness and finite type of N. The isomorphism e from
  N_L to V satisfies `e.hom ≫ j = pullback.map i`, so N_L=V as subgroup schemes,
  with their specified embeddings, rather than just as abstract schemes.
* The final universal quantifier in that theorem is uniqueness: for every other
  closed subgroup i' whose scalar extension equals V over J_L, there is an
  isomorphism `e : N' ≅ N` with `e.hom ≫ i = i'`. Such an isomorphism automatically
  respects the group laws, since both embeddings are group homomorphisms and
  closed immersions are monomorphisms. It is unique for the same reason. This is
  equality of subgroups, allowing different isomorphic representatives, not
  literal equality of the underlying types or of chosen pullback objects.
* `affine_closed_subgroup_inclusion_iff_baseChange` states both directions of
  inclusion detection. Inclusion is an actual factorization `h ≫ j = i`, and
  the right side is the same factorization after canonical scalar extension.
  Such a factorization is automatically a group homomorphism since j is monic.
* `affine_closed_subgroup_eq_iff_baseChange` states both directions of equality
  detection, using isomorphisms commuting with the embeddings on both sides.
* `affine_closed_subgroup_normal_iff_baseChange` states the equivalence of the
  recorded `IsNormalSubgroupScheme i` with the very same predicate on the
  canonically pulled back embedding. Its defining class tests normality of the
  image subgroup on every commutative base algebra, including nonreduced ones.

Dependency declarations read and used:

* Mathlib.Algebra.Field.Defs: `Field`; Mathlib.Algebra.Algebra.Defs: `Algebra`;
  Mathlib.FieldTheory.Galois.Basic: `IsGalois` (normal and separable/algebraic).
* Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj` and
  `CategoryTheory.Functor.grpObjObj`; the latter transports through the canonical
  monoidal `Over.pullback` functor.
* WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`, and
  `IsNormalSubgroupScheme`, with their full all-algebra-points signatures.
* Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: `QuasiCompact`.
* The vocabulary-only dependency declarations were also read:
  Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth` and
  Mathlib.Topology.Connected.Basic: `ConnectedSpace`. Neither is assumed in this
  node, so neither has been added to the signatures.
* Mathlib.AlgebraicGeometry.Scheme: `Spec`, `Spec.map`;
  Mathlib.CategoryTheory.Comma.Over.Pullback: `Over.pullback`;
  WeilConjectures.AlgebraicGeometry.PicardFunctor: `baseChangeMap`;
  WeilConjectures.AlgebraicGeometry.Picard.Jacobian: `specAlgEquivOver`.
* The private proof-plan imports give the stated Mathlib leaves for tensor
  pushouts (`Algebra.TensorProduct.productMap`, `Algebra.TensorProduct.ext`),
  faithfully flat field base change (`Module.FaithfullyFlat.instTensorProduct`),
  and `Ideal.comap_map_eq_self_of_faithfullyFlat`. The proof-only linear-descent
  node `lem-sfb-galois-stable-subspace-descent` currently has no Lean record and
  hence no module to import; its use is retained explicitly in the proof
  docstring, and its eventual module can be added as a private proof import.

Edge cases checked mathematically and against the signatures:
L=k gives the identity action and descent of V itself. Infinite algebraic Galois
extensions remain allowed. K/k may be inseparable or transcendental. Both the
whole group (zero defining ideal) and identity subgroup are included. Nonreduced
subgroups, notably μ_p in characteristic p, remain covered because the actual
kernel ideal and all algebra points are used. The zero test algebra is allowed
by IsNormalSubgroupScheme's `CommRing R` quantifier. A group scheme over a field
cannot be empty, since its identity section exists. All geometric and coefficient
objects share an arbitrary explicit universe u, the convention of the recorded
scheme and subgroup interfaces; no test-algebra universe smaller than the field
universe is introduced.

Searches actually made for an existing statement:

* msearch.py leanfinder, query "Galois descent of closed subgroup schemes of affine
  group schemes": eight hits, consisting of InfiniteGalois and IntermediateField
  fixing-subgroup results, PreGaloisCategory closed embedding results, closed
  immersion affine properties and affine-transition-limit closed-point results.
  None states descent of closed subgroup schemes.
* msearch.py loogle, query "IsClosedSubgroupScheme, IsGalois": zero hits, with
  `unknown identifier 'IsClosedSubgroupScheme'` in the Mathlib-only search service;
  this does not index the project's predicate. Direct project searches below
  establish absence of the desired declaration there.
* msearch.py leansearch, query "Closed subgroup schemes descend uniquely under
  Galois field extensions when their defining ideal is stable under the canonical
  semilinear action": eight hits, all InfiniteGalois/IsGaloisGroup fixed-field and
  fixing-subgroup results; none is the scheme-theoretic statement.
* msearch.py grep, query
  `(galois|Galois).*(subgroupScheme|[Cc]losed[Ss]ubscheme)|(subgroupScheme|[Cc]losed[Ss]ubscheme).*descent`:
  zero hits.
* rg in lean/WeilConjectures and lean/Sheaf for Galois closed-subscheme/subgroup
  descent: found the general `exists_closed_subset_of_galois_invariant` in
  GaloisInvariantClosedSubsetDescends, which concerns only closed topological
  subsets, so cannot express nonreduced closed subgroup schemes. Its source led
  to reusing the existing canonical `baseChangeMap`/`specAlgEquivOver` action.
* rg for the node id in lean/WeilConjectures: no matching statement. In lean/Sheaf
  the existing PerfectSolvableUnipotentTorus docstring cites the item as a future
  proof input, rather than stating it. Searches for each of the four new full
  declaration names in Mathlib, WeilConjectures, Sheaf and the upstream name
  index found no collision.

Validation: scompile.py compiled both its sandbox check and the module under its
final library name successfully (10.8 s and 16.5 s), with no errors or warnings.
The module contains four theorem declarations and exactly four whole-proof
`sorry`s. All variables and the universe are explicitly bound. The required
server preflight and final per-file compile are run through deliver2.py.

## Second reading by Q149

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
