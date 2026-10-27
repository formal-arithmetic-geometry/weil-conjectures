## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations
states `AlgebraicGeometry.TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
with one postponed proof, and defines two coordinate helpers with actual data.
The informal node statement, proof, and proof dependencies are unchanged.

Source read: Milne, Algebraic Groups (2017), printed pp.428–431 (PDF pages
440–443), Definition 21.10, Theorem 21.11(b),(c),(e), and paragraph 21.19,
formula (135). The current blueprint unit is the six-functor stability proposition;
this node is a supporting algebraic-group fact, not that unit's own statement.
There is no statement correction or mathematical dispute.

Hypotheses, clause by clause:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- Group schemes and their homomorphisms are `Grp (Over (Spec (.of F)))` and
  morphisms in that category; their underlying Over morphisms are `.hom.hom`.
- `hG : ReductiveTorusCentralizer.IsReductive G` uses the recorded definition:
  affine, finite type, smooth, geometrically connected, and with no nontrivial
  smooth connected closed normal unipotent subgroup over an algebraic closure.
  Since F is already algebraically closed this is equivalent to the node's
  formulation over F. Unipotence is the existing faithful geometric-matrix
  predicate, not an abstract Lie-algebra condition.
- `i : T ⟶ G` with `hT : ...IsMaximalTorus i` gives a closed torus inclusion
  maximal among torus subgroups. `(r : ℕ)` and `hsplit` specify an isomorphism
  with the recorded rank-r split torus. This includes rank zero.
- `[ModObj T.X G.X]` and `hconj` identify the internal action map with the actual
  morphism `(t,g) ↦ i(t) g i(t)⁻¹`. This presents the conjugation action already
  specified in the node; it places no additional mathematical condition on i.
  Every homomorphism gives this action, uniquely determined by that map.
- `α : T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)`, `hα : α.hom.hom ≠ 1`,
  and `hweight : weightSpace T G α ≠ ⊥` mean exactly membership in the set Φ
  of nontrivial character weights. The canonical Lie space is `GrpObj.Lie G.X`.
  The recorded `weightSpace` uses actual dual-number tangent points and character
  values, not differentials of characters; rational points of a split torus over
  algebraically closed F detect its rational representation weights.

Conclusions, clause by clause:

- Existential U and j are the root subgroup scheme and its inclusion.
  `IsClosedSubgroupScheme j.hom.hom`, `Smooth U.X.hom`, and
  `ConnectedSpace U.X.left` give all three stated properties.
- `IsStable T G j` is normalization under the specified conjugation action,
  on all test schemes. Equality of the range of `GrpObj.differential j.hom.hom`
  with `weightSpace T G α` says its tangent space inside g is exactly g_alpha.
- `Nonempty (Grp.mk (StandardGroupSchemes.additive F) ≅ U)` is the required
  group-scheme isomorphism with Ga.
- The universal clause for K and k quantifies over every smooth connected closed
  normalized subgroup with this tangent image. `∃ e : K ≅ U, e.hom ≫ j = k`
  expresses equality as subgroup schemes of G. Both inclusions are injective
  subfunctors, so this is precisely uniqueness, independent of a choice of
  presenting scheme. An extra assertion that the underlying group type equals U
  would incorrectly compare presentations rather than subgroups.
- The clause for every isomorphism v, every commutative F-algebra A, every
  t in T(A), and every a in A is exactly `t u(a) t⁻¹ = u(α(t) a)` in G(A).
  `additiveParameterPoint F a` is Spec of polynomial evaluation at a.
  `multiplicativePointCoordinate F (t ≫ α.hom.hom)` evaluates the Laurent
  coordinate using the canonical Γ(Spec A) ≅ A. No arbitrary maps are supplied.
- `∃ αcoroot : Grp.mk (StandardGroupSchemes.multiplicative F) ⟶ T` is an actual
  group-scheme homomorphism. For every A-point s of Gm, the equality
  `s ≫ αcoroot.hom.hom ≫ α.hom.hom = s ^ 2` is the required unit-valued identity.
  Points of Spec F[t,t⁻¹] are canonically units of A; the group law and square
  are those of the recorded multiplicative group, so this tests all units.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`; the algebraic-closure
  dependency's recorded AlgebraicClosure module also supplies the closure used
  by the existing reductivity/torus definitions.
- Mathlib.CategoryTheory.Monoidal.Grp: `CategoryTheory.GrpObj`, `Grp`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  `AlgebraicGeometry.IsClosedSubgroupScheme` (extending `IsSubgroupScheme`),
  and `IsNormalSubgroupScheme` inside the recorded reductivity predicate.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `AlgebraicGeometry.Smooth`.
- Mathlib.Topology.Connected.Basic: `ConnectedSpace`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `LocallyOfFiniteType` and `QuasiCompact` inside `IsReductive`/`IsAlgebraic`.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: `affine`, `map`, `additive`,
  `additiveGroup`, `multiplicative`, `multiplicativeGroup`.
- Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology:
  `IsReductive`, `IsMaximalTorus`.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `MultiplicativeType.splitTorus`.
- Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights: `weightSpace`, `IsStable`.
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential:
  `GrpObj.differential` and the canonical Lie/tangent-space construction.
- The recorded proof module Sheaf.AlgebraicGeometry.TorusPositiveRaySubgroup
  is imported without public visibility as required. The proof dependencies
  lem-sfb-reductive-rank-one-reflections and lem-sfb-one-dimensional-unipotent-additive
  have no recorded Lean declarations in the read repository; there are no imports
  to add for them. Their mathematics is retained in the complete theorem docstring.

The three already-landed definition nodes for reductivity/maximality, character
weights, and split tori are added to stmt_deps to reference their existing notions.
No new definition node or dependency replacement is needed. The two coordinate
helpers belong to the item's own formula and are listed in lean.declarations.

Edge cases checked: G=T has no nontrivial adjoint weights, so no hweight and the
assertion is vacuous. The trivial rank-zero group likewise has no roots. Positive
characteristic is unrestricted: for SL2 in characteristic two the root character
is nontrivial even though its differential can vanish. The statement uses the
character and retains this case. The test algebra is not assumed reduced or
nonzero, so dual numbers and the zero algebra are included. The formula quantifies
over every group-scheme isomorphism v, not just a chosen normalization. Candidate
subgroups in the uniqueness clause need not be assumed unipotent or additive.

Searches performed through msearch.py:

- leanfinder: "Root subgroups of a reductive algebraic group are additive groups
  with torus conjugation by a root character" — eight hits on abstract root data
  and Lie-algebra Killing-form root systems; no reductive group-scheme statement.
- loogle: `"root", "GrpObj"` — zero hits.
- grep (Mathlib): `rootSubgroup|rootGroup|corootHom` — zero hits.
- leansearch: "Root subgroup schemes of reductive algebraic groups and coroot
  homomorphisms" — eight hits on root pairings/Lie-algebra coroot spaces; no match.
- rg over lean/WeilConjectures and lean/Sheaf for reductive/rootSubgroup/rootGroup/
  corootHom/torus-weight names found the recorded supporting definitions, not this
  statement. Searching the item id in WeilConjectures found none. DAG searches
  found def-sfb-torus-character-tangent-weights,
  def-sfb-reductive-torus-centralizer-terminology and def-sfb-tori-multiplicative-type;
  their exact declarations are reused instead of copied.

The first scompile.py run typechecked both the sandbox and named library module,
with only a whitespace warning at the action notation. The spacing was corrected;
subsequent compiler and delivery checks are recorded below when complete.

Verification: the corrected file compiled cleanly with scompile.py in both sandbox
and named module modes (16.5 s and 11.4 s); no errors or warnings. All binders and
universes are explicit and autoImplicit is disabled. Only the permitted lean and
stmt_deps fields differ in the item copy.

## Second reading by Q135

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
