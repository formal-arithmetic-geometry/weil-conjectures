## Worker report

The delivery states `AlgebraicGeometry.field_split_torus_rational_containment` in
`Sheaf.AlgebraicGeometry.GroupScheme.FieldSplitTorusRationalContainment`, with one
`sorry` and no new definitions. The node's mathematical statement is unchanged.
Two already landed definition nodes are added to `stmt_deps` to cite the existing
split-torus construction and reductivity predicate used in the signature:
`def-sfb-tori-multiplicative-type` and
`def-sfb-reductive-torus-centralizer-terminology`. No new nodes or dependency repairs
are needed. No statement dispute or node fault was found.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Any field k: `{k : Type u} [Field k]`, with no restriction on characteristic,
  perfection, cardinality or algebraic closedness; the universe u is arbitrary.
- G, S and D are k-group schemes: `G S D : Grp (Over (Spec (.of k)))`.
  The bundled `Grp` supplies a `GrpObj` on each underlying k-scheme, and its arrows
  are multiplication-compatible scheme morphisms. This is the existing interface
  recorded by `def-sc-group-scheme`, not a new group-scheme definition.
- Smooth affine finite-type, geometrically connected, reductive G:
  `_hG : ReductiveTorusCentralizer.IsReductive G`. Its actual definition is the
  conjunction of `SolvableGroupStructure.IsAlgebraic G`, `Smooth G.X.hom`,
  `ConnectedSpace` of its scalar extension to `AlgebraicClosure k`, and triviality
  of every connected normal closed algebraic unipotent subgroup after that
  extension. `IsAlgebraic` is exactly `IsAffine`, `LocallyOfFiniteType`, and
  `QuasiCompact` for the structure map. Its `IsUnipotent` predicate includes
  smoothness, a faithful closed finite-dimensional matrix representation, and
  nilpotence of the matrix minus the identity at every geometric point. Closed
  subgroups of affine finite-type G are affine finite-type, so its algebraicity
  condition on U does not restrict the node's subgroups. Connectedness is the
  recorded `ConnectedSpace`, including nonemptiness.
- The specified closed subgroup S of G: `(i : S ⟶ G)` together with
  `[IsClosedImmersion i.hom.hom.left]`. It is a group homomorphism because i is a
  `Grp` arrow; a closed immersion is automatically a subgroup inclusion.
- S is split of some nonnegative finite rank: `_hS : ∃ r : ℕ,
  Nonempty (S ≅ MultiplicativeType.splitTorus k r)`. These are group-scheme
  isomorphisms over k, not isomorphisms after extending the field. The existing
  `splitTorus` is the finite product of `StandardGroupSchemes.multiplicative k`,
  which is Spec of the Laurent polynomial ring with the canonical Hopf law.
- Maximality under inclusion among closed split torus subgroups over k:
  `_hmax` quantifies over every group scheme T and homomorphism j into G,
  assumes `IsClosedImmersion j.hom.hom.left` and a splitting of T over k, and
  says every factorization `a : S ⟶ T`, `a ≫ j = i`, has `IsIso a`.
  A factorization between two closed subgroups is their inclusion, and being an
  isomorphism says this containment is equality. This expresses maximality, not
  the stronger property of containing every split torus; nonsplit tori are not
  included in the quantifier's hypotheses.
- The source D is any split torus of rank s ≥ 0: `_hD : ∃ s : ℕ,
  Nonempty (D ≅ MultiplicativeType.splitTorus k s)`. No presentation is chosen
  and no positive-rank assumption is imposed.
- f is any group-scheme homomorphism: `(f : D ⟶ G)` with no immersion,
  injectivity, smoothness or restriction on its kernel.
- Existence of a conjugating rational point: the conclusion quantifies
  `g : 𝟙_ (Over (Spec (.of k))) ⟶ G.X`. The monoidal unit of the over category
  is the identity scheme over Spec k, so these are exactly G(k).
- Existence of a group homomorphism to the prescribed torus: `v : D ⟶ S`.
- The conjugation and factorization equality is
  `(toUnit D.X ≫ g) * f.hom.hom * (toUnit D.X ≫ g)⁻¹ =
  v.hom.hom ≫ i.hom.hom`. It is an equality in the group of k-scheme morphisms
  D -> G. Its left side is the conjugate by the constant section g, in exactly
  the node's orientation. Precomposition with any B-point x of D gives
  g_B f_B(x) g_B⁻¹ = i_B(v_B(x)). Thus the identity is required over every
  commutative k-algebra, including nonreduced ones; no rational-points-only
  surrogate and no surjectivity on B-points is used. Morphism equality itself
  works for test algebras in any larger universe as well.

Dependency declarations read and reused:

- `Field`, in `Mathlib.Algebra.Field.Defs` (def-weil-field).
- `AlgebraicGeometry.Smooth`, in `Mathlib.AlgebraicGeometry.Morphisms.Smooth`
  (def-sbc-smooth-morphisms), as used by the existing reductivity predicate.
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, its homomorphism category and
  group law on morphisms, in `Mathlib.CategoryTheory.Monoidal.Grp`;
  `CategoryTheory.IsMonHom` is the existing multiplication-compatibility class.
  The k-group-scheme specialization and subgroup conventions are documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` (def-sc-group-scheme).
- `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`,
  in `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`
  (def-weil-finite-type-morphism), inside `IsAlgebraic`.
- `ConnectedSpace`, in `Mathlib.Topology.Connected.Basic`
  (def-weil-connected-scheme), inside `IsReductive`.
- `AlgebraicGeometry.IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
  (def-weil-closed-immersion), directly on i and j.
- `AlgebraicGeometry.MultiplicativeType.splitTorus` and `.baseChange`, in
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`.
- `AlgebraicGeometry.ReductiveTorusCentralizer.IsReductive`, in
  `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`, and the
  `IsAlgebraic` and `IsUnipotent` definitions it reuses from
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`.

The public imports expose these statement dependencies. Available proof nodes
are imported privately: `Sheaf.AlgebraicGeometry.GroupScheme.AffineHomomorphismFlatImage`
(`AlgebraicGeometry.affineGroupHom_exists_faithfullyFlat_closedImmersion`),
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`AlgebraicGeometry.exists_topologicalKrullDim_le`) and
`WeilConjectures.Mathlib.Topology.KrullDimension` (the recorded dimension interface).
The proof-only nodes `lem-trf-lattice-torus-coordinates-action`,
`lem-sfb-field-split-torus-flat-quotient`, `lem-trf-split-lattice-torus-projection`
and `lem-sfb-field-maximal-split-tori-conjugacy` have no Lean record at this reading;
there is no module to import for them yet. Their uses remain in the theorem's
five-step proof docstring. They are not needed to type this statement.

Source and edge-case checks:

I read the local Milne PDF by `pdftotext -layout`: Theorem 12.9(b),(c), pp.233--234,
Definition 12.14 and the split-quotient sentence on p.236, the reductive-over-k
convention at the start of §25(a), p.544, and Theorem 25.10, p.546. The source
asserts rational conjugacy over k, and its quotient statement retains inseparable
kernels. The proof plan in the module follows all five steps of the node.

I checked rank-zero D and rank-zero S, the trivial homomorphism, and trivial G:
`splitTorus k 0` is the monoidal unit, the empty product is included by ℕ, and no
hypothesis excludes the trivial image. For k of positive characteristic p, a
p-power homomorphism of G_m with kernel μ_p is allowed; f has no embedding or
smooth-kernel condition. Finite fields and imperfect fields are allowed by the
bare `[Field k]`. A nonsplit reductive group with a proper maximal split torus
is allowed: `_hG` does not say that G splits, and `_hmax` tests only split tori.
The all-algebras morphism equality retains infinitesimal information.

Searches (2026-10-24; remote searches through msearch.py with group Q153 and this item):

- LeanFinder: "Over any field every homomorphism from a split torus to a connected
  reductive algebraic group is conjugate by a rational point into a fixed maximal
  split torus". Eight hits: field-extension Hom equivalences, abstract group
  extension conjugacy, root pairing, and number-field embeddings; no match.
- Loogle: `IsReductive, splitTorus, IsMaximalTorus`. No hits; unknown identifier
  `IsReductive` in Mathlib.
- LeanSearch: "A homomorphism from a split torus into a connected reductive group
  is rationally conjugate into a fixed maximal split torus". Eight hits concerning
  group extensions, conjugate algebraic roots and field embeddings; no match.
- msearch grep, subdirectory AlgebraicGeometry:
  `IsMaximalSplitTorus|split.torus.*conjug|conjug.*split.torus`. Zero hits.
- Direct rg of Mathlib, WeilConjectures, Sheaf and dag/lean_names_upstream.json
  for `field_split_torus_rational_containment|IsMaximalSplitTorus`: no hits.
  Direct rg of the group-scheme sources for `splitTorus|IsReductive` located the
  existing definitions above and consumers, with no existing rational-containment
  theorem. Direct rg of Sheaf for split tori, reductivity, unipotence and maximal
  split tori located `ToriMultiplicativeType`, `SolvableGroupStructure` and
  `ReductiveTorusCentralizerTerminology`; I read their complete relevant signatures
  and docstrings. The latter's `IsMaximalTorus` uses arbitrary tori, so it cannot
  replace the inline split-only maximality hypothesis.
- `grep -rn` for this node id in lean/WeilConjectures: no hits. Sheaf has only
  its proof-plan mention in the existing complete-DVR consumer.
- `python3 tools/blueprint_refs.py search 'maximal split torus'`: zero blueprint
  node matches. Existing DAG definition records were read directly and reused.

Validation: the delivered module compiled in both sandbox and final module mode
through scompile.py, within the 60-second limit, with no errors or unexpected warnings.

## Second reading by Q153

I reread the node and the completed module together, without launching another agent,
as the dispatcher explicitly forbids sub-agents. This is a second pass by the same
worker; the maintainer supplies the independent review.

The field and the three group schemes match the node. I expanded `IsReductive`
and its algebraic/unipotent predicates to verify smoothness, affine finite type,
geometric connectedness and geometric unipotent-radical triviality, rather than
assuming them from the name. I checked that the maximality quantifier uses a
splitting over k, whereas the library's `IsMaximalTorus` would test nonsplit tori
as well. Both S and D admit rank zero. i is a closed immersion and f is merely a
group homomorphism. The existential g has domain the terminal k-scheme, v has
codomain the specified S, and precomposition of the displayed equality gives
exactly the node's conjugation identity on every B-point, with the correct
orientation. No hypothesis on perfection, infinitude, algebraic closedness,
injectivity of f or smoothness of its kernel appears. No mathematical mismatch
was found and no statement correction was made. I clarified the theorem docstring
about the nonsmooth-kernel case. The node record changes only lean and the two
authorized additional dependencies on already landed definitions.
