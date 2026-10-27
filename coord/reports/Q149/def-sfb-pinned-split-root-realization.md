## Worker report

Group Q149; item def-sfb-pinned-split-root-realization; stage 2, 2026-10-24.
The module `Sheaf.AlgebraicGeometry.GroupScheme.PinnedSplitRootRealization`
defines the data of a pinned split realization, its unpinned version, the specified
isomorphisms, and the split-reductive predicate. Every definition has actual data.
There are no theorems, axioms, or `sorry`s in this delivery. The original node's
statement is unchanged. The one additional statement dependency is the already
landed `def-sfb-split-torus-over-ring`, whose multiplicative group is used directly.
No new node or dependency repair is needed.

Source read: Brian Conrad, *Reductive group schemes*,
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Definitions 1.3.3
(printed p.27), 5.1.1 (p.136), and 6.1.1 (p.186), with the isomorphism discussion
on p.187. Definition 5.1.1 explicitly retains disconnected bases and constant
roots and coroots, and requires free root lines. Definition 6.1.1 chooses
trivializing simple-root sections and a base. The current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was also read. This supporting definition is not the unit statement.

Clause-by-clause correspondence (names below are in `AlgebraicGeometry.PinnedSplit`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Nonzero commutative A and S = Spec A | `[CommRing A] [Nontrivial A]` in `SplitRealization` and `PinnedRealization`; `Over (Spec (.of A))` |
| S-scheme with specified structure map | `Over` objects carry their actual `hom` |
| Group operations, all group diagrams, homomorphisms preserving them | Existing `Grp (Over ...)`, its `GrpObj`, and its morphisms; no abstract point group is substituted |
| Closed torus subgroup | `inclusion : T ⟶ G` and `closed : IsClosedImmersion inclusion.hom.hom.left` |
| Smooth, affine, finite presentation over S | `IsReductive`: `Smooth`, `IsAffineHom`, `LocallyOfFinitePresentation`, `QuasiCompact`, `QuasiSeparated` on the structure map |
| Every algebraically closed geometric fibre | `geometricBaseChange A Ω = (Over.pullback (Spec.map ...)).mapGrp`; quantifiers over `[Field Ω] [IsAlgClosed Ω] [Algebra A Ω]` include every ring homomorphism |
| Geometric connectedness and no nontrivial smooth connected normal unipotent subgroup | The existing `ReductiveTorusCentralizer.IsReductive` on every fibre; its full definition was read |
| Faithful representation and matrix unipotence | That predicate uses `SolvableGroupStructure.IsUnipotent`: smoothness, an actual closed immersion into GL_n, and `(matrix - 1)^N = 0`, `0 < N`, on every geometric extension |
| Normality after every algebra extension | The same field interface uses the actual existing `IsNormalSubgroupScheme`, not normality of rational points alone |
| Finite-rank free abelian M | `ReducedDatum.free : Module.Free ℤ M` and `.finite : Module.Finite ℤ M` |
| Actual dual Hom_Z(M,Z) | `Module.Dual ℤ M` in `.pairing` and `.evaluation` identifying the pairing with evaluation |
| Finite root and coroot subsets with correspondence | `Index`, `finiteIndex : Fintype Index`, and the two embeddings of `RootDatum Index M (Module.Dual ℤ M)` |
| Roots/coroots nonzero, pairing two | `RootPairing.root_coroot_two`; evaluation at zero is zero, so neither root nor coroot can vanish over ℤ |
| Both reflections preserve the sets and their correspondence | Mathlib's `reflectionPerm`, `reflectionPerm_root`, `reflectionPerm_coroot` in the same `RootDatum` |
| Reducedness Qα ∩ Φ = {α,-α} | `.reduced : pairing.IsReduced`; over a torsion-free finite free ℤ-module, integral linear dependence is equivalent to rational collinearity |
| Specified base with Q-linear independence and positive/negative integer expansions | `BasedDatum.base : pairing.Base`: ℤ-linear independence is equivalent to Q-linear independence after rationalization; additive-monoid closure is precisely nonnegative integer combinations, and negation gives the negative combinations |
| Positive roots | `positiveRoots` uses `D.base.IsPos`, the existing height-sign predicate |
| Empty roots and empty base allowed | No `Nonempty Index`, no nonempty-support assumption |
| Roots need not span rationalized M | No `RootPairing.IsRootSystem`, no root-spanning condition anywhere |
| Based-datum lattice isomorphism | `BasedDatumIso.lattice : M ≃+ N` (an abelian-group map is automatically ℤ-linear) |
| Carries Φ and Δ to the specified Φ' and Δ' | `.roots : D.Index ≃ E.Index`, `.root_eq`, `.base_eq` |
| Contragredient coroot preservation | `.coroot_eq`: the target coroot evaluated on `lattice m` equals the original coroot at `m` |
| Identification T ≃ D_A(M) | `splitting : T ≅ ringDiagonalizableGroup A M`, the recorded diagonalizable group |
| Geometric maximal torus, rank zero allowed | `.maximal` uses `ReductiveTorusCentralizer.IsMaximalTorus` on the actual pulled-back inclusion; its torus definition allows `n = 0` |
| Constant monomial character t ↦ e_m | `character`, constructed by the existing `hopfSpec` and `AddMonoidAlgebra.mapDomainBialgHom` of `zmultiplesHom M m` |
| Constant cocharacter e_m ↦ t^(y m) | `cocharacter`, the same construction applied to `y.toAddMonoidHom` |
| Roots of each fibre precisely prescribed monomials | `HasGeometricRootDatum`: the action's `smul` is the actual adjoint map; every prescribed root has its constant character, and membership in existing `RankOneRoots.roots` is equivalent to being one of those characters |
| Coroots are the actual rank-one reflection cocharacters | For each prescribed geometric root, `HasGeometricRootDatum` requires its constant cocharacter and an actual normalizer point whose conjugation acts on every character by `x / α^<x,ν>`; the dependency theorem uniquely identifies this cocharacter with the SL2 coroot |
| No characteristic restriction on roots/coroots | No characteristic hypothesis; characters remain full torus morphisms |
| Lie(H) is the dual-number kernel, with derivation module operations | Existing `GrpObj.Lie`, `GrpObj.lieEquiv`, `GrpObj.infPointsEquivTangentGroup`, and `GrpObj.tangentPoint`; the ring interface identifies it with `ker(H(A[ε]) → H(A))`, and its module law is the existing derivation module law |
| Lie(G)(R), v_R | `points G.X (DualNumber R)` and `points.map G.X (DualNumber.mapAlgebraMap R) (GrpObj.tangentPoint v)` in `HasWeight`; these are the actual extended tangent-kernel points |
| Inclusion of t into G(R[ε]) | `points.map G.X (TrivSqZeroExt.inlAlgHom A R R) (t ≫ i.hom.hom)` |
| Actual conjugation Ad(t) | The product `tε * v_R * tε⁻¹` in `HasWeight`, using the represented group law |
| χ_m(t) is evaluation of e_m | `monomialValue` evaluates `AddMonoidAlgebra.single m 1` via the canonical ΓSpec isomorphisms and the actual point; it is a unit because e_m e_(-m) = 1 |
| Weight equations over all commutative A-algebras | `HasWeight` quantifies over `R : CommAlgCat.{u} A` and every `t : points T.X R` |
| χ_m(t) v_R with actual module scaling | Precomposition with `DualNumber.scale (monomialValue e m t.left)`, restricted to A; this sends ε to χ_m(t)ε and leaves the constant term fixed |
| Exact weight submodule | `weightSpace` is the span of precisely the vectors satisfying those equations; these equations are A-linear, so the set being spanned is already a submodule (details below) |
| Lie(T) ⊕ direct sum of root modules is Lie(G) | `.decomposition` requires bijectivity of the actual map `v ↦ differential inclusion v.1 + DirectSum.toModule ... subtype v.2`; it is the canonical sum of the inclusion differential and the submodule inclusions |
| Each root module free rank one | `.rootLines : ∀ α, Nonempty (A ≃ₗ[A] weightSpace ... (D.pairing.root α))` |
| Chosen generator for each simple root | `PinnedRealization.pinning` indexed by `D.base.support`, with `.generates : span A {pinning α} = ⊤` inside that root module |
| Pinning-compatible S-group isomorphism | `PinnedIso.groupIso`, `.torusIso`, and `.inclusion_eq` |
| Torus map D_A(u⁻¹), correct variance | `.torus_eq` uses the existing `ringDiagonalizableGroupMap A u.lattice.symm.toAddMonoidHom` |
| Differential takes each specified Xα to X'_(uα) | `.pinning_eq`, using the root-index equivalence and `.base_eq` to type its target |
| Differential is postcomposition of dual-number points | `differential` is `lieEquiv` after the existing `infPointsMap` applied to the inverse `lieEquiv` |
| Forget generators and base for split realization | `PinnedRealization` extends `SplitRealization A M D.toReducedDatum`; the latter takes no base |
| Split reductive group admits these data | `IsSplitReductive` existentially quantifies an abelian lattice, reduced datum, split realization and an isomorphism of its group with G |
| No existence assertion | These are structures and predicates; no theorem inhabits them |

On the weight-space construction: under the existing equivalence between tangent
kernels and Lie modules, multiplying two tangent points adds their derivations;
ε-rescaling is multiplication of the derivation by its scalar. Extension of scalars
postcomposes these derivations. Conjugation by a fixed point also postcomposes the
point, hence acts linearly on this tangent kernel. Consequently zero satisfies
`HasWeight`, sums of satisfying vectors satisfy it, and A-multiples satisfy it.
The span in `weightSpace` therefore has exactly the stated set as its carrier;
it does not enlarge the weight condition. This parallels the existing field
weight-space interface but tests all algebra points, as this node requires.
There is no assumed identification of Lie(G)(R) with Lie(G) tensor R.

The normalizer-reflection formulation of the coroot is the equivalent formulation
expressly allowed in the node. On all characters, the integer k is fixed by
`ν ≫ x = id^k`. Conjugation by the normalizer element then acts as
`x ↦ x - kα`. The existing rank-one reflection theorem makes this cocharacter
unique and identifies it with the diagonal restriction of its rank-one SL2 map.
No arbitrary family of cocharacters, abstract Weyl group, or downstream existence
hypothesis replaces this characterization.

Dependency declarations used (their sources and full signatures/docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  the finite-presentation clause includes `QuasiCompact` and `QuasiSeparated`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, as used by the field predicate.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`; `Over.pullback` is the associated chosen pullback functor.
- `Sheaf.AlgebraicGeometry.RingDiagonalizableGroup`: `ringDiagonalizableGroup`,
  `ringDiagonalizableGroupMap` (same module as the corresponding dependency record).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.Algebra.DualNumber`: `DualNumber`, `DualNumber.eps`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`:
  `RankOneRoots.reductive_rankOne_reflections` and its public `RankOneRootInterfaces`
  (`Character`, `Cocharacter`, `roots`, `adjointMap`, `normalizer`, `multiplicativeValue`).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; its cited role is
  rationalization of the abstract lattice. The equivalent integral independence
  and reducedness interfaces avoid introducing a second tensor product.
- `Mathlib.Algebra.DirectSum.Module`: `DirectSum.toModule` and the actual `DirectSum`.
- Added landed dependency `def-sfb-split-torus-over-ring`:
  `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusOverRing`,
  `RingGroupSchemes.multiplicative`. It provides G_m over an arbitrary ring.
- Existing transitive interfaces: `ReductiveTorusCentralizer.IsReductive`,
  `.IsMaximalTorus`, `SolvableGroupStructure.IsUnipotent`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring` and `.Functoriality`
  provide `GrpObj.Lie`, `lieEquiv`, `infPointsMap`, `tangentPoint`, and `points.map`;
  `WeilConjectures.Mathlib.Algebra.DualNumber` supplies `mapAlgebraMap` and `scale`.
- Mathlib root datum interfaces are reused directly: `RootDatum`,
  `RootPairing.Base`, `RootPairing.IsReduced`, and `RootPairing.Base.IsPos`.
  `ReducedDatum` packages the required finite/free/reduced mixins and specifies
  the actual integral dual and evaluation; it does not redefine a root pairing.

Edge cases checked by reading the definitions and types:

1. Empty Index and empty base: no nonempty binder, no invalid choice of a root.
   The direct sum is zero and the canonical decomposition reduces to Lie(T) → Lie(G).
2. Zero-rank lattice and trivial group: allowed; rank-zero split tori exist in
   the reused maximal-torus interface.
3. Pure tori: the nonspanning/empty-root case retains arbitrary finite-rank M.
4. Characteristic two for SL2: the root character remains 2χ, which is a genuine
   nontrivial character despite zero differential. The definition never replaces
   it by its differential.
5. Disconnected A (e.g. a product of fields): the same lattice elements and the
   same coroots are required in every geometric fibre; componentwise unrelated
   root data are excluded, as in Conrad's Example 5.1.2.
6. Nilpotent test algebras are included by `CommAlgCat`; no restriction to fields,
   reduced rings, domains, or flat extensions enters the ring weight condition.
7. The zero ring is excluded exactly by the node's `[Nontrivial A]`.
8. All scheme, ring, lattice, and test-algebra universes are explicitly bound.
   Tests live in the base's universe, large enough to contain the universal
   coordinate algebras; there is no smaller independent test-algebra universe.
9. On a free rank-one module, `span {X} = ⊤` says precisely that X is a generator;
   it is stronger than X merely being nonzero over an arbitrary ring.
10. For u : M ≃ N the induced torus arrow uses u inverse, exactly the required
    contravariance. The differential is the specified postcomposition, not a
    freely chosen linear isomorphism.

Searches (all through the prescribed wrapper unless marked rg):

- LeanFinder: `Pinned split reductive group scheme finite reduced based root datum`:
  eight abstract root-system hits (`IsReduced`, `RootSystem.mk'`, etc.), no pinned
  group-scheme realization.
- LeanSearch: `pinned split reductive group scheme root datum`: eight hits including
  `RootDatum`, restriction of scalars, and root-system mixins; root datum reused,
  no matching realization definition.
- Loogle: `RootDatum, RootPairing.Base`: zero hits for the combined query.
- Mathlib grep: `PinnedSplit|IsReductive|GroupScheme` in `AlgebraicGeometry`: zero hits.
- Mathlib grep: `Pinned|pinned|ReducedDatum|IsReductive` in `LinearAlgebra/RootSystem`:
  zero hits. Direct reads found the existing `RootDatum`, `Base` and `IsReduced`.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for `PinnedSplit`, `pinnedSplit`,
  `PinnedRealization`, `BasedDatumIso`, `RootDatum`, `ReductiveGroup`, and the node id:
  no realization definition; existing field reductivity, root interfaces, Lie
  modules, and ring diagonalizable group found and reused. Unrelated `Pinned`
  hits concern derived pullback functors.
- The exact node-id search in `lean/WeilConjectures` had no hit; the upstream name
  inventory also has no collision with the declared `PinnedSplit` names.

Validation: `scompile.py Q149 def-sfb-pinned-split-root-realization <module>`
compiled the complete module cleanly, in required module mode, with no warning.
Compilation initially exposed that `ringDiagonalizableGroup A ℤ` forces ℤ into
A's universe. The final character/cocharacter maps use the identical `hopfSpec`
construction with the existing Laurent algebra, so no universe equality or
restriction on A was added. No live file was edited and no global build was run.

No STATEMENT-DISPUTED flag and no source/node fault remains.

## Second reading by Q149

I reread the original node and the completed module as a separate clause audit.
This is a self-audit, not a claim that another agent reviewed the delivery; the
assignment explicitly forbids starting other agents and supplies independent
maintainer review after delivery.

The table above was checked with both files open. The substantive checks were:
(a) no root-spanning or connected-base assumption is present; (b) all geometric
roots and their coroots use the same constant lattice elements; (c) the ring
weight equation tests every algebra and uses actual ε-scaling; (d) the direct
sum is the actual sum of inclusions, not an arbitrary equivalence; (e) generator
means spanning its rank-one module, not merely nonzero; (f) the torus map of
`PinnedIso` uses the inverse lattice map and the differential is actual
postcomposition. The fields of `BasedDatumIso` give precisely the prescribed
root, coroot and base correspondence.

This audit added explicit existence of the constant character for each root in
`HasGeometricRootDatum`, so the root correspondence cannot be read as a vacuous
implication, and added the named `positiveRoots` construction. The ring character
maps were checked against the Laurent Hopf-algebra definitions after the universe
repair. The span presentation of the weight submodule was checked against its
linearity as explained above, with no base-change tensor comparison assumed.
No change to the node's statement was necessary. All helper declarations belong
to the one composite notion in this node and are listed in `lean.declarations`.
