## Worker report

The module `Sheaf.AlgebraicGeometry.ComponentRankOneClusterDimension` states
`AlgebraicGeometry.Scheme.Modules.component_rank_one_cluster_dimension`, with one
`sorry` proof and no new definitions. The item changes only in `lean`.

Source read: Franciosi--Tenni, *On Clifford's theorem for singular curves*, Lemma
3.6(i),(ii), printed pp.240--242, primary author-hosted PDF
https://pagine.dm.unipi.it/franciosi/lavori/clifford.pdf. The node uses its reduced
nodal specialization B = X = X_red and only the first degree bound. I also read
the node's full accepted six-step proof, including its separate empty-cluster
argument; the declaration docstring carries that plan. The node's explicit
canonical-section interpretation is retained.

Hypothesis and clause correspondence:

- Algebraically closed base field: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Scheme over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; the specified structure
  map throughout is `X ↘ Spec (.of k)`.
- Nonempty and connected: `[ConnectedSpace X]`. The Mathlib class extends
  `Nonempty X`, so no empty curve is included and no separate restriction is added.
- Projective and reduced: `[IsHProjective (X ↘ Spec (.of k))] [IsReduced X]`.
- Pure dimension one and nodal singularities: `D.pure_dimension` and `D.nodal`
  from the recorded `SubcanonicalClusterData`. The latter quantifies over closed
  points outside the smooth locus and supplies the completed local-ring
  isomorphism to `k[[u,v]]/(uv)` together with its equality on constants, so it is
  an isomorphism of local k-algebras, not just abstract rings.
- The two-connectedness hypothesis is `hTwoConnected`. It quantifies over all
  closed immersions `a : A ⟶ X`, `b : B ⟶ X` with reduced, nonempty sources.
  The subsets `P,Q` of `irreducibleComponents X`, their disjointness, union, and
  the two range equalities say exactly that A,B are complementary reduced unions
  of components, with no component in common. The canonical scheme pullback is
  `CategoryTheory.Limits.pullback a b`; its structure map is the first projection
  followed by a and the structure map of X. The displayed `2 ≤ finrank` is the
  required dimension of its structure-ring global sections, via H^0.
- The zero-dimensional closed cluster is `(S : Scheme.{u}) (i : S ⟶ X)` with
  `[IsClosedImmersion i]` and `D.zero_dimensional : topologicalKrullDim S ≤ 0`.
  This includes the empty cluster. There is no Cartier, reducedness, or support
  condition on S.
- The specified dualizing invertible module is `D.dualizing`, with invertibility
  and the natural Serre-duality representing isomorphisms stored in D. This uses
  the dependency's actual dualizing interface, not an arbitrary line bundle.
- Subcanonicity is explicitly `hSsub : IsSubcanonicalCluster i D.dualizing`.
  This matters because D alone permits an empty cluster without subcanonicity;
  the item's hypothesis still requires subcanonicity even for S empty.
- `F_S` is the existing `subcanonicalModule i D.dualizing`, defined from the kernel
  ideal sheaf and the tensor product. `V_S` in the conclusion is
  `scalarCohomology (X ↘ Spec (.of k)) (subcanonicalModule i D.dualizing) 0`.
  The existing `scalarGlobalSectionsEquiv` identifies this H^0 with `scalarObj`
  at `op ⊤`, the space used in the restriction hypothesis.
- `hRankOne` quantifies over every `C : irreducibleComponents X`. The map first
  applies `subcanonicalModuleInclusion`, and then `tensorPullbackTopSection` along
  `NodalIdealScalarGluing.componentι C`. The latter is the inclusion of the reduced
  component defined by its vanishing ideal, as verified in `ReducedNormalization`;
  despite its type's name, it does not normalize that component. The codomain
  module is the pullback of `D.dualizing`, not the pullback of the ideal twist.
  `Submodule.span k (Set.range ...)` is the image: both constituent maps are
  k-linear, so their range is already a subspace. Its `Module.finrank` is one.
- The first conjunct is exactly `dim_k V_S = subcanonicalSplittingIndex D + 1`.
  The index is the recorded definition, including its separate empty-cluster
  convention, not a new partition invariant.
- The second conjunct is the implication with antecedent
  `0 < subcanonicalSplittingIndex D`. Its inequality uses integer casts and is
  `r(S) ≤ 2*(1-eulerChar k (unit X))-2-length(S)`. Thus it is exactly the degree
  bound in the node, with no natural-number subtraction truncating the degree.
- The arithmetic genus notation expands to `1 - eulerChar k (unit X)` and the
  cluster length expands to `finrank` of `scalarCohomology (i ≫ p) (unit S) 0`.
  The displayed c(S) and h^i in the informal statement introduce notation only;
  neither adds a further assertion. The two actual conclusions are both present.

Recorded dependencies used (full source signatures and docstrings read):

- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (finite projective-space embedding).
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar` (integer alternating finsum).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst` (scheme fibre product).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  the singular closed-point condition is in the dependency's `D.nodal`.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.moduleCohomology`. The inherited
  `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`
  provides `Scheme.Modules.scalarCohomology`, defined by restriction of scalars
  on this module cohomology, and `scalarObj`, the actual section module.
- `Sheaf.AlgebraicGeometry.SubcanonicalSplittingIndex`:
  `Scheme.Modules.SubcanonicalClusterData`, `IsSubcanonicalCluster`,
  `subcanonicalModule`, `subcanonicalModuleInclusion`, `subcanonicalSplittingIndex`.
  Its supporting section-space and admissible-partition definitions were also read.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (the algebraically closed
  clause of def-weil-algebraic-closure; no algebraic-closure construction is needed).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents` and closedness of components.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`,
  `AdicCompletion.of`, as used in `SubcanonicalClusterData.nodal`.
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries (Fin 2) k` and its variables.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- The already-recorded proof dependency
  `Sheaf.AlgebraicGeometry.NodalIdealScalarGluing` supplies the existing canonical
  `AlgebraicGeometry.NodalIdealScalarGluing.componentι` used by the statement.
- `WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison` supplies
  `Scheme.Modules.tensorPullbackTopSection` and `scalarGlobalSectionsEquiv`.

All recorded proof-dependency modules are imported; imports used only for the
proof plan are ordinary imports. The three proof dependencies still without Lean
records (`lem-sfb-nodal-completed-normalization-model`,
`lem-sfb-closed-component-stalk-calculus`, `lem-trf-closed-union-pushout`) have no
module to import and are not needed for elaborating the statement.

Edge cases checked before writing:

- Empty X is excluded by the stated connectedness convention.
- Empty S is allowed by the dimension inequality. Its index is zero, so the second
  implication has false antecedent. The first conclusion still asserts dimension
  one under the rank-one and two-connectedness hypotheses; proof step 6 covers it.
- On an irreducible X the decomposition hypothesis has no nontrivial instance;
  the rank-one map to that component forces dim V = 1, matching index zero.
- For S meeting a node, nonreduced S, or a non-Cartier cluster ideal, the map uses
  inclusion into omega before restriction; no punctual torsion is accidentally
  counted in the rank-one image.
- Self-nodes do not introduce a second irreducible component or an extra block.
- There is no characteristic restriction and no extra finite-dimensionality
  assumption. Projective coherent cohomology supplies finiteness mathematically.
- Scheme and field universes are the existing framework's common universe u;
  a larger field/scheme pair can be accommodated by increasing u. No independent
  test-object universe makes any quantification vacuous.

Searches actually run with `msearch.py Q96 lem-sfb-component-rank-one-cluster-dimension`:

- LeanFinder: `Subcanonical cluster canonical sections rank one restrictions on every
  irreducible component dimension splitting index plus one`. Eight hits on simplicial
  pairing ranks and stalk/Grassmannian ranks; none is the cluster theorem.
- Loogle: `"finrank", "Scheme"`. Twelve hits on scheme-morphism ranks and residue
  degrees; none is this theorem.
- grep in Mathlib/AlgebraicGeometry:
  `splittingIndex|subcanonical|rank.one.*cluster`. Fifteen hits about subcanonical
  sites; no curve-cluster declaration.
- LeanSearch: `Subcanonical cluster with rank one canonical restrictions on all
  components has h0 equal to splitting index plus one`. Eight hits on valuation
  rank-one predicates, module stalk rank, and simplicial splittings; no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, and the upstream name index,
  for `subcanonical` and the item id. The project has the splitting-index definition,
  residual-duality theorem, and nodal scalar-gluing interface, all inspected; no
  declaration states this dimension-and-degree theorem. Generic subcanonical-site
  results are unrelated. Focused searches found the reused scalar-section and
  canonical pullback-section operations, avoiding any new helper definition.

Validation: `scompile.py` compiled the sandbox and final library module cleanly
(4.5 s and 4.6 s), with no errors or unexpected warnings. The initial elaboration
failures were repaired by qualifying the scheme pullback and supplying the ambient
`scalarObj` explicitly to `Submodule.span`. The statement and its mathematical
hypotheses were not changed. Every variable and universe is explicitly bound;
`autoImplicit` and `relaxedAutoImplicit` are false. All lines are at most 100 characters.

No new nodes, dependency repairs, statement correction, or disputed statement.

## Second reading by Q96

The delivered section recorded only a self-check, since no second worker was started. This
is an independent second reading by the maintainer reviewer. I read the node, its source
place (Franciosi--Tenni Lemma 3.6(i),(ii), with B = X = X_red), the 13 stmt_dep records, the
module `Sheaf.AlgebraicGeometry.ComponentRankOneClusterDimension`, and the declarations it
uses: `SubcanonicalSplittingIndex.lean` in full, `NodalIdealScalarGluing.componentι`,
`ScalarGlobalSectionsComparison.tensorPullbackTopSection` and `Cohomology/Defs.eulerChar`.

Below is the node statement as a list, with the Lean that renders each item and my verdict:

1. k algebraically closed: `(k : Type u) [Field k] [IsAlgClosed k]`. Correct.
2. X a nonempty connected projective reduced k-scheme: `[X.Over (Spec (.of k))]`,
   `[IsHProjective (X ↘ Spec (.of k))]`, `[ConnectedSpace X]` (which extends `Nonempty`), and
   `[IsReduced X]`. Correct.
3. X of pure dimension one, smooth except at ordinary nodes: `D.pure_dimension` and
   `D.nodal`. The second is a ring isomorphism of the completed stalk at every closed point
   outside `smoothLocus` with k[[u,v]]/(uv), compatible with k, so it is a k-algebra
   isomorphism. Correct.
4. Two-connectedness: `hTwoConnected`. A and B are closed immersions with reduced, nonempty
   sources. Their supports are ⋃P and ⋃Q, where P and Q are disjoint and their union is the
   set of all components. A reduced closed subscheme is determined by its support, so this
   is exactly "reduced unions of components with no common component". The fibre product is
   the scheme `pullback a b` (record def-pc-fibre-product), with structure map
   `pullback.fst ≫ a ≫ X ↘ Spec k`, and H^0 of its structure sheaf is Γ. The bound is
   `2 ≤ finrank`; A ∩ B is finite, so finrank is the true dimension. Correct. On an
   irreducible X there is no instance of the hypothesis, as there is no decomposition in the
   node.
5. S a zero-dimensional closed subscheme, possibly empty: `(i : S ⟶ X) [IsClosedImmersion i]`
   and `D.zero_dimensional : topologicalKrullDim S ≤ 0`, which includes the empty S.
   Correct.
6. S subcanonical: `hSsub : IsSubcanonicalCluster i D.dualizing`. D only gives
   `IsEmpty S ∨ subcanonical`, so stating `hSsub` explicitly keeps the node's hypothesis for
   S = ∅ as well. Correct.
7. ω_X, F_S, V_S, r(S): `D.dualizing`, `subcanonicalModule i D.dualizing` (= i.ker ⊗ ω),
   its `scalarCohomology … 0`, and `subcanonicalSplittingIndex D`, the recorded definition
   including its r(∅) = 0 convention. Correct, with no private copy.
8. Rank-one image for every component Γ: `hRankOne`. Each C is a component. The map is
   `subcanonicalModuleInclusion` (V_S ⊆ H^0(ω)) followed by `tensorPullbackTopSection` along
   `componentι C`. The latter is the closed immersion of the vanishing-ideal (reduced)
   subscheme on C, so its target is H^0(Γ, ω|_Γ). This is the canonical-section image the
   node asks for, not the tensor restriction of I_S. The span of the range is the image,
   because both maps are k-linear (`tensorPullbackTopSection_smul`). `finrank = 1` forces
   finite dimension one. `tensorPullbackTopSection` uses a chosen adjunction unit. A
   different choice changes it by a linear automorphism of the target, which does not change
   the rank, so the hypothesis does not depend on the choice. Correct.
9. Conclusion 1, dim V_S = r(S) + 1: `finrank … = subcanonicalSplittingIndex D + 1`. Correct.
10. Conclusion 2, r(S) > 0 ⇒ 2p_a − 2 − ℓ(S) ≥ r(S): an implication with antecedent
    `0 < r`, stated in ℤ as `r ≤ 2*(1 - eulerChar k (unit X)) - 2 - ℓ`. `eulerChar` uses the
    `X.Over` structure, and ℓ = finrank H^0(S, O_S) over `i ≫ X ↘ Spec k`. There is no
    truncated subtraction. Correct.
11. No Cartier, reducedness or support condition on S: none is present. Nothing stronger
    than the node is assumed.

Edge cases. Empty X is excluded, as in the node. Empty S is allowed: r = 0, the second
clause is vacuous, and the first claims dim = 1 (proof step 6). For an irreducible X,
`hTwoConnected` is vacuous and rank one gives dim V = 1 = r + 1. There is no characteristic
restriction. The universe u is shared by k, X, S, A and B, as the recorded
`SubcanonicalClusterData` requires; no quantification becomes vacuous.

Records. The node differs from live only in `lean`. The 13 dependency records are
byte-identical to live. `lean.statement` is verbatim in the file. Docstrings carry the source
place, the blueprint tag and the six proof steps. No line exceeds 100 characters, and
autoImplicit is off.

Advisory. `componentι` lives in the module of the theorem node
lem-sfb-nodal-ideal-scalar-gluing, which is a proof dependency and not a stmt_dep. It is
definitionally Mathlib's `(IdealSheafData.vanishingIdeal ⟨C, _⟩).subschemeι`, so the item
does not depend on that theorem. No change.

Mismatches found: none in the statement. Only this section was rewritten.
