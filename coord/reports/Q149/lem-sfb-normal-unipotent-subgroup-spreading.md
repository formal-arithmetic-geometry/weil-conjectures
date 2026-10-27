## Worker report

The module states `AlgebraicGeometry.NormalUnipotentSubgroupSpreading.exists_model`.
The theorem alone has `sorry`. The two helper abbreviations `scalarChange` and `projection`
are real constructions: the existing `Over.pullback` functor mapped to group
objects, and its actual first fibre-product projection. The real Prop definition `IdentifiesInclusion` packages the specified comparison.
They introduce no new
mathematical notion and select no arbitrary map or group structure.

Hypothesis and conclusion correspondence:

- F is a field: `{F : Type u} [Field F]`.
- K/F is an algebraically closed extension: `{K : Type u} [Field K]
  [Algebra F K] [IsAlgClosed K]`. There is no algebraicity hypothesis on K/F.
- J is an F-group scheme: `J : Grp (Over (Spec (.of F)))` bundles the group
  operations and their identities, using the recorded `GrpObj` notion.
- J is smooth, affine, and finite type: `[Smooth J.X.hom]`,
  `[IsAffineHom J.X.hom]`, `[LocallyOfFiniteType J.X.hom]`,
  `[QuasiCompact J.X.hom]`. Affineness of the structure morphism to an affine
  spectrum is equivalent to affineness of the underlying scheme.
- J_K is the actual fibre product: `(scalarChange (algebraMap F K)).obj J`.
- N is a K-group scheme and its inclusion is a group homomorphism: `N : Grp ...`
  and `i : N ⟶ ...`. The latter bundles `IsMonHom`.
- N is a closed normal subgroup: `[IsClosedSubgroupScheme i.hom.hom]` and
  `[IsNormalSubgroupScheme i.hom.hom]`, the recorded upstream definitions;
  the former includes closed immersion, the latter normal range for every
  commutative K-algebra, and both include injectivity on all algebra-valued points.
- N is smooth and connected: `[Smooth N.X.hom] [ConnectedSpace N.X.left]`.
- N is nontrivial: `hne : ¬ Nonempty (N ≅ Grp.trivial ...)` is absence of a
  group-scheme isomorphism with Spec K and its unique group law.
- N is unipotent in precisely the matrix sense: `hN :
  SolvableGroupStructure.IsUnipotent N`. I read its complete definition: smoothness,
  an existential finite matrix size and closed subgroup representation, and for
  every algebraically closed extension and every point a positive nilpotence
  exponent for the matrix minus identity. Smoothness is repeated because it is
  separately stated by the node, but no extra mathematical assumption results.
- The subalgebra is a literal subalgebra of K, with the specified F-structure:
  `∃ A : Subalgebra F K, A.FG ∧ ...`; `A.FG` is finite algebra generation, not
  finiteness as an F-module or a finitely generated field extension.
- The model is an A-group scheme: `M : Grp (Over (Spec (.of A)))`.
- It is smooth affine and finite presentation: `Smooth M.X.hom ∧
  IsAffineHom M.X.hom ∧ LocallyOfFinitePresentation M.X.hom`. Affine morphisms
  are quasi-compact and quasi-separated, so together these are full finite
  presentation, not merely local finite presentation.
- Its inclusion in the fixed J_A is `j : M ⟶ (scalarChange
  (algebraMap F A)).obj J`, with `IsClosedImmersion j.hom.hom.left`.
  As a group homomorphism and closed immersion this is an injective subgroup
  on every test algebra; the upstream field-only subgroup class is not misused
  over the ring A.
- Normality over A is rendered literally: for every `B : Type u` with
  `[CommRing B] [Algebra A B]`, the range of
  `IsMonHom.monoidHom j.hom.hom (Over.mk (Spec.map ...))` is `.Normal`.
- Recovery of the specified inclusion: there is an isomorphism over Spec K preserving the group law
  `e : ((scalarChange A.val.toRingHom).obj M).X ≅ N.X` with `IsMonHom e.hom`, inside `IdentifiesInclusion J N i A M j`, and ordinary equality compares its two
  composites to J. The left composite is the projection M_K -> M followed by
  j and J_A -> J; the right is e followed by i and
  J_K -> J. Both arrows have domain the underlying scheme of M_K and codomain J.
  Both arrows are over Spec K already. By the universal property of
  J_K this is exactly the equation in J_K with its canonical pullback-composition
  identification. It does not permit replacing the given inclusion by another one.
- All geometric fibres: `∀ (E : Type u) [Field E] [IsAlgClosed E]
  (a : A →+* E), ...`. The ring map is arbitrary, including maps with nonzero
  kernel, and no F-algebra compatibility beyond its restriction from A is imposed.
- Each fibre is nontrivial, smooth, connected and matrix-unipotent: the first four
  conjuncts respectively exclude `Grp.trivial`, assert `Smooth`, `ConnectedSpace`,
  and the same recorded `IsUnipotent` on `(scalarChange a).obj M`.
- The fibre inclusion remains closed and normal: the final two conjuncts use
  `IsClosedSubgroupScheme` and `IsNormalSubgroupScheme` on the pulled-back j.
  Its codomain is the actual J_A base change to E, canonically J_E along F -> A -> E.
- There is no connectedness or reductivity assumption on J, and no perfectness
  assumption on F. Universes are explicitly bound and `autoImplicit false` is set.
  All rings, schemes and test algebras use the common ambient universe u of
  the recorded group-scheme and unipotence APIs, not an independently smaller
  universe that could make algebra-valued testing vacuous.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, `algebraMap`
  (def-pc-field-extension).
- `Mathlib.FieldTheory.IsAlgClosed.Basic` (through AlgebraicClosure): `IsAlgClosed`
  (def-weil-algebraic-closure); no `IsAlgClosure F K` is imposed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.trivial`
  (def-sc-group-scheme), with the generic group homomorphism and point-group APIs.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (def-sc-group-scheme-subgroup).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`;
  `Morphisms.Affine`: `IsAffineHom`; `Morphisms.FiniteType`:
  `LocallyOfFiniteType`; `Morphisms.QuasiCompact`: `QuasiCompact`;
  `Morphisms.ClosedImmersion`: `IsClosedImmersion`; `Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`, for their respective recorded definition nodes.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst` (def-pc-fibre-product); `Mathlib.CategoryTheory.Comma.Over.Pullback`
  and `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: `Over.pullback` and `mapGrp`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (def-weil-connected-scheme).
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `AlgebraicGeometry.SolvableGroupStructure.IsUnipotent`. The already landed node
  `def-sfb-solvable-group-structure` is added to stmt_deps under the express rule
  allowing existing landed notion nodes. No new definition node or dependency
  repair is needed; no statement or proof field is changed.
- `Mathlib.RingTheory.Adjoin.FG`: `Subalgebra.FG` is the finite-generation notion.

All proof dependencies with a recorded module/Mathlib match are imported, privately
when they are used only by the proof plan. Two proof nodes currently have no usable
recorded declaration (`lem-sfb-perfect-unipotent-additive-series` and
`lem-sfb-exact-algebraic-group-property-permanence`), so there is no module to
import for these proof-only prerequisites. Their eight-step proof plan is carried
in the theorem's docstring. They are not needed to type the statement.

Edge cases checked before writing:

- The trivial group is excluded exactly by hne; size-zero faithful matrix
  representations alone do not accidentally imply nontriviality.
- The empty scheme cannot satisfy the group-scheme unit over a field, and
  `ConnectedSpace` explicitly includes nonemptiness.
- Arbitrary positive characteristic and imperfect F remain allowed.
- K/F may be transcendental; neither module finiteness nor algebraicity is assumed.
- Disconnected J remains allowed. A unipotent subgroup of positive dimension is
  retained, with no demand that J itself be unipotent or connected.
- The case F = K and A = F is included. For geometric fibres all A -> E maps,
  not just the inclusion A -> K or maps from its fraction field, are quantified.
- The comparison is an isomorphism of group schemes and fixes the inclusion,
  not a bare isomorphism of underlying schemes or an arbitrary target comparison.

Searches for existing statements/notions:

- `msearch.py ... leanfinder "smooth connected normal unipotent subgroup spreads
  out finitely generated subalgebra"`: eight results, including
  `Algebra.Smooth.exists_subalgebra_fg` and `_finiteType`. These descend smooth
  algebras only, with no normal inclusion or nontrivial unipotent geometric fibres;
  none states this theorem.
- `msearch.py ... loogle "IsUnipotent, GrpObj, IsNormalSubgroupScheme"`:
  zero hits, unknown identifier `IsUnipotent` in the Mathlib search service.
- `msearch.py ... grep 'unipotent|Unipotent' AlgebraicGeometry`: zero hits.
- `rg` for unipotent/Unipotent in both project Lean trees finds the existing
  `SolvableGroupStructure.IsUnipotent` and extension theorem, but no spreading
  statement. Exact node-id search in `lean/WeilConjectures` has no match.
- DAG search for matrix unipotence locates def-sfb-solvable-group-structure;
  its full definition and the smooth-unipotent-extension signature were read.
- `tools/blueprint_refs.py search 'unipotent'`: only the curve-Sylow-trace blueprint
  unit matches; it does not define the needed normal-subgroup spreading theorem.
- Exact declaration/namespace search in `dag/lean_names_upstream.json` found no
  collision for the new theorem. No new mathematical definition is introduced.

Source check: opened Conrad's online PDF
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, printed p.104,
Exercise 3.4.1(i)-(ii). Part (ii) spreads a smooth affine normal closed subgroup
with a positive-length series and fppf additive quotients. The node deliberately
uses this spreading construction for the specified subgroup without carrying
along the reductivity/connectedness hypotheses of the exercise's contradiction
setup; the reviewed eight-step proof supplies this generality. No correction
or STATEMENT-DISPUTED flag is needed.

Validation: the file compiles through scompile.py against the published live build.
Only the expected declaration-uses-sorry warning is permitted. The final delivery
dry run additionally checks the exact node record, module and report.

Elaboration repair: the subalgebra inclusion is explicitly
`A.val.toRingHom`; the final comparison uses ordinary equality. The helper
`IdentifiesInclusion` contains real propositional data, with no postponed proof.
No heartbeat or timeout limit was increased.

## Second reading by Q149

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
