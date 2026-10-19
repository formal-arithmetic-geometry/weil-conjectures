## Worker report

The module `Sheaf.CategoryTheory.LeftConeRestrictionCocartesian` states
`SSet.Enhanced.leftConeRestriction_cocartesian`, with its entire proof postponed as `sorry`.
It introduces no definitions, extra hypotheses, or changes to the mathematical node.
The node copy changes only `lean`. The earlier worker's duplicate-splitting refusal concerns
stage 1; this packet supplies the missing stage-2 Lean statement of the already split node.

I opened the full node, all three statement-dependency nodes and their recorded interfaces,
and the relevant source declarations and docstrings. I checked the source online:
[Kerodon 02VW, Corollary the project server(1)](https://kerodon.net/tag/02VW) gives restriction and
the apex criterion; [Kerodon 01UF, Remark the project server](https://kerodon.net/tag/01UF) gives
base-change stability and detection. These agree with the current node; no correction or
STATEMENT-DISPUTED flag is needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Small simplicial sets in a fixed containing universe | Explicit `universe u`, with `K E : SSet.{u}` and `B : SSet.{u}`. There is no dimension, finiteness, connectedness, or quasicategory hypothesis on `K`. All the simplicial sets are interpreted in the fixed containing universe, which can be chosen arbitrarily large. |
| `E` is a quasicategory | `[Quasicategory E]`. |
| `T = Δ⁰ ⋆ K`, with cone vertex `v` | The recorded `leftJoinCone K`; its vertex is `(orderedJoinInl Δ[0] K).app (op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0)`, the canonical pure left vertex, without a choice. |
| Internal functor simplicial sets | Mathlib `(ihom (leftJoinCone K)).obj E` and `(ihom K).obj E`. |
| Restriction `r_E` | `(MonoidalClosed.pre (leftJoinConeInclusion K)).app E`, using the recorded pure boundary inclusion. |
| `r_E` is a cocartesian fibration | First conjunct `cocartesianFibrationOver` applied to exactly that restriction. Its total and base functor objects are quasicategories by the recorded enhanced functor calculus, so the instance-free predicate expresses the same inner-fibration and edge-lift conditions here. |
| Every edge `η` is cocartesian iff its apex is an equivalence | Second conjunct quantifies over every degree-one simplex `η`; `SSet.yonedaEquiv.symm η` is its representing `Δ[1]` map for `IsCocartesianEdge`. The right side is `IsEquivalenceEdge E` applied to degree-one evaluation at exactly the pure left vertex. |
| For every quasicategory `B` and functor `h` | The last conjunct binds `∀ (B : SSet.{u}) [Quasicategory B] (h : B ⟶ (ihom K).obj E)`. |
| The degreewise pullback `P_h` | Mathlib `pullback h ((MonoidalClosed.pre (leftJoinConeInclusion K)).app E)`, with factors in the order `B ×_D Fun(T,E)`. Pullbacks in `SSet` are the existing degreewise construction. |
| `P_h` is a quasicategory | First conjunct inside the quantification over `B,h` is exactly `Quasicategory` of that pullback. |
| Projection `π : P_h → B` is cocartesian | Next conjunct applies `cocartesianFibrationOver` to `pullback.fst h r_E`. |
| Every pullback edge `(α,η)` is cocartesian iff `η_v` is an equivalence | Final universal quantifier runs over every degree-one pullback simplex `ε`. The left side uses its representing edge and `pullback.fst`; the right side first applies degree-one `pullback.snd` and then the same apex evaluation. Thus the actual compatible pair is retained, with no arbitrary map or omitted compatibility. |
| Empty `K`, empty `B`, and no limits or colimits in `E` | No `Nonempty`, chosen vertices of `K` or `B`, or categorical existence assumptions occur. The apex comes from `Δ[0]` even for empty `K`. |

Dependency declarations used:

- `def-cbc-enhanced-diagrams-cones`: module
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, in particular
  `SSet.Enhanced.IsEquivalenceEdge` and `SSet.Enhanced.evaluation`. Its recorded main
  declaration `SSet.Enhanced.coneCategory` was also read; this statement concerns the
  varying left join cone, not the fixed-boundary comma cone.
- `def-coef-infinity-relative-cone`: module `Sheaf.CategoryTheory.RelativeInfinityCone`,
  `SSet.Enhanced.leftJoinCone`, `SSet.Enhanced.leftJoinConeInclusion`, with the publicly
  reexported existing `SSet.Enhanced.orderedJoinInl` from
  `Sheaf.CategoryTheory.JoinSliceRightFibration`. The recorded relative-limit and
  relative-colimit predicates were read but are not needed in this statement.
- `def-coef-infinity-fibrations`: module
  `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`,
  `SSet.Enhanced.cocartesianFibrationOver`, and its reexported
  `SSet.Enhanced.IsCocartesianEdge` from `Sheaf.CategoryTheory.InfinityFibrations`.
  The newly recorded interface is used directly, so no instance is chosen from a
  postponed quasicategory theorem.
- Mathlib supplies `SSet`, `Quasicategory`, `ihom`, `MonoidalClosed.pre`,
  `SSet.yonedaEquiv`, `SSet.stdSimplex.obj₀Equiv`, `pullback`, `pullback.fst`, and
  `pullback.snd`. Their types are instantiated to the existing dependency objects.

All nine additional stated proof-dependency modules are imported without `public`:
`EnhancedFunctorConeCalculus`, `InfinityCocartesianCompositionInitiality`,
`InfinityCocartesianMappingCriterion`, `InfinityHomotopyPullbackPasting`,
`InnerMappingFiber`, `IsofibrationExponentiation`, `InfinityJoinConeCalculus`,
`InfinityMappingComposition`, and `KanHomotopyPullbackInvariance`, all under
`Sheaf.CategoryTheory`. The theorem docstring carries the complete five-step natural
proof: joint restriction and join comparison, mapping-space sufficiency, strict
identity-apex lifts, necessity by initiality, and base-change preservation and reflection.

Edge cases checked mathematically before writing:

- `K = ∅`: left cone is `Δ⁰`, so restriction is `E → Δ⁰` and its cocartesian edges
  are exactly equivalences; the base change is `B × E → B` with the same criterion.
- `K = Δ⁰`: cone diagrams are arrows and restriction is target evaluation; the
  source component, namely the left apex, must be invertible for a cocartesian edge.
- `B = ∅`: the pullback is empty, a quasicategory, and every lifting and edge test
  is vacuous. There is no hidden existence requirement.
- `E = ∅`: the total cone functor simplicial set is empty since the cone has a
  vertex; cocartesian lifts from its vertices are vacuous, including for empty `K`.
- `E = Δ⁰`: every evaluation edge is an equivalence and all compatible edges are
  cocartesian. Disconnected and nonquasicategorical `K` are not excluded.

Searches for an existing statement and declaration (2026-10-17):

- `msearch.py ... leanfinder`, query “Restriction from left cone diagrams to boundary
  diagrams is a cocartesian fibration with cocartesian edges detected by equivalence
  at the apex”: eight hits, including ordinary `CategoryTheory.Functor.IsCocartesian`,
  `IsStronglyCocartesian`, and `Limits.Cone.toCostructuredArrow`; none gives the
  simplicial cone-restriction theorem.
- `msearch.py ... loogle`, query
  `SSet.Enhanced.IsCocartesianEdge, MonoidalClosed.pre`: zero hits, unknown project
  identifier `SSet.Enhanced.IsCocartesianEdge` in the external index. Its actual
  recorded project definition was read locally and reused.
- `msearch.py ... grep`, regex
  `leftCone.*ocartesian|left_cone.*cocartesian|cocartesian.*cone`, subdirectory
  `AlgebraicTopology`: zero Mathlib hits.
- `msearch.py ... leansearch`, query “Left cone restriction between functor
  quasicategories is a cocartesian fibration and cocartesian edges are equivalences
  at the apex”: eight ordinary category cone and Kan-extension hits, including
  `Limits.Types.isLimitEquivSections`, `Limits.limit.cone` and `Limits.Cone.whisker`;
  no matching simplicial statement.
- `rg` with the same regex in the upstream `WeilConjectures`, project `lean/Sheaf`
  and `dag/lean_names_upstream.json`: only unrelated project cone-lifting, section
  colimit and relative-colimit docstrings. No matching declaration.
- `grep -rn` for the exact item id in upstream `WeilConjectures`: no hits.
- Exact proposed name `leftConeRestriction_cocartesian` searched in Mathlib,
  upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream-name index:
  no hits, so the new name has no collision.
- The existing `InfinityJoinConeCalculus` gives the join/comma comparison and
  `InfinityLaxCommaTargetFibration` gives a lax-comma target fibration; neither
  states this join-restriction theorem and both existing notions are preserved.

Validation: the delivered file passed the prescribed `scompile.py NP
lem-coef-left-cone-restriction-cocartesian` wrapper in both sandbox and library modes,
with no errors or warnings. Explicit `autoImplicit false` and the declared `universe u`
ensure all binders are explicit. Maximum Lean line length is 94 characters. The only
postponed theorem is the declaration matching this node; no definition data is postponed.

The worker does not write the independent second-reading section or push the packet.

## Second reading by NP

I reread the node statement, its Kerodon source places (02VW, Corollary the project server(1),
and 01UF, Remark the project server), and the three statement dependencies. The item-by-item
rendering and verdict are:

* The objects are a small simplicial set `K`, a quasicategory `E`, the left join
  `T = Δ[0] ⋆ K`, its canonical left vertex, and the restriction map. Lean uses
  `K E : SSet.{u}`, `[Quasicategory E]`, `leftJoinCone K`, the vertex from
  `orderedJoinInl Δ[0] K`, and
  `(MonoidalClosed.pre (leftJoinConeInclusion K)).app E`. These are exactly the
  recorded dependency constructions; no vertex or inclusion is chosen privately.
* The first conclusion, that restriction is cocartesian, is rendered as
  `cocartesianFibrationOver` for that map. This is the dependency's arbitrary-base
  interface, whose inner-fibration and prescribed-source cocartesian-lift clauses
  are exactly the source assertion here; no extra quasicategory instance is imposed
  on the total or base simplicial set.
* The edge criterion quantifies over every degree-one simplex `η` of
  `((ihom (leftJoinCone K)).obj E)`. Its left side is
  `IsCocartesianEdge` on `SSet.yonedaEquiv.symm η`; its right side evaluates `η` at
  the canonical cone vertex and applies `IsEquivalenceEdge E`. The quantifier and
  both directions of the equivalence match the node.
* For every quasicategory `B` and map `h : B ⟶ (ihom K).obj E`, Lean forms the
  degreewise pullback with factors in the node's order, using `pullback h r_E`.
  It asserts `Quasicategory` of that pullback, `cocartesianFibrationOver` of
  `pullback.fst h r_E`, and quantifies over every degree-one pullback simplex `ε`.
  The criterion evaluates the `pullback.snd` component at the same cone vertex,
  retaining the compatibility encoded by the pullback. All three clauses match.
* The hypotheses are exactly `K`, `E`, `[Quasicategory E]`, then `B`,
  `[Quasicategory B]`, and `h`; there is no finiteness, connectedness, nonempty,
  limit, colimit, characteristic, or universe-equality hypothesis. All objects use
  one arbitrary fixed universe `u`, as allowed by the source's containing-universe
  convention.

Edge cases checked: `K = ∅` gives restriction `E → Δ[0]` and the equivalence-edge
criterion at the unique cone vertex; `K = Δ[0]` gives target evaluation on arrows;
empty `B` gives an empty pullback with vacuous lifting and edge clauses; empty `E`
has no cone vertices and is covered vacuously; `E = Δ[0]` makes every tested edge an
equivalence; degenerate degree-one simplices and disconnected `K` are included.
No index set, finite product, or existence of a limit or colimit is used.

Searches were repeated by exact name and concept in Mathlib, the upstream
`WeilConjectures` source, the project's `lean/Sheaf`, and
`dag/lean_names_upstream.json`, using `msearch.py` LeanFinder/Loogle/grep queries
for left-cone restriction, simplicial cocartesian fibrations, apex equivalence, and
`leftConeRestriction_cocartesian`. Only ordinary-category cocartesian/cone results
and unrelated simplicial constructions appeared; no matching declaration exists.
The three dependency declarations and docstrings were opened directly. No repair
node or additional dependency is needed.

No mismatch was found, so no Lean or node statement change was made. The sandbox
node's `lean.statement` is verbatim the theorem signature. The module has one
postponed theorem proof (`sorry`), no hollow definitions, explicit `autoImplicit
false`, source/blueprint docstrings, and all stated proof-dependency imports. The
prescribed `scompile.py` compile passed in both sandbox and library modes with no
errors or warnings.
