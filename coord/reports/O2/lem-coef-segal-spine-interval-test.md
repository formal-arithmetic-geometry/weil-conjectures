## Worker report

The module `Sheaf.AlgebraicTopology.SegalSpineIntervalTest` states exactly the
interval-product spine test as `SSet.SegalSpace.spine_interval_test`, with one `sorry`.
It introduces no definitions. The theorem's docstring contains the four node proof steps,
including the prism-chain intersections, interval-preimage calculation, mapping pullbacks,
and induction using strict-pullback invariance. No statement correction or dispute is needed.

Clause-by-clause correspondence:

- Small simplicial spaces in fixed universes: `(V : SimplicialSpace.{u})`, where the
  published abbreviation is `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. The universe `u` is explicit
  and arbitrary. No object universe is equated with a smaller morphism universe.
- Reedy fibrancy and the consecutive-edge weak equivalences for every `m ≥ 2`:
  `(hV : IsSegal V)`. Its full definition is `IsReedyFibrant V ∧ ∀ m : ℕ, 2 ≤ m →
  Enhanced.IsWeakHomotopyEquivalence (segalMap V m)`. The first predicate uses the
  Reedy relative matching condition on `terminal.from V`; the second uses `pathSpace`,
  whose inner simplices are `SSet.Path` with the endpoint equations. Thus this is
  precisely the iterated strict fibre product in the node, not a strict Segal condition.
- Every `n ≥ 2`: `(n : ℕ) (hn : 2 ≤ n)`.
- `F(1)`: `discreteRepresentable.{u} 1`, whose outer degree is the standard
  representable set, constant in the inner direction. `F(n)` is defined the same way.
- `G(n)` is the existing `SSet.simplexSpine n`, made discrete in the inner direction
  by composing its simplicial set with `Functor.const SimplexCategoryᵒᵖ`.
  Its simplices have monotone vertex span at most one. For `n ≥ 2` these are exactly
  the simplices in a consecutive edge: if the minimum is less than `n`, use that
  minimum as the edge's first vertex; if it is `n`, the simplex is constant and lies
  in the last edge. Conversely an edge has span at most one. This also checks both
  endpoint vertices and all degenerate simplices. No second definition is written.
- The inclusion `G(n) ⟶ F(n)` is
  `Functor.whiskerRight (simplexSpine.{u} n).ι (Functor.const SimplexCategoryᵒᵖ)`.
  Its target is definitionally `discreteRepresentable n`.
- The inclusion `F(1) × G(n) ⟶ F(1) × F(n)` is that inclusion tensored with
  `𝟙 (discreteRepresentable.{u} 1)` on the left, using the published pointwise
  cartesian monoidal structure. This keeps the interval horizontal, rather than
  replacing it by a constant inner simplicial interval.
- Restriction from `Map(F(1) × F(n),V)` to `Map(F(1) × G(n),V)` is
  `mappingSpacePre` applied to that canonical tensor inclusion and `V`.
  The mapping simplicial set is the dependency's degree-zero internal hom, with
  q-simplices the specified maps from product with `cΔ[q]`.
- The conclusion is `Enhanced.IsWeakHomotopyEquivalence` of exactly this restriction,
  using the published realization-based weak homotopy equivalence predicate.

Dependency declarations read and used:

- `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian`:
  `SSet.SegalSpace.mappingSpace`, `mappingSpacePre`, and
  `reedy_cartesian_simplicial` (the recorded dependency theorem, reserved for the proof).
  The full signatures and docstrings were read. It publicly imports
  `Sheaf.AlgebraicTopology.SegalCartesianExponent`, supplying `SimplicialSpace`,
  `discreteRepresentable`, `IsReedyFibrant`, `pathSpace`, `segalMap`, and `IsSegal`.
  None is copied and the proof does not appeal to `cartesian_exponent`.
- `Sheaf.AlgebraicTopology.SimplexSpineInnerAnodyne`: `SSet.simplexSpine` and its
  subcomplex inclusion. The definition and theorem signature/docstring were read.
  Its already-landed owning node `lem-cbc-spine-inner-anodyne` is added to
  `stmt_deps` under brief-stage2 §5 (landed-node additions are permitted).
  No inner-anodyne conclusion is assumed by this statement.
- Proof-only import `Sheaf.AlgebraicTopology.KanPullbackFibrationInvariance`:
  `SSet.Enhanced.isWeakHomotopyEquivalence_pullback_map`, whose full signature and
  docstring were read. It handles both fibration legs without fibrancy of the objects.
- The proof dependency `lem-coef-segal-interval-cover` has no Lean record in the
  current shared DAG, so there is no module to import. Its complete statement was read
  and it is named in the proof docstring; it is not needed to type this statement.

Import-cycle note for the maintainer: do not add the new module as a proof import to
`SegalCartesianExponent` while the latter owns the shared definitions:
`SegalSpineIntervalTest → SimplicialSpaceReedyCartesian → SegalCartesianExponent`
would close a cycle. This is the same shared-definition issue already recorded in
`lem-coef-simplicial-space-reedy-cartesian.reviewed_lean`. Stage 3 should extract the
shared definitions before adding that reverse proof import. No downstream file is edited.

Edge cases checked before writing: `n = 2` is the first admitted case and gives the
union of edges `{0,1}` and `{1,2}`; a long edge `{0,2}` and the full triangle are excluded.
All constant simplices at vertices, including `0` and `n`, lie in the union. Inner
and outer degree zero remain present. The hypothesis excludes `n = 0,1` as the node
requires, without excluding any larger `n`. An empty Segal space is allowed: both
mapping spaces from these nonempty source spaces are empty and restriction is their
identity. A terminal or discrete constant Segal space is allowed, with no completeness,
connectedness, basepoint, nonemptiness, or objectwise replacement hypothesis added.
The construction takes the canonical product inclusion and contains no arbitrary map.

Searches on 2026-10-17 (all through the prescribed `msearch.py` wrapper unless noted):

- LeanFinder: `For a Reedy fibrant Segal simplicial space restriction from the interval
  times a simplex to the interval times its spine is a weak homotopy equivalence`:
  8 hits, all `StrictSegal` / `IsStrictSegal` spine bijection results for one simplicial set.
- LeanSearch: `The product of an interval with a spine inclusion induces a weak
  equivalence on mapping spaces into any Reedy fibrant homotopy Segal space`:
  8 hits, again `StrictSegal` spine maps and inverses, not this statement.
  Read Mathlib `AlgebraicTopology/SimplicialSet/StrictSegal.lean:275-325` to reject
  the closest results: bijectivity in a single simplicial set is a different hypothesis
  and conclusion from weak equivalences of bisimplicial mapping spaces.
- Loogle: `"spine", "WeakEquivalence"`: 0 hits.
- Mathlib grep: `SegalSpace|spine.*prod|prod.*spine`: 0 hits.
- Direct `rg` on upstream `WeilConjectures` for the same expression: 0 hits.
  Direct `grep -rn` for the item id: 0 hits. `dag/lean_names_upstream.json` has
  no `spine_interval_test` or `simplexSpine` declaration.
- Direct `rg` on `lean/Sheaf` for spines, `mappingSpace`, `IsSegal`, and interval
  products located the published Segal/restriction interface, the existing
  `SSet.simplexSpine`, and only a docstring mention of this item in
  `SegalCartesianExponent`. No existing theorem states this interval-product result.

Source: read Rezk Lemmas 10.1 and 10.3 and diagram (10.4) online at
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf
(printed pages 23--24). The node's mapping-space statement is the local-object
interpretation of Lemma 10.3, consistent with the recorded Reedy/Segal conventions.

Validation: the delivered module compiled cleanly using `scompile.py`, with no errors
or warnings. A separate scratch consumer also compiled: it checks by `rfl` that the
whiskered target is `discreteRepresentable n`, checks the restriction's exact domain
and codomain, and applies the theorem at `n = 2` in arbitrary universe `u`.
The scratch consumer is outside `lean/` and is not part of the delivery.


## Second reading by N2

Independently read the sandbox node and theorem together, the shared node, and the
recorded source and dependency declarations. The source is Rezk, not Stacks: the
node explicitly says no Stacks tag states this result. Read the online paper,
Sections 2.1--2.4 and 4.1, Theorem 7.1(3), and Lemmas 10.1 and 10.3 with diagram
(10.4), printed pages 23--24. Section 4.1 includes Reedy fibrancy in a Segal space;
Theorem 7.1(3) translates Lemma 10.3 into precisely this mapping-space assertion.
No completeness, connectedness, or choice of basepoint is assumed in that translation.
Also read Kerodon Example the project server, Tag 00JA, for the existing spine's exact definition.
Sources:
https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf
and https://kerodon.net/tag/00JA.

Object, hypothesis, and conclusion inventory with Lean correspondence:

1. Small simplicial spaces in fixed, arbitrarily large universes: the binder
   `V : SimplicialSpace.{u}` uses the existing abbreviation
   `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. Its object and morphism universes are those
   of the standard functor category; `universe u` is explicit. Verdict: exact.
2. The source's discrete representable `F(n)` has outer degree `k` equal to
   `Hom([k],[n])`, constant in inner degree. The existing
   `discreteRepresentable n := (stdSimplex.obj ⦋n⦌) ⋙ Functor.const SimplexCategoryᵒᵖ`
   is precisely this object. The interval is `discreteRepresentable.{u} 1`,
   in the horizontal direction. Verdict: exact.
3. For every `n ≥ 2`, the spine is the union of images of all consecutive edges.
   The imported `simplexSpine n` consists of monotone maps with last value at
   most first value plus one. A nonconstant such map has image exactly in an
   edge `{i,i+1}`. A constant map at `i < n` belongs to edge `{i,i+1}`;
   a constant map at `n` belongs to `{n-1,n}`. Conversely every simplex of a
   consecutive edge has that span bound. This identifies all simplices and
   operators with the node's union, including degenerate simplices.
   Verdict: exact for the stated `n ≥ 2`.
4. The actual inclusion `G(n) ⟶ F(n)` is
   `Functor.whiskerRight (simplexSpine.{u} n).ι (Functor.const SimplexCategoryᵒᵖ)`.
   Whiskering makes the existing outer subcomplex discrete in the inner
   direction; its codomain is definitionally `discreteRepresentable n`.
   Verdict: exact, with the recorded dependency rather than a private spine.
5. `V` is Reedy fibrant: `hV : IsSegal V` includes `IsReedyFibrant V`, which
   is the existing relative matching condition on `terminal.from V`.
   Read `IsReedyFibration` and its scoped Kan--Quillen fibration class.
   Verdict: exact; no additional fibrancy instance is required.
6. Every consecutive-edge comparison in outer degree `m ≥ 2` is a weak
   homotopy equivalence: the other conjunct of `IsSegal V` is
   `∀ m : ℕ, 2 ≤ m → Enhanced.IsWeakHomotopyEquivalence (segalMap V m)`.
   Read `segalMap`, `pathSpace`, and Mathlib `SSet.Truncated.Path₁`,
   `SSet.Path`, and `SSet.spine`: the data are consecutive edges with vertices
   and the source/target equations. For positive `m` the vertices are uniquely
   determined by the edges, yielding exactly the iterated strict fibre product
   in the node. Verdict: exact; no strict Segal bijectivity is assumed.
7. For every `n ≥ 2`: the explicit `(n : ℕ) (hn : 2 ≤ n)` comes after
   the arbitrary `V` and its hypotheses. The initial introduction of `G(n)`
   is a definition for each `n`, so this quantifier order agrees with the node.
   Verdict: exact.
8. The canonical product inclusion is
   `(𝟙 (discreteRepresentable.{u} 1)) ⊗ₘ` the whiskered inclusion in item 4.
   The existing pointwise cartesian monoidal structure gives
   `F(1) × G(n) ⟶ F(1) × F(n)`. Verdict: exact; no arbitrary map is substituted.
9. The specified mapping simplicial sets and their restriction are the recorded
   `mappingSpace` and `mappingSpacePre`. Read both definitions:
   `mappingSpace A X := ((ihom A).obj X).obj (op ⦋0⦌)` and
   `mappingSpacePre i X := ((MonoidalClosed.pre i).app X).app (op ⦋0⦌)`.
   The cartesian closed adjunction and Yoneda identify inner `q`-simplices with
   maps `A × cΔ[q] ⟶ X`, and the latter map with precomposition by `i`.
   Its source is therefore `Map(F(1) × F(n), V)` and its target
   `Map(F(1) × G(n), V)`, in exactly the stated direction. Verdict: exact.
10. The sole conclusion is `Enhanced.IsWeakHomotopyEquivalence` of this
    restriction. Read its definition in `EnhancedDiagramsCones.lean`: realization
    induces a bijection on components and on all positive based homotopy groups.
    Verdict: exactly weak homotopy equivalence, with no stronger fibration claim.

Dependency and scope review: read the full signatures and docstrings of
`SimplicialSpaceReedyCartesian.reedy_cartesian_simplicial` (in namespace
`SSet.SegalSpace`), `SSet.simplexSpine` and `simplexSpine_innerAnodyne`, and
`SSet.Enhanced.isWeakHomotopyEquivalence_pullback_map`. The latter requires
fibrations on both first cospan legs, as the proof docstring explicitly supplies;
it imposes no extra Kan-object assumption. The imported `IsSegal` and shared
definitions in `SegalCartesianExponent.lean` were read, not inferred from their
names. Only those definitions, not its downstream `cartesian_exponent` theorem,
occur in this statement. The extra statement dependency
`lem-cbc-spine-inner-anodyne` already exists with its recorded module on the base;
brief-stage2 §5 authorizes this addition. No new nodes or dependency modules are
part of this delivery. Read the unstated proof dependency
`lem-coef-segal-interval-cover`; there is still no recorded module to import.
The worker's reverse-proof-import cycle note remains valid.

Edge cases: `n = 2` includes exactly the two adjacent edges and all three vertices,
while the long edge `{0,2}` is absent. A constant simplex at the final vertex is
retained through the last edge, in every degree. `n = 0,1` are excluded by the
node itself; no admitted degree is removed. Both simplicial degrees still include
zero. The empty simplicial space is allowed: neither binder requires a point,
and mapping from either nonempty prism source into it is empty. The terminal
space and discrete nerves are allowed without any extra assumption. There are
no scheme, ring, characteristic, zero-object, or auxiliary index-set parameters.
The arbitrary inner universe `u` covers all small objects in the chosen universe;
there is no equality imposed between independently variable universes.

Independent searches on 2026-10-17, using different phrasing from the worker:

- LeanFinder through `msearch.py`: "Bisimplicial sets: mapping from a horizontal
  prism into a fibrant Segal object is weakly equivalent to mapping from the prism
  over its consecutive edges". Eight hits, all strict Segal definitions, path
  concatenation, and nerve-lifting results. None states this theorem.
- LeanSearch through `msearch.py`: "A homotopy Segal bisimplicial object satisfies
  the mapping-space restriction equivalence for the horizontal prism and its
  chain of consecutive edges". Eight hits: strict Segal, coskeletal, and
  nerve-lifting declarations. Read Mathlib `StrictSegal.lean:270--330` and the
  relevant `NerveAdjunction.lean` declarations: these concern bijective spines of
  single simplicial sets, not this weak mapping-space equivalence.
- Loogle through `msearch.py`: `"spine", "mappingSpace"`; zero hits.
- Direct `rg` in the upstream `WeilConjectures` tree for `segal|spine|bisimplicial`
  (case insensitive): no hits. Checked `dag/lean_names_upstream.json` for
  `spine_interval_test`, `simplexSpine`, and `SegalSpace`: no hits.
- Direct searches in Mathlib and project `lean/Sheaf` for interval/spine and
  prism terminology, followed by `mappingSpace` and `IsSegal`: existing spine
  and mapping constructions were found and used; only the downstream
  `SegalCartesianExponent` proof docstring mentions this interval-spine result.
  Other Segal, cotensor, and marked-prism modules have different statements.
  No exact existing declaration was found.

H5/H6/H8/H9: the delivered module introduces no definitions and proves nothing;
its only theorem has proof `by sorry`. Both docstrings identify Rezk and the
blueprint node. The theorem docstring gives all four DAG proof steps: chain
cover/intersections, interval preimages and cover test, mapping pullbacks and
fibration legs, and finite gluing induction. All binders and the sole universe
are explicit; no private definitions, local notation, or hidden instance binders
occur. All Lean lines fit within 100 characters. Statement imports and the
available proof-only dependency import match the plan.

Mismatches and repairs: no mathematical mismatch was found and the Lean module
was left unchanged. The node's `lean.statement` had collapsed the signature to
one line; replaced only that metadata string by the literal multiline signature
from the file, as the brief requests. No natural-language statement correction
or citer audit is needed. Added this independent second reading.

Validation: independently reran the required `scompile.py` from the sandbox;
`Sheaf.AlgebraicTopology.SegalSpineIntervalTest` compiled cleanly (no errors or
warnings), including its sandbox probe and library-form compilation. The single
file contains the complete delivery's Lean modules. The earlier scratch consumer
was also inspected: it checks the definitional representable target, exact
restriction domain/codomain, and application in arbitrary universe at `n = 2`.
