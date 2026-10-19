## Worker report

The repaired module is `Sheaf.CategoryTheory.CoreKanFibration`. It imports
`Sheaf.CategoryTheory.IsofibrationPullbackLimit` and reuses its existing
`SSet.Enhanced.coreMap`, the canonical restriction of any simplicial map to the
existing core subcomplexes. This repairs the returned duplicate declaration:
`coreMap` is not redeclared here, and the redundant `coreMap_range` helper is
also removed. The module states three postponed theorems:

* `SSet.Enhanced.coreMap_is_kan_fibration` binds
  `{C D : SSet.{u}}`, a simplicial map `p : C ⟶ D`, and
  `hp : IsIsofibration p`, and renders the first source clause as
  `modelCategoryQuillen.J.rlp (coreMap p)`.
* `SSet.Enhanced.core_eq_top_of_kanComplex` binds
  `{K : SSet.{u}} [KanComplex K]` and renders the second source clause as
  `core K = ⊤`.
* `SSet.Enhanced.core_kan_fibration` combines exactly those two clauses:
  `(∀ {C D : SSet.{u}} (p : C ⟶ D) (hp : IsIsofibration p),
  modelCategoryQuillen.J.rlp (coreMap p)) ∧
  (∀ {K : SSet.{u}} [KanComplex K], core K = ⊤)`.

Every theorem proof is `by sorry`; no definition with postponed data remains.
The source is Kerodon Propositions the project server (Tag 01EZ) and the project server
(Tag 019D), as recorded in the node. The first conclusion uses Mathlib's
`modelCategoryQuillen.J.rlp`, whose generators are the positive-dimensional
horn inclusions, so it includes all `n ≥ 1` and `0 ≤ i ≤ n` horn lifts and no
extra dimension-zero condition. The second conclusion is equality of
simplicial subcomplexes and carries no nonemptiness assumption. Since `core K`
consists exactly of the simplices all of whose edges are equivalences, this
equality also expresses the node's assertion that every edge is an equivalence.

The dependency declaration used is `SSet.Enhanced.core`, from
`Sheaf.CategoryTheory.EnhancedDiagramsCones` (the statement dependency
`def-cbc-enhanced-diagrams-cones`). The canonical map used in this module is
`SSet.Enhanced.coreMap` from `Sheaf.CategoryTheory.IsofibrationPullbackLimit`;
its source declaration has the signature
`def coreMap {C D : SSet.{u}} (f : C ⟶ D) :
(core C).toSSet ⟶ (core D).toSSet` and explicitly transports inverse-edge
witnesses through `f`. `SSet.Enhanced.IsIsofibration` is imported through
`Sheaf.CategoryTheory.IsofibrationExponentiation` and is the source-fixed
inner-fibration plus equivalence-edge lifting predicate used by `hp`.

I checked identity maps, maps to the terminal simplicial set, empty source or
target cores, an empty Kan complex, `\Delta^0`, one-dimensional horns, and
higher horns. These cases remain permitted by the statement; no hidden
inhabitedness, finiteness, characteristic, or universe equality was added.

Existing-definition searches were made with `msearch.py` (LeanFinder query
for an isofibration restricting to a Kan fibration on maximal/core Kan
subcomplexes; generic Kan and Quillen results only), `msearch.py` Loogle
(`Quasicategory`, `KanComplex`, `core`, `isofibration`; no exact result), and
`msearch.py` grep plus `rg` over Mathlib, the upstream `WeilConjectures` tree,
and project `lean/Sheaf`. Those searches found no exact theorem. The focused
project search did find the already existing `coreMap` in
`Sheaf.CategoryTheory.IsofibrationPullbackLimit`; it is now imported and
reused, as required by the repair entry. The module compiles cleanly with
`scompile.py`.

No `STATEMENT-DISPUTED` finding or statement correction was needed.

Repair validation: the node copy was refreshed against the current shared node;
only its `lean` field differs. The three retained theorem docstrings now carry
the corresponding six-step natural-language proof plan, and the two recorded
proof dependencies with available declarations are imported for stage 3.
The UTC record date comes from the machine clock.
At the second reading, `lem-coef-homotopy-category-triangle-calculus` has a
recorded Lean declaration, so its module is now imported for stage 3 as well.


## Second reading by Q37

I independently read the item statement and all six proof steps, the dependency
node `def-cbc-enhanced-diagrams-cones` and its recorded module, the definitions
`IsIsofibration` and `coreMap` in their owning modules, and the three available
proof-dependency declarations. I read Kerodon 01EZ (Proposition the project server), its
proof, 019D (Proposition the project server), and 01ES (Definition the project server) online. The source
places are Kerodon tags, not Stacks tags. The source has no standing finiteness,
nonemptiness or algebraic hypotheses. Kerodon uses target-fixed isomorphism
lifting in its definition; the node and the recorded `IsIsofibration` both use
the equivalent source-fixed convention, with the other orientation supplied by
inverse triangles as in the node's Step 2. There is no statement correction.

The complete object/hypothesis/conclusion list and its Lean rendering is:

1. Simplicial sets C and D, in a common arbitrary universe: `{C D : SSet.{u}}`
   in `coreMap_is_kan_fibration` and in the first universal of
   `core_kan_fibration`. Verdict: exact; `u` is explicitly declared and unrestricted.
2. Both are quasicategories: `hp : IsIsofibration p` unfolds to
   `Quasicategory C ∧ Quasicategory D ∧ InnerFibration p ∧ ...`.
   Verdict: exact; no extra instances are silently required by `coreMap`.
3. The simplicial map p: `(p : C ⟶ D)`. Verdict: exact, with no monomorphism,
   surjectivity, Kan-complex or equivalence assumption on p.
4. Inner-horn lifting and source-prescribed equivalence lifting: the remaining
   clauses of `IsIsofibration p` are `InnerFibration p` and, for every vertex c
   and edge e, `D.δ 1 e = p.app _ c → IsEquivalenceEdge D e → ...`, with a lifted
   equivalence e' satisfying `C.δ 1 e' = c` and `p.app _ e' = e`.
   Verdict: exact, including strict image equality and the prescribed source.
5. Equivalence edges and cores: the recorded `IsEquivalenceEdge` existentially
   specifies one inverse and both inverse triangles, and `core C` has membership
   `∀ a : ⦋1⦌ ⟶ n.unop, IsEquivalenceEdge C (C.map a.op s)`.
   Verdict: exactly all edges of each simplex, including degenerate ones.
6. The induced map on those cores: imported `coreMap p` has type
   `(core C).toSSet ⟶ (core D).toSSet`; I read its `Subcomplex.lift`
   construction, which applies p to the inverse and both triangles.
   Verdict: the actual canonical restriction, with no private copy or arbitrary map.
7. Every positive-dimensional horn lifts against that map:
   `modelCategoryQuillen.J.rlp (coreMap p)`. I read the Mathlib definition
   `J := ⨆ n, .ofHoms (fun (i : Fin (n + 2)) ↦ Λ[n + 1, i].ι)`.
   Verdict: exactly all n ≥ 1 and all 0 ≤ i ≤ n, with the given base simplex fixed.
8. Any Kan complex K: `{K : SSet.{u}} [KanComplex K]` in the second universal,
   independently of C, D and p. Verdict: quantifier order and scope agree.
9. Every edge of K is an equivalence, and its core is K as a simplicial subset:
   `core K = ⊤`. Verdict: exact combined rendering, not a weakened conclusion.
   Indeed for an arbitrary edge f, this equality puts f in the degree-one core;
   specializing its defining condition to the identity `⦋1⦌ ⟶ ⦋1⦌` gives
   `IsEquivalenceEdge K f`. Conversely that edge assertion puts every simplex
   in the core. Equality with top means equality of subcomplexes, not merely an
   equivalence of underlying spaces.

The two component theorems state the corresponding clauses separately; their
signatures and the combined signature introduce no unbound variables. All three
proofs remain precisely `by sorry`. There is no new definition or dependency
module in this delivery, no hollow data, no private or file-local construction,
and all docstrings cite the owning blueprint node and source. The combined
statement's docstring contains the six-step proof; the component docstrings point
to their respective steps. The exact recorded `lean.statement` was compared with
the file text and is unchanged. Only the item's `lean` differs from the base node.

Edge cases: an empty Kan complex is permitted and has top core, without choosing a
vertex; empty-source isofibrations and the empty-to-empty map are not excluded.
Identity maps, projection to the point, and the one-point Kan complex are included.
The dimension-one generators include both horn orientations; dimension two needs
the proof's two-out-of-three check; higher dimensions include both outer horns.
Dimension zero adds no lifting condition. There is no index set, ring, scheme,
characteristic or zero-object parameter; no spurious corresponding hypothesis is
introduced. An arbitrary `u` covers all sizes in the common universe convention.

Independent H4 searches used vocabulary different from the worker's queries:
`msearch.py` LeanFinder, “Every simplex of a Kan complex has invertible edges,
and categorical fibrations restrict to fibrations of their maximal infinity
groupoids”, returned only primitive Kan/quasicategory/fibration declarations;
Loogle `"KanComplex", "core"` returned no hit; grep
`maximal.*Kan|categorical.*fibration|invertible.*edge` returned no hit. I also used
`rg` for maximal, invertible, isofibration, core and the exact declaration names
across pinned Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`.
The ordinary-category core and anodyne pairing cores are different notions.
The only canonical restriction found is the already imported
`SSet.Enhanced.coreMap`; no exact existing theorem replaces this module.

Mismatch found and repaired: the worker report said the homotopy-category
triangle-calculus proof dependency lacked a recorded Lean declaration. It now
has `SSet.homotopyCategory_triangle_calculus` in
`Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus`. I opened its signature
(edge representatives and the exact triangle criterion), added its ordinary
proof-dependency import, and corrected that stale report sentence. No mathematical
statement or existing definition was rewritten. The earlier duplicate-coreMap
repair is independently verified: neither `coreMap` nor its redundant range helper
is redeclared. No maintenance repair note exists for this item in the shared clone.

Validation: the final module is compiled individually using the prescribed
`scompile.py` wrapper, with the default 60-second per-file limit. Delivery preflight
is run through `deliver2.py --no-push`, then the same wrapper delivers the packet.
