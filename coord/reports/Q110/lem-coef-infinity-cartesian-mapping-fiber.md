## Worker report

Item: `lem-coef-infinity-cartesian-mapping-fiber`, group Q110, stage 2.
The module `Sheaf.CategoryTheory.CartesianMappingFiber` states
`SSet.Enhanced.cartesian_mapping_fiber`. Its only postponed theorem is this node itself.
All helpers have real data or are predicates; no object is chosen from a postponed existence
theorem. There is no statement correction, dependency repair, new independent notion, or
STATEMENT-DISPUTED finding. No repair handoff exists for this item.

Source checked online: [Kerodon Proposition the project server](https://kerodon.net/tag/01U8),
including its reduction to the interval, and the node's eight-step relative triangle proof.
The source concerns locally cartesian edges; a horn-cartesian edge as assumed by this node
is in particular locally cartesian. The node's stronger cartesian hypothesis is preserved.

The signature packages endpoints in `CartesianMappingFrame B s t`. This is a record of the
objects already quantified in the node, not an additional hypothesis. An arbitrary edge
`y → z` gives such data with `s = p(y)` and `t = p(z)` and every `w` in that strict fiber.
Conversely each frame is precisely such an edge, together with the specified fiber vertices.
`target : p(z) = t` just identifies the name `t`; it does not impose an additional property
on the edge or on the base. The vertex `y` in the strict fiber determines its upstairs vertex
through the actual pullback inclusion. Universe `u` is explicit everywhere, and
`autoImplicit false` is enabled. No equality between independent universes is imposed.

Hypotheses and clauses, individually:

- Quasicategories in a fixed universe: `B : SSet.{u}`, `[Quasicategory B]`, the frame's
  `E : SSet.{u}`, and `[Quasicategory F.E]`.
- Inner fibration `p : E → B`: `F.p` and `[InnerFibration F.p]`; there is no assumption
  that `p` is a cartesian fibration or has any other cartesian lifts.
- The specified cartesian edge: the frame's `e` is a degree-zero simplex of the existing
  `mappingSpace E y z`, equivalently an edge with exactly those endpoints. Its underlying
  1-simplex gives `he : IsCartesianEdge F.p (SSet.yonedaEquiv.symm F.e.1)`.
- `s = p(y)`, `t = p(z)`, `f = p(e)`: `y` is in `fiber F.p s`, `F.target` identifies
  the second endpoint, and `F.baseEdge = (F.baseMap F.y).app _ F.e`. The map `baseMap`
  is the dependency's `mappingSpaceMap F.p` followed only by the endpoint equality cast.
  Its source-endpoint equality is proved from `pullback.condition`, not assumed.
- The degreewise fiber `E_s`: the existing `SSet.Enhanced.fiber`; its factors are
  `{s} ×_B E` as specified in the recorded definition, canonically the node's ordered fiber.
- Every `w` in this fiber: `F.w : (fiber F.p s) _⦋0⦌` is arbitrary frame data.
- Left mapping space: `F.domain = mappingSpace (fiber F.p s) F.w F.y`.
- Total and base mapping spaces: `F.total` and `mappingSpace B s t` are the existing
  right-pinched mapping spaces with the indicated endpoints.
- Right homotopy fiber: `F.codomain = homotopyFiber (F.baseMap F.w) F.baseEdge` uses
  the recorded path model, with paths from the image to `f`, in exactly that orientation.
- The map is coherent postcomposition: `IsCartesianPostcomposition F c` specifies a
  simplicial family `σ` of relative `(n+2)`-triangles. Its face `n+2` is the input,
  face `n+1` is the output, last edge is `F.e.1`, and the full base simplex is
  `p(e) ∘ cartesianTriangleCollapse n`. The simplicial compatibility uses `appendLast`
  twice. These are the Q simplices and a section of its first face map in proof steps
  2--6. The homotopy-fiber path is fixed to the constant diagram at `f`. In step 6,
  the prism `[2] × [n] → [n+2]` identifies this relative triangle formula with the
  canonical composition class characterized by `mapping_composition`. Thus the helper
  specifies a representative of that class over the fixed edge; it does not replace
  canonical postcomposition by an arbitrary equivalence or unspecified nullhomotopy.
- Equivalence of spaces and Kan assertions: `IsCartesianMappingComparison F c` requires
  `KanComplex` for `F.domain`, `F.total`, `mappingSpace B s t`, and `F.codomain`, the
  preceding relative characterization, and the recorded realization-based
  `IsWeakHomotopyEquivalence c`.
- A second inner fibration: `F'` has the same `B,s,t`, with `[Quasicategory F'.E]` and
  `[InnerFibration F'.p]`. Fixed `s,t` express that the functor is over the same base.
- A functor over the base: arbitrary `T : F.E ⟶ F'.E` with `hT : T ≫ F'.p = F.p`.
  It is not required to be an inner fibration or to preserve other cartesian edges.
- The specified edge is taken to a cartesian edge: `_hee` identifies its whole image
  1-simplex with `F'.e.1`, and `_he'` asserts precisely its cartesianness. `_hw`, `_hy`
  identify the specified fiber vertices under the actual strict-fiber functor;
  `_hz` identifies `T(z)`. These are naming identifications for the second frame.
- Left naturality map: the conclusion supplies `a` and fixes its entire simplex by
  `(a.app n x).1 = (rightFibrationFiberMap F.p F'.p T hT s).app _ x.1`.
- Right naturality map: the conclusion supplies `m` applying `T` to each total mapping
  simplex, and `h` whose degreewise coordinates are exactly `(m(x), γ)`.
  Existence is asserted, so none of these exact specifications is a vacuous conditional
  assumption about a map that might not exist. Their coordinates determine them uniquely.
- Commutativity up to homotopy: `Nonempty (SSet.Homotopy (c ≫ h) (a ≫ c'))`.
  The clause works against every comparison `c'` with the same relative triangle
  characterization. Such comparisons exist by the theorem applied to `F'`; the section
  homotopy in the node's step 8 compares any two choices. This states naturality of the
  specified homotopy classes without pretending that a strict natural section is chosen.
- No further cartesian lifts: only `he` and `_he'` mention cartesianness.

Dependency declarations used (full source signatures and docstrings read):

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `mappingSpaceMap`, `appendLast`, `homotopyFiber`, `constantDiagrams`, and
  `IsWeakHomotopyEquivalence`. Their recorded constructors and realization convention
  are reused directly.
- `Sheaf.CategoryTheory.InfinityFibrations`: `SSet.Enhanced.fiber` and
  `IsCartesianEdge`; Mathlib's `SSet.InnerFibration` and `SSet.Quasicategory` are reused.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `SSet.Enhanced.mapping_composition`,
  its complete `MappingCompositionStatement`, triangle maps and component-category
  package were read. The relative triangle characterization is its relative representative
  as justified by the exact prism argument in proof step 6, not a second composition law.
- `Sheaf.CategoryTheory.RightFibrationFibers`:
  `SSet.Enhanced.rightFibrationFiberMap`. This declaration constructs the canonical
  pullback map using only the commuting equality; it does not require right-fibration
  hypotheses. Its already-landed node `lem-coef-infinity-right-fibration-fibers` is added
  to `stmt_deps`, as allowed for an additional landed declaration. Neither that node
  nor its module is modified.
- Proof imports: `Sheaf.CategoryTheory.InnerMappingFiber`, declaration
  `innerFibration_mappingSpaceMap_isKanFibration`;
  `Sheaf.CategoryTheory.RightPinchComparison`, declaration `right_pinch_comparison`;
  `Sheaf.AlgebraicTopology.KanPullbackPathComparison`, declaration
  `kan_pullback_path_comparison`; `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  declaration `SSet.KanQuillen.right_proper_kan_quillen`.
  Each is already a proof dependency of the node; the theorem docstring follows all
  eight proof steps, including degree-zero lifting and section-choice naturality.

Edge cases checked before writing:

- Empty mapping spaces: no `Nonempty` assumption on any mapping space. If the input is
  empty, the triangle family is vacuous there; cartesianness forces the corresponding
  strict and homotopy mapping fibers empty. The asserted weak equivalence includes the
  component bijection and does not treat empty space as contractible.
- Empty total category/base: there are no frames with the specified vertices. No
  inhabitedness assumption was added to exclude these cases.
- Point base: the path model is the ordinary mapping space up to equivalence, and
  postcomposition by a cartesian edge over a point is postcomposition by an equivalence.
- `p = id`: a strict fiber is a point; the homotopy fiber of the identity mapping map
  over the specified edge is contractible, including a degenerate edge.
- `w = y`, degenerate base edge, degenerate cartesian identity edge, and `T = id` are
  included. No inequality between vertices or nondegeneracy hypothesis appears.
- Degree zero of the triangle family uses 2-simplices and both ordinary horn problems;
  degree zero is included in the universal `n : SimplexCategoryᵒᵖ`, not omitted.
- Nerves of ordinary Grothendieck fibrations reduce to the usual bijection between
  vertical arrows to `y` and arrows to `z` over `f`.
- A functor preserving only the one specified cartesian edge is permitted. The clause
  does not use the stronger `preservesCartesianEdges` or `cartesianFibration` predicates.

Searches performed for this item:

1. `msearch.py ... leanfinder` with query
   `Cartesian edge of an inner fibration gives equivalence from mapping space in fiber to homotopy fiber of mapping spaces`:
   eight results, all generic model-category statements (`PathObject.instFibrationP₁`,
   `PathObject.instFibrationP₀`, `CofibrantObject.homRel_equivalence_of_isFibrant_tgt`,
   `BifibrantObject.homMk_homMk`, `PrepathObject`/path fibration results,
   `SSet.modelCategoryQuillen.fibrations_eq`, Brown factorization, and fibrations in
   an over category). None gives the cartesian-edge mapping-fiber formula.
   The returned path-object and simplicial-fibration source signatures were inspected;
   they concern model-category path projections or all-horn fibrations, not this edge.
2. `msearch.py ... loogle 'IsCartesianEdge, mappingSpace, homotopyFiber'`:
   zero hits; the service does not index `IsCartesianEdge`.
3. `msearch.py ... grep 'cartesian.*mapping|mapping.*cartesian|homotopyFiber' AlgebraicTopology/Quasicategory`:
   zero hits. Local Mathlib grep in the same directory likewise found no formula.
4. `rg` in `WeilConjectures/` for `cartesian.*mapping|mapping.*cartesian|homotopyFiber`
   and the exact node id: no hits. The upstream-name index has no names for this node
   in either its blueprint or docstring tables.
5. `rg` in `lean/Sheaf/CategoryTheory` and `lean/Sheaf/AlgebraicTopology` for
   fiber/mapping/postcomposition patterns found the recorded dependencies above and
   consumers (notably `CartesianInitialBoundaryLift`), but no existing theorem stating
   this formula. Search for `CartesianMappingFrame`, `IsRelativePostcomposition`, and
   `cartesian_mapping_fiber` found no conflicting declarations. Existing canonical
   strict-fiber maps were inspected, and `rightFibrationFiberMap` was reused rather
   than rewritten. The existing `fiberPoint` belongs to a downstream consumer and
   is unnecessary here: arbitrary vertices of the recorded strict fiber are used directly.

Validation: `scompile.py Q110 lem-coef-infinity-cartesian-mapping-fiber` compiled
the module in sandbox and library mode with no errors or warnings. The endpoint
transport proof was adjusted to an explicitly typed morphism equality to avoid an
elaboration failure; no mathematical hypothesis changed. Prescribed delivery check:
`deliver2.py Q110 lem-coef-infinity-cartesian-mapping-fiber --no-push`.
Independent second reading and delivery are left to the next worker, as instructed.

## Second reading by Q110

Independent second reader: I did not write the module. I read the base node, its
sandbox copy, all four statement-dependency records and their actual declarations,
the composition package, the four proof interfaces, and the delivered module.
No repair note exists for this item. This is a Kerodon source, not a Stacks tag:
I opened https://kerodon.net/tag/01U8 and https://kerodon.net/tag/01U7, and also
01P8 and 0329. Proposition 01U8 states the forward implication even for locally
cartesian edges; the node deliberately assumes horn-cartesian edges. I preserved
that hypothesis. Notation 01U7 defines composition relatively over the fixed base
edge, rather than merely in the absolute mapping space. WANTED: an archived copy
of these Kerodon references; the node accurately records that they were read online.

My object/hypothesis/conclusion checklist, written from the node before matching
it to Lean, is as follows. Each entry passes.

1. A fixed universe of simplicial sets; quasicategories E and B; an inner
   fibration p:E→B. Lean: `B : SSet.{u}`, `[Quasicategory B]`, `F.E : SSet.{u}`,
   `[Quasicategory F.E]`, `F.p : F.E ⟶ B`, `[InnerFibration F.p]`.
   Mathlib's inner-fibration class is used directly. There is no assumption of a
   cartesian fibration, equivalence, Kan total space, or additional lifts.
2. An edge e:y→z and its cartesianness. Lean: `F.y` is a vertex of the strict
   fiber, `F.z` a vertex upstairs, and `F.e` a degree-zero simplex of the existing
   `mappingSpace` with exactly these endpoints. The theorem assumes
   `IsCartesianEdge F.p (SSet.yonedaEquiv.symm F.e.1)`. I read that predicate:
   it quantifies over final outer horns in every dimension at least two with
   the specified ordered final edge. This is the node's condition.
3. s=p(y), t=p(z), and f=p(e). Lean: `F.y : (fiber F.p s) _⦋0⦌`,
   `F.target : F.p.app _ F.z = t`, and `F.baseEdge = (F.baseMap F.y).app _ F.e`.
   The source endpoint equation in `baseMap` is derived from `pullback.condition`;
   it is not an extra hypothesis. `mappingSpaceMap` applies p to the complete
   simplex and `eqToHom` only identifies the endpoints. Specifying s and t with
   these equalities is equivalent to the node's naming of them.
4. The degreewise fiber E_s and every w in it. Lean: the recorded `fiber F.p s`
   is `{s} ×_B E`, canonically the reversed-factor pullback in the node;
   `F.inclusion` is its actual second projection. `F.w` and `F.y` are arbitrary
   vertices of that fiber. Every choice of the node's data yields a frame,
   since the point factor is unique, and every frame yields the node's data.
   The frame is a package of the quantified objects, not an additional property.
5. Left mapping space Map_{E_s}(w,y), total Map_E(w,z), base Map_B(s,t),
   and their induced map. Lean: `F.domain`, `F.total`, `mappingSpace B s t`,
   and `F.baseMap F.w`. I opened the dependency's `mappingSpace` and
   `mappingSpaceMap`: the entire initial face is constant and operators append
   the last vertex, exactly the right-pinched convention.
6. The homotopy fiber over f. Lean: `F.codomain = homotopyFiber
   (F.baseMap F.w) F.baseEdge`. Opening `homotopyFiber`, `comma`, and
   `commaSubcomplex` shows the path runs from the image to f. Both endpoint
   equations hold in every degree. No strict fiber is substituted for it.
7. Coherent postcomposition induces an equivalence of spaces. Lean:
   `∃ c : F.domain ⟶ F.codomain, IsCartesianMappingComparison F c ∧ ...`.
   This predicate includes `IsWeakHomotopyEquivalence c`, the recorded
   realization-based bijections on components and positive homotopy groups.
   Its `IsCartesianPostcomposition` clause requires a simplicial family σ
   of (n+2)-simplices, with input face n+2, output face n+1, final edge e,
   and full base simplex fρ_n; the path coordinate is constant at f.
   The two `appendLast` operations are precisely the extensions fixing the
   final two vertices. Thus σ is a section of Q→A in node proof steps 2–5.
   Conversely such a section gives exactly these equations. Step 6's prism
   sends its three restrictions to `(e,j a)` and `j b`, which matches
   `MappingCompositionStatement`'s specified θ and ℓ and fixes the canonical
   composition class. This is a relative representative of the prescribed
   class, not a freely supplied equivalence or nullhomotopy. The section and
   its path are existential conclusions, not assumptions that strengthen p.
8. The mapping spaces are Kan. Lean: the four `KanComplex` conjuncts for
   `F.domain`, `F.total`, `mappingSpace B s t`, and `F.codomain` include all
   spaces in the formula. The last assertion also makes explicit that the
   homotopy-fiber model is a space; it follows by the cited path comparison.
9. A second inner fibration over the same B and a functor T over B carrying
   the specified edge to a cartesian edge. Lean: arbitrary `F'` with its
   two instances, `T : F.E ⟶ F'.E`, `hT : T ≫ F'.p = F.p`, and `_he'`.
   The equalities `_hw`, `_hy`, `_hz`, `_hee` identify the second frame with
   the images of precisely the named vertices and edge. They do not restrict
   which functors occur: any T in the node gives those data. There is no
   global preservation-of-cartesian-edges requirement.
10. The naturality square has the map induced by T_s on the left and the
    induced homotopy-fiber map on the right. Lean existentially supplies a,m,h
    and specifies their full simplex coordinates. The formula for a uses
    `rightFibrationFiberMap F.p F'.p T hT s`; opening that definition confirms
    that it is `pullback.map` with identity point/base factors, with no
    right-fibration hypothesis despite its name. The formula for m applies T
    upstairs, and h has coordinates `(m(x),γ)`, retaining the base path.
    These equations determine the canonical maps, not just their components.
11. Commutativity up to homotopy and no other cartesian lifts. Lean:
    `Nonempty (SSet.Homotopy (c ≫ h) (a ≫ c'))`. It is required for every
    second comparison with the same section characterization. Such a comparison
    exists by this theorem on F'; the section homotopy in Q' compares all
    choices. Existential c precedes all second-frame and functor quantifiers,
    so the assertion does not choose c separately for each T. Only he and
    _he' require cartesianness, exactly as in node proof step 8.

Edge cases: empty mapping spaces are permitted (no Nonempty assumption, including
on a domain or codomain); weak equivalence still tests π₀. An empty base or total
simplicial set supplies no specified-vertex frame, exactly as in the node. A point
base reduces to postcomposition by an equivalence. The identity fibration has
point strict fibers and contractible identity-map homotopy fibers. Identities,
degenerate e or f, w=y, coincident endpoints, and T=id are included. At n=0 the
predicate requires an actual 2-simplex with faces d₂=input and d₁=output and edge
12=e, and the node's inner/final horn arguments cover it; no degree was omitted.
All categories and maps use arbitrary universe u as the node's fixed universe
requires. There are no coefficient, characteristic, scheme, index-set, or
finiteness parameters to restrict.

Independent searches using different words from the first reader:

- `msearch.py ... leanfinder "Relative morphism spaces over a fixed arrow are
  equivalent to fiber mapping spaces by composition with a cartesian lift"`
  returned eight ordinary-category fiber results: HasFibers.inducedMap, homLift,
  projMap, fiber_factorization, Functor.Fiber.homMk,
  Functor.IsFibered.pullbackPullbackIso, ChosenPullbacksAlong.Over.lift_left,
  and Over.pullback. Reading the ordinary fiber interfaces shows Category
  instances, Hom sets and unique factorization, not simplicial mapping fibers.
- `msearch.py ... loogle '"InnerFibration", "fiber"'` returned no hits.
- `msearch.py ... grep 'relative.*morphism|composition.*fiber|fiber.*composition'
  AlgebraicTopology/Quasicategory` returned no hits.
- Direct rg for mappingSpace, homotopyFiber, IsCartesianEdge, the item id and
  the new declaration/frame names in upstream WeilConjectures and the upstream
  name index returned no hits. Direct rg for cartesian/morphism/mapping and
  relative-morphism terminology in Mathlib's quasicategory directory and the
  project's CategoryTheory/AlgebraicTopology modules found the dependencies,
  ordinary or marked model-category material, the dual pointwise-cocartesian
  statement, and the downstream CartesianInitialBoundaryLift. None states this
  specified-edge formula with its naturality. Existing mapping spaces, fibers,
  composition, and strict-fiber maps are reused rather than defined again.

There are no new definition nodes or dependency modules to audit. Adding the
already-landed right-fibration-fibers node to stmt_deps is permitted by §5 and
records the exact helper used; its existing module and node are unmodified.
The sandbox differs from the base only in lean and that added stmt_dep.
There is no statement_change and no need for a citer correction audit.
All construction helpers have real data or are predicates. The only sorry is
this node's named theorem; its docstring follows all eight proof steps, and
all declarations have source/blueprint docstrings. All variables and universes
are bound, no file-local instances or notation occur, and every line is at most
100 characters. The node's lean.statement is verbatim the file's signature.

Mismatches and changes: none requiring a Lean or node repair. I retained the
correct statement and definitions and appended this independent review. The prescribed compilation and dry-run results are recorded below.

Second-reader validation: the prescribed `scompile.py` compiled this delivery's
only module in both sandbox and library modes, with no errors or warnings
(1.6 s and 2.0 s respectively). The prescribed `deliver2.py Q110 lem-coef-infinity-cartesian-mapping-fiber
--no-push` returned `OK (dry run)` at commit 76369af0ba: preflight and
compilations passed. The wrapper correctly omitted a concurrent lean_audit
update from the delivery; that maintainer-owned field is not part of our change.
