## Worker report

Item: `lem-coef-infinity-fixed-edge-prism-coherence`.
Module: `Sheaf.CategoryTheory.FixedEdgePrismCoherence`.
Main declaration: `SSet.Enhanced.fixed_edge_prism_coherence`.

The module defines the actual fixed-edge simplicial set and the actual triangular
prism, then states the existence of their prescribed roof maps and strict naturality.
The only postponed proof is `fixed_edge_prism_coherence`; its docstring gives all seven
steps of the DAG proof. Definitions have explicit data and checked structural proofs.
No dependency node or statement is changed, and no extra node is needed: the helpers
are constructions expressly introduced in this item's own statement, or the record
packaging its asserted maps and equations.

### Hypotheses and objects

- The fixed containing universe is `universe u`, and both quasicategories are
  `D E : SSet.{u}` with `[Quasicategory D] [Quasicategory E]`. The letter D denotes
  the node's total quasicategory E; the letter E denotes its base B.
- The simplicial functor is exactly `p : D ⟶ E`. There is no inner-fibration,
  equivalence, or lifting hypothesis on p.
- The vertices are `x y z : D _⦋0⦌`. An edge with endpoints x,y is represented by
  `s : (leftMappingSpace D x y) _⦋0⦌`. Unfolding that recorded dependency in degree
  zero says precisely that the underlying 1-simplex `s.1` has initial vertex x and
  final vertex y. Thus this adds no hypothesis and omits no edge.
- Its image is `((leftMappingSpaceMap p x y).app _ s)` with vertices `p.app _ x`,
  `p.app _ y`, and `p.app _ z`. The underlying edge is definitionally `p.app _ s.1`.

### Every clause of the statement

1. `fixedEdgeSpace D s.1 z` has at degree n the subtype of `D _⦋n+2⦌` whose
   restriction along `fixedEdgeInclusion n` is s.1 and whose restriction along
   `fixedEdgeFinalFace n` is the constant n-simplex at z. The first inclusion sends
   0 to 0 and 1 to 1. The final-face inclusion is the composite of the two face-0
   maps, hence sends i to i+2. Its operators are
   `D.map (prependFirst (prependFirst f.unop)).op`, so fix exactly vertices 0 and 1.
   Identities, composition and the two constraints are proved by ordinal-map
   equalities and functor laws. The identical definition is used over the base.
2. `FixedEdgePrismData.r₀` and `.r₁` have the exact left-mapping-space codomains
   L(x,z) and L(y,z). The fields `r₀_simplex` and `r₁_simplex` characterize them in
   every degree by `D.map (SimplexCategory.δ 1).op` and `D.map (δ 0).op` respectively.
   These maps therefore cannot be replaced by arbitrary arrows.
3. `fixedEdgeTrianglePrism n : Δ[2] ⊗ Δ[n] ⟶ Δ[n+2]` is defined degreewise on
   the pair of order maps: row 0 gives 0, row 1 gives 1, and row 2 gives i+2.
   The values are monotone by the two input monotonicity conditions. Naturality
   is checked on the underlying order-map values. This is the exact prism q_n
   prescribed in the node, in the dependency's interval/triangle-first convention.
4. The field `e` lands in the dependency's `triangleFiber D x y z`, not an
   independently defined triangle space. The field `e_simplex` says that its
   inclusion into `(ihom Δ[2]).obj D`, uncurried using the Yoneda equivalence,
   is precomposition of the underlying simplex by `fixedEdgeTrianglePrism`.
   It specifies e on all simplices and all dimensions.
5. The fields `θ_edges` and `ℓ_edge` identify θ and ℓ with the recorded dependency's
   edge restrictions, in order 12,01 and 02 respectively, after the canonical
   arrow-space inclusions. These inclusions are monic: they are pullbacks of maps
   from Δ[0], and Δ[0] is terminal. Thus the fields specify exactly the dependency's
   maps, rather than arbitrary replacements.
6. `sU_edge` specifies sU as precisely the vertex in `arrowMappingSpace D x y`
   corresponding to the edge s. The constant map c_s is `SSet.const sU`.
   `boundary_pair : e ≫ θ = lift (r₁ ≫ j y z) (SSet.const sU)` is θe=(jL r1,c_s).
   `boundary_long : e ≫ ℓ = r₀ ≫ j x z` is ℓe=jL r0. These are equalities of
   actual simplicial maps, before taking homotopy classes.
7. The theorem's family j has exactly the all-dimensional left-prism formula of
   `left_pinch_comparison`. This determines the recorded dependency's canonical
   left pinch, using the Yoneda bijection, uncurry equivalence, and monic inclusion.
   We do not introduce a private mapping-space or pinch definition, and we do not
   choose data from an unconstrained existence statement. The existential j is
   characterized on every simplex, as in its recorded dependency theorem.
8. `θ_inv`, `θ_homotopy`, and `θ_inv_homotopy` express the inverse of [θ]. The field
   `composition_class` is a simplicial homotopy from jL r0 to
   `(jL r1,c_s) ≫ θ_inv ≫ ℓ`, precisely the displayed equality of homotopy classes.
   The arrow-space composition class [ℓ][θ]^{-1} is the one characterized by
   `mapping_composition`. `roof_equivalence` makes the left leg invertible up to
   simplicial homotopy; therefore this identity says the displayed roof represents
   precomposition. Its triangle witness is exactly the map e already specified.
   No strictly natural choice of homotopy inverse is asserted.
9. The family P provides this package for every quasicategory and all its specified
   edges and vertices. Consequently it supplies the same construction for the base,
   with exactly the image edge and image vertices, as requested.
10. `fixedEdgeSpaceMap p s.1 z` is the actual degreewise postcomposition map on T.
    Its construction preserves the two defining constraints by the naturality of p.
    The theorem quantifies existential vertical maps uxy, uxz, uyz, and v, each
    uniquely characterized by its equality with postcomposition after its canonical
    inclusion into the internal hom. Thus these are exactly the maps induced by p;
    this is not a theorem about arbitrary chosen comparison maps.
11. The next three equalities are the literal `e ≫ v = fixedEdgeSpaceMap ≫ e_B`,
    `r₀ ≫ leftMappingSpaceMap = fixedEdgeSpaceMap ≫ r₀_B`, and the same equation
    for r₁. The following three equalities state strict naturality of jL for xy,
    xz, and yz in the actual arrow spaces. These are p e=e_B p, p r_k=r_k p,
    and p jL=jL p with categorical composition written left-to-right.
12. The final equalities state that p carries sU to the image-edge vertex, that θ
    commutes with v and `uyz ⊗ₘ uxy`, and that ℓ commutes with v and uxz. Combined
    with the strict boundary formulas, these give exactly the strictly commuting
    roofs and triangle witnesses, including all their boundary maps. Together
    with `composition_class` in the two rows, they present the precomposition
    square with its specified commutation data. They do not merely assert an
    equality between unspecified homotopy classes.

### Dependency declarations inspected and used

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.diagramVertex`,
  the simplicial/internal-functor convention, and the actual Mathlib `SSet`,
  `Quasicategory`, products, and Yoneda models used by that module. Its declaration
  source and docstrings were read, including the recorded right mapping space.
- `Sheaf.CategoryTheory.LeftPinchComparison`: `SSet.Enhanced.leftMappingSpace`,
  `leftMappingSpaceMap`, `leftPinchPrism`, and `left_pinch_comparison`. The entire
  module, including the existential family's full characterization and proof
  docstring, was read. The main theorem's j uses precisely this characterization.
- `Sheaf.CategoryTheory.InfinityMappingComposition`: `SSet.Enhanced.triangleVertices`,
  `triangleEndpointMap`, `triangleFiber`, `triangleEdgePair`, `triangleLongEdge`,
  `MappingCompositionStatement`, and `mapping_composition`. Its full package and
  proof docstring were read; θ and ℓ are tied to its maps by the inclusion equations.
- The transitive `Sheaf.CategoryTheory.RightPinchComparison` source was inspected
  for `arrowMappingSpace`, `arrowMappingSpaceInclusion`, and `arrowEndpoints`.
- The published proof dependency `Sheaf.Paper.TrivialKanHomotopyEquivalence` is
  imported without `public`; its `SSet.exists_section_homotopy_equivalence` is the
  proof's section/inverse step. Its full statement and proof docstring were read.
- The Mathlib match for `def-weil-pbc-trivial-kan-fibration` is
  `SSet.modelCategoryQuillen.I.rlp`, and the match for
  `lem-weil-pbc-trivial-kan-lifts-monomorphisms` is `SSet.rlp_monomorphisms`, both
  in `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`. Their full
  definitions/signatures were inspected. That proof-only module is imported.

### Source and edge cases

Read online Kerodon [Proposition the project server](https://kerodon.net/tag/02LL), its
fixed-edge prism proof, [Remark the project server](https://kerodon.net/tag/02LM), and
[Construction the project server](https://kerodon.net/tag/01PF). They agree with the node.
No statement correction or dependency repair was necessary.

- At m=0, T consists of 2-simplices with first edge s and last vertex z. The
  final-face inclusion picks vertex 2, the two r maps pick edges 02 and 12, and
  q_0 is the identity on the triangle vertices. The lift proof is the inner
  2-horn on s and the prescribed edge yz, including empty boundary data.
- Degenerate edges, identity edges, repeated vertices, degeneracy operators,
  arbitrary face maps and noninjective ordinal maps are included. The ordinal
  operator and prism definitions are natural for all monotone maps.
- Mapping spaces may be empty. No nonempty or inhabitance hypothesis or
  arbitrary choice of an arrow to z occurs. In that case the empty maps and
  inverse conditions have their usual meanings. If D has no vertices then the
  universally quantified edge/vertex assertions have no instances, correctly.
- p may be the identity, a constant simplicial map, or any simplicial functor;
  no inner-fibration assumption is used in step 7 or added to the statement.
- One arbitrary universe u covers both categories and all the finite simplicial
  domains, without any site/universe equality or smallness restriction.

### Searches for existing declarations

All service searches used the prescribed `msearch.py N2 <item> ...`; its raw
records are in `searches.jsonl` in the sandbox.

- LeanFinder: “Fixed edge triangle prisms realize precomposition on quasicategory
  mapping spaces naturally under simplicial maps”. Eight hits concern individual
  `SSet.Edge.CompStruct.map_simplex`, truncated composition and edge maps. None
  states the fixed-edge space, all-dimensional prism, boundaries and naturality.
- Loogle: `SSet, SSet.Homotopy, SSet.Edge`. Zero hits.
- Mathlib grep: `fixedEdge|trianglePrism|leftPinch|coslice` in `AlgebraicTopology`.
  Zero hits.
- LeanSearch: “Fixed edge triangle prism induces a simplicial natural roof for
  precomposition in a quasicategory”. Eight hits concern Dold–Kan precomposition,
  edge definitions/maps, truncated composition and the quasicategory predicate.
  None is this statement.
- `rg -n 'fixedEdge|fixed_edge_prism|trianglePrism|leftPinch'` in upstream
  `WeilConjectures` and the side `lean/Sheaf`: only the recorded left-pinch
  dependency, which is reused; no existing main statement or T construction.
- `grep -rn 'lem-coef-infinity-fixed-edge-prism-coherence'` in upstream:
  no result. An exact-name rg for every new declaration in Mathlib, upstream,
  side modules and `dag/lean_names_upstream.json` found no collision.

### Validation

The prescribed `scompile.py` compiled the module cleanly, including its side-only
left-pinch dependency. A first draft's finite-index bookkeeping obligations were
repaired; the real prism and all final signatures compile. Every variable and
universe is explicitly bound (`autoImplicit false`). There are no new axioms,
no postponed definitions, no proved theorems, and one intended theorem `sorry`.
The delivery dry run and final delivery are run after the final file checks.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
