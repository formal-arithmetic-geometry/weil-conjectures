## Worker report

This delivery states `lem-coef-finite-inverse-tetrahedron` in
`Sheaf.AlgebraicTopology.FiniteInverseTetrahedron`. It changes only the item's
`lean` field. There are no new nodes, dependency repairs, statement corrections,
or disputed statements. The only postponed proof is the named theorem
`SSet.Enhanced.finite_inverse_tetrahedron`; it is `by sorry` and its docstring
reproduces all five steps of the node's proof. All seven helper definitions have
real data and belong to the quotient and canonical edge explicitly introduced
by this item's own statement.

Source read: Lurie, Higher Algebra, proof of Proposition B.1.6, forward (3)
and reverse (A1), printed pp. 1473--1474 (PDF indices 1472--1473), at
https://people.math.harvard.edu/~lurie/papers/HA.pdf. The displayed quotient,
central edge and final diagram-chase assertion agree with the node. I also read
the current blueprint ancestor's proof, paragraph 2 of
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`.
This foundational lemma supports that paragraph through the recorded pattern
calculus branch; no blueprint unit or proof route is changed.

Each hypothesis and clause is represented as follows:

| Node text | Lean rendering |
| --- | --- |
| Simplicial sets in any fixed input universe | Explicit `universe u`; all objects are `SSet.{u}`. |
| The edges `{0,2}` and `{1,3}` of `Δ³` | `inverseTetrahedronEdge02` and `inverseTetrahedronEdge13` use `yonedaEquiv.symm (stdSimplex.edge 3 0 2 ...)` and `yonedaEquiv.symm (stdSimplex.edge 3 1 3 ...)`. |
| Collapse `{0,2}` to a vertex | `inverseTetrahedronFirst` is `pushout inverseTetrahedronEdge02 (stdSimplex.isTerminalObj₀.from Δ[1])`. |
| Also collapse `{1,3}` to a vertex | `inverseTetrahedron` is the pushout of `inverseTetrahedronEdge13 ≫ inverseTetrahedronFirstMap` along the same unique map to a second `Δ[0]`. This is exactly the iterated pushout defining `Q`, up to the irrelevant order of the two legs of the first pushout. |
| The central edge `c` is the image of `{1,2}` | `inverseTetrahedronQuotient` composes the two canonical coprojections; `inverseTetrahedronCentralEdge` composes it with `yonedaEquiv.symm (stdSimplex.edge 3 1 2 ...)`. |
| Every small quasicategory `D` | `(D : SSet.{u}) [Quasicategory D]`, with no further assumptions. |
| Every equivalence edge `e : Δ¹ → D` | First conjunct: `∀ e : (Δ[1] : SSet.{u}) ⟶ D, IsEquivalenceEdge D (yonedaEquiv e) → ...`. Yoneda identifies the map with its one-simplex, without changing its endpoints or imposing any conditions on them. |
| There is a simplicial map `f : Q → D` | `∃ f : inverseTetrahedron.{u} ⟶ D, ...`. |
| Its restriction is exactly `fc = e` | `inverseTetrahedronCentralEdge ≫ f = e`, equality of simplicial maps, not merely a homotopy class or an isomorphism. |
| Every simplicial map `Q → D` carries every edge to an equivalence | Second conjunct: `∀ (f : inverseTetrahedron.{u} ⟶ D) (a : inverseTetrahedron.{u} _⦋1⦌), IsEquivalenceEdge D (f.app _ a)`. All one-simplices are quantified, including degenerate ones. |

Dependency interfaces were read in full before use:

- `def-cbc-enhanced-diagrams-cones` records
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its actual relevant definition is
  `SSet.Enhanced.IsEquivalenceEdge (C : SSet.{u}) (f : C _⦋1⦌) : Prop`:
  an inverse edge and two two-simplices whose boundary equalities witness both
  inverses. This is used directly, with no substitute predicate. Its public
  Mathlib primitives `SSet.Quasicategory`, `stdSimplex`, `yonedaEquiv` and
  `stdSimplex.isTerminalObj₀` were also read in their defining source files.
- Proof dependency `lem-coef-homotopy-category-triangle-calculus` records
  `Sheaf.AlgebraicTopology.HomotopyCategoryTriangleCalculus`, declaration
  `SSet.homotopyCategory_triangle_calculus`. Its statement gives both edge
  representatives in the presented homotopy category and the exact equivalence
  between a composite equation and `Nonempty (Edge.CompStruct f g h)`.
  This module is imported without `public`, as a stage-3 proof input.
- Mathlib's `CategoryTheory.Limits.pushout` and `pushout.inl` are used directly
  from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. These are
  canonical chosen colimits with their proved universal properties. None of
  the quotient data is chosen from an unproved existence theorem.

Edge cases checked mathematically before writing:

- Empty `D`: there are no maps `Δ¹ → D` and no maps from the inhabited quotient
  `Q`, so both conjuncts are vacuous; no `Nonempty` hypothesis was added.
- Degenerate `e` and equal endpoints: choose all tetrahedron vertices equal
  and all its simplices constant. Both extension and detection include this.
- Nerves of ordinary categories: the four faces impose `uv = 1`, `vw = 1`
  and `u = z = w` (categorical composition order as in the node). Thus the
  remaining edges really are invertible. A one-sided retraction alone cannot
  define a map from `Q`, since the other inverse equation is also forced.
- The quotient retains two vertices: collapsing `02` and `13` does not identify
  those disjoint vertex classes with each other. The attached points are two
  separate copies, not one common point.
- Every edge is quantified in the second conjunct, rather than only the central
  edge or only the six nondegenerate edges of the original tetrahedron.
- Arbitrary universe `u` is retained for `D`, the standard simplices and both
  pushouts. There is no restriction to a smaller universe and no universe equality.

Searches actually run on 2026-10-17:

- `msearch.py ... leansearch "Quasicategory equivalence edge finite tetrahedron quotient collapse opposite edges"`:
  eight hits, including `homotopicL_iff_homotopicR`, `instSetoidEdge`, and ordinary
  categorical opposite equivalences. None states either requested quotient assertion.
- `msearch.py ... leanfinder "An equivalence edge in a quasicategory extends to a three simplex with edges 02 and 13 collapsed, and every map from that quotient sends all edges to equivalences"`:
  eight hits, including `Truncated.Quasicategory₂.fill31`, `fill32`,
  `Quasicategory.hornFilling`, and `hornFilling'`. These provide horn fillers,
  not the quotient and its two universal assertions.
- `msearch.py ... loogle "SSet.Quasicategory, SSet.coherentIso"`: zero hits.
- `msearch.py ... grep "tetrahedron|walking.?isomorphism|inverse.?tetra" AlgebraicTopology`:
  one hit, `CoherentIso.lean:16`. I read its module description, the definition
  of the nerve `SSet.coherentIso`, and its inverse-structure declarations.
  It concerns the entire nerve of the walking isomorphism, not this finite
  quotient of a single tetrahedron.
- `rg` in the Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`
  directories for `inverseTetra`, `inverse_tetra`, `FiniteInverse`, `tetrahedron`,
  `Tetrahedron`, and the proposed final declaration names found no duplicate.
  A project hit in `MarkedAnodyneLiftingCalculus.lean:140--180` was read:
  its `SSet.Marked.equivalenceDetector` imposes two entire face-degeneracy
  relations and distinguishes edge `01`, a different construction from `Q`.
  The other hits concern operadic square factorization, not this quotient.
- `grep -rn "lem-coef-finite-inverse-tetrahedron"` in upstream `WeilConjectures`
  found no declaration. `dag/lean_names_upstream.json` and the
  `lean_names_upstream.py show` inventory supplied no matching statement.

The previous attempt's unchanged-node failure concerned a stage-1 split.
This is a stage-2 delivery: the already reviewed split is preserved exactly,
and the new `lean` binding makes the item's node genuinely change.

Validation: prescribed `scompile.py Q25 lem-coef-finite-inverse-tetrahedron`
compiled the module cleanly, including its check as a library module. No error
or warning was printed. The worker returns READY only after the prescribed
`deliver2.py Q25 lem-coef-finite-inverse-tetrahedron --no-push` prints OK.
The independent second reading and actual delivery belong to the next worker.


## Second reading by Q25

I independently read the complete item node, the sandbox module and its `lean`
record, both dependency-node statements and their recorded source modules, and
Higher Algebra B.1.6(3) and (A1), printed pp. 1473--1474, in the author's PDF
<https://people.math.harvard.edu/~lurie/papers/HA.pdf> (PDF indices 1472--1473).
The PDF text was available; its screenshot endpoint failed, so I checked the
explicit quotient and edge labels in the extracted text. The source constructs
Q by collapsing 02 and 13, extends the equivalence on 12 into the Kan core,
and asserts that every Q-diagram in an infinity-category sends all edges to
equivalences. The categorical-pattern, marked-edge and cocartesian-fibration
assumptions of the surrounding argument do not restrict this extracted lemma:
in (A1) its last reduction is to an arbitrary infinity-category C. There is no
Stacks source for this item. No repair note exists for this item.

The node's objects, hypotheses and conclusions, checked individually:

| Item in the informal statement | Lean rendering and verdict |
| --- | --- |
| Standard simplices in a fixed arbitrary universe | `universe u`, `SSet.{u}` and Mathlib `Δ[n]`; exact. |
| Opposite edges 02 and 13 in Δ3 | `inverseTetrahedronEdge02` and `inverseTetrahedronEdge13`; `stdSimplex.edge 3 0 2` and `stdSimplex.edge 3 1 3` become maps by `yonedaEquiv.symm`; exact, with the indicated order of vertices. |
| Collapse 02 to a point | `inverseTetrahedronFirst := pushout inverseTetrahedronEdge02 (stdSimplex.isTerminalObj₀.from Δ[1])`; exact simplicial pushout, with canonical quotient `inverseTetrahedronFirstMap := pushout.inl ...`. |
| Collapse 13 to a second point, forming Q | `inverseTetrahedron := pushout (inverseTetrahedronEdge13 ≫ inverseTetrahedronFirstMap) (stdSimplex.isTerminalObj₀.from Δ[1])`; exact iterated pushout. The two point legs are distinct copies. |
| Canonical image of Δ3 and central edge c | `inverseTetrahedronQuotient` composes the two `pushout.inl` maps; `inverseTetrahedronCentralEdge` precomposes with `yonedaEquiv.symm (stdSimplex.edge 3 1 2 ...)`; exact. |
| Every small quasicategory D | `(D : SSet.{u}) [Quasicategory D]`; exact, with no Kan, inhabitedness, size equality, or other extra instance. |
| Every equivalence edge e | `∀ e : (Δ[1] : SSet.{u}) ⟶ D, IsEquivalenceEdge D (yonedaEquiv e) → ...`; exact. The dependency's predicate requires a single inverse edge and both inverse two-simplices; Yoneda evaluates precisely this edge. |
| Existence of a simplicial map f from Q | `∃ f : inverseTetrahedron.{u} ⟶ D, ...`; exact, after D and e have been supplied. |
| Restriction fc equals e | `inverseTetrahedronCentralEdge ≫ f = e`; exact equality of maps. |
| Every map sends every edge to an equivalence | Second conjunct `∀ (f : inverseTetrahedron.{u} ⟶ D) (a : inverseTetrahedron.{u} _⦋1⦌), IsEquivalenceEdge D (f.app _ a)`; exact, all one-simplices, independently of the first conjunct's e. |

I read `IsEquivalenceEdge` in `EnhancedDiagramsCones.lean`, Mathlib's
`Quasicategory` class in `Quasicategory/Basic.lean`, `stdSimplex.edge` and the
Yoneda-map correspondence in `SimplicialSet/StdSimplex.lean`. The former records
both inverse equations, and the latter constructs the monotone map with the
specified endpoints. The proof-only import `HomotopyCategoryTriangleCalculus`
records edge representatives and the iff between the composite equation and
`Nonempty (Edge.CompStruct f g h)`, for arbitrary vertices and edges of D. It
therefore supplies exactly the proof's step 5, including degenerate long edges.
It is correctly imported without `public`. No private dependency copy, new
node or dependency repair is present or needed.

Edge cases: empty D has neither a map from Δ1 nor a map from the inhabited Q,
so both clauses are vacuous; it is not excluded by an instance. Degenerate e
and coincident endpoints are permitted and admit the constant tetrahedron.
In nerves of ordinary categories, faces 012 and 123 give uv=1 and vw=1,
while faces 013 and 023 identify u=z=w in the homotopy category; this checks
both inverses and rules out a one-sided-retraction mistake. The two classes
of vertices of Q remain separate. The second conjunct includes every degenerate
edge and every edge represented in either pushout leg. All constructions and
D vary with arbitrary u, including u=0; there is no finiteness, nonemptiness,
characteristic or zero-object assumption. There is no variable index set or
integer parameter n in the theorem; the only dimensions are fixed 0, 1 and 3.

Independent H4 searches on 2026-10-17 (the exact new calls are also in
`searches.jsonl`):

- LeanFinder: `Equivalence edge extends across the finite simplicial quotient of a tetrahedron with disjoint opposite edges identified with points`.
  Eight hits, including `SSet.horn.edge₃`, `horn₃₁.ι₃`, `horn₃₁.ι₂`,
  `horn.primitiveEdge` and `horn.primitiveTriangle`: horn inclusions and simplices,
  no quotient or requested universal assertions.
- Loogle: `SSet, CategoryTheory.Limits.pushout`.
  Two hits, `SSet.Subcomplex.unionProd.ιIso_hom_left` and its inverse analogue;
  these concern pushout products and do not define Q or state this lemma.
- LeanSearch: `A simplicial map out of the quotient of Δ3 collapsing edges 02 and 13 takes every one-simplex to an invertible edge`.
  Eight hits about `Edge.edge`, `Edge.map`, `Edge.ofTruncated`, `Edge.map_id`,
  `Edge.mk` and the simplex degeneracy epimorphism; no match.
- msearch grep: `pushout.*stdSimplex|stdSimplex.edge 3 [01] [23]|inverseTetra|finite_inverse`
  in `AlgebraicTopology`: six hits in horn pushouts and skeletons, no match.
- Direct `rg` on Mathlib's algebraic topology sources, upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for inverse-tetrahedron names, tetrahedra, collapsed edges and detectors;
  no existing copy of this construction or statement. I opened
  `CoherentIso.lean`: its object is the entire nerve of WalkingIso, not Q.
  I opened `MarkedAnodyneLiftingCalculus.lean:140--174`: its detector is a
  coequalizer imposing two face-degeneracy relations and uses distinguished
  edge 01. This is a different finite simplicial set, not Q.

H5--H9: each of the seven helper definitions has actual data, built from
Mathlib's existing colimit construction; no data comes from an unproved
existence theorem. The only theorem has `by sorry`. All eight declarations have
source/blueprint docstrings; the theorem's docstring contains all five proof
steps, including the precise inner horn, strict descent, four face equations,
substitution, and exact triangle criterion for all edges. No file-local notation,
private construction or local instance is used. All Lean lines have at most
100 characters, `autoImplicit` is false, and u and all variables are bound.

Mismatches found: none. No Lean, statement or definition changes were needed;
I preserved the worker's module and node record. The only second-reader change
is this audit. The sandbox node differs from the read-only base only in `lean`;
its `lean.statement` is byte-for-byte equal to the theorem signature in the file.

Validation: prescribed `scompile.py Q25 lem-coef-finite-inverse-tetrahedron
lean/Sheaf/AlgebraicTopology/FiniteInverseTetrahedron.lean` succeeded, compiling
both the sandbox check (1.9 s) and the delivered library module (1.8 s), with no
errors or warnings. The delivery preflight and push follow this audit.
