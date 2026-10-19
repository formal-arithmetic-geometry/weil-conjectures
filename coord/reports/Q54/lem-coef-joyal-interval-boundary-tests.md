## Worker report

This delivery states `SSet.joyal_interval_boundary_tests` in
`Sheaf.AlgebraicTopology.JoyalIntervalBoundaryTests`. It constructs the exact finite
free interval of the node, its distinguished edge, both endpoints, and the actual
boundary-cylinder subcomplex and inclusion. The one theorem has proof `sorry`.
Every definition has real data; none chooses data from a postponed existence theorem.
All helper declarations belong to the interval explicitly introduced in this node,
and are listed in `lean.declarations`. No new independent notion or dependency repair
is needed. The original statement and dependency lists are unchanged.

Source checked: Cisinski, *Higher Categories and Homotopical Algebra*, July 30, 2026
revision, https://cisinski.app.uni-regensburg.de/CatLR.pdf, Construction 3.3.1,
Proposition 3.3.2 and Definition 3.3.3 (printed pp.92–94), Remark 3.3.4 and Definition
3.3.7 (pp.94–95), and Theorem 2.4.19 (p.57). I opened the online PDF, read its free
left/right inverse construction and universal property and the boundary-cylinder
generators, and inspected the diagrams on PDF pages 109–110 (one-based).

The module uses the established parameter convention of the landed
`JoyalQuasicategoryCharacterizations` module: `M` is a model structure, `hcof`
identifies its cofibrations with degreewise injective maps, and `hweak` identifies
its weak equivalences with the exact enlarged-universe ordinary-hFun tests of
`SSet.exists_joyal_model_structure`. These bind the phrase “the Joyal model
structure”; they add no restriction to the maps or quasicategories in the node.
The model dependency supplies such an `M` in every universe. Its fibration class
is then determined by the model-category axioms. No selected model, private Joyal
weak-equivalence notion, or same-universe replacement of the hFun test is used.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Simplicial sets and operators in one universe | `SSet.{u}`; Mathlib's `stdSimplex`, `horn`, tensor product and subcomplex APIs, inherited from `EnhancedDiagramsCones` |
| The Joyal model structure | `M : HomotopicalAlgebra.ModelCategory SSet.{u}`, `hcof`, `hweak` as above; the independent `v` gives `SSet.{max u v}` testing objects exactly as in the dependency |
| Boundary is the union of proper faces, including empty boundary in dimension zero | Existing `SSet.boundary n`; `boundary_eq_iSup` identifies precisely that union and `boundary_zero` identifies `boundary 0` with bottom |
| Start from the edge a with vertices 0 and 1 | Start with `Δ[1]`; `JoyalInterval.edge` is its map through the two pushout inclusions |
| Freely adjoin b and its triangle with successive edges (a,b) and degenerate long edge at 0 | `firstAttachingMap` glues `𝟙 Δ[1]` on face [0,1] and `stdSimplex.σ 0 ≫ stdSimplex.δ 1` on face [0,2] using `horn₂₀.isPushout.desc`; `first` is its pushout along `Λ[2,0].ι` |
| Freely adjoin c and its triangle with successive edges (c,a) and degenerate long edge at 1 | `secondAttachingMap` glues `stdSimplex.σ 0 ≫ stdSimplex.δ 0` on face [0,2] and `𝟙 Δ[1]` on face [1,2] using `horn₂₂.isPushout.desc`, then maps through `firstEdge`; `obj` is its pushout along `Λ[2,2].ι` |
| Specified identifications and no further simplex relations | The pushout universal properties are exactly free attachment of a missing edge and its triangle; the horn contains all three vertices and the two already specified edges. Equivalently first attach the missing edge along its boundary, then the triangle along its boundary. No face is identified except through the explicit attaching maps |
| Finite simplicial set J | First conjunct `JoyalInterval.obj.{u}.Finite`; this is Mathlib's finiteness of the set of all nondegenerate simplices |
| Both endpoint inclusions | `endpoint (ε : Fin 2)` is `SSet.const (stdSimplex.obj₀Equiv.symm ε) ≫ edge`, from `Δ[0]` to the constructed `obj` |
| Kan anodyne is saturated all-horn generation | Existing `SSet.anodyneExtensions`; see cellular identification below |
| Both endpoints are Kan anodyne | `∀ ε : Fin 2, anodyneExtensions (JoyalInterval.endpoint.{u} ε)` |
| The degreewise union in the product | `boundaryCylinderSubcomplex ε n := (boundary n).unionProd (Subcomplex.range (endpoint ε))`; `unionProd` is the actual supremum of the two product subcomplexes |
| Its inclusion into Delta[n] times J | `boundaryCylinder ε n := (boundaryCylinderSubcomplex ε n).ι`; its codomain is `Δ[n] ⊗ obj`, the degreewise product |
| Every n ≥ 0 and both endpoints give trivial cofibrations | `∀ (ε : Fin 2) (n : ℕ), (M.categoryWithCofibrations.cofibrations ⊓ M.categoryWithWeakEquivalences.weakEquivalences) (boundaryCylinder ε n)` |
| Any map between quasicategories in one universe | `∀ {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)` |
| Joyal fibration if and only if the stated RLP tests | `M.categoryWithFibrations.fibrations p ↔ innerHornInclusions.rlp p ∧ ∀ (ε : Fin 2) (n : ℕ), HasLiftingProperty (boundaryCylinder ε n) p` |

Why Mathlib's Kan-anodyne notion is exactly the one specified: the definition
`SSet.anodyneExtensions` is the left lifting class of all-horn Kan fibrations.
`anodyneExtensions_eq_retracts_transfiniteCompositions` in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic` identifies it
with retracts of transfinite composites of pushouts of coproducts of the all-horn
inclusions. Its instances explicitly supply cobase-change, retract, transfinite
composition and isomorphism closure. The cellular formula gives the converse
minimality: in any class closed under the node's operations, a coproduct of
horn attachments can be well-ordered and attached one summand at a time by
pushouts, with unions/colimits at limit ordinals. Thus such a class contains
those cellular maps and their retracts. `modelCategoryQuillen.J` indexes exactly
`Λ[n+1,i].ι` for all `n : ℕ` and `i : Fin (n+2)`, so all positive dimensions
and both outer horns are included and dimension-zero horns are excluded.
No extra anodyne definition is introduced.

Dependency declarations read and used:

- `def-cbc-enhanced-diagrams-cones`:
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`, recorded main declaration
  `SSet.Enhanced.coneCategory`. I read its docstring and full signature and the
  file's simplicial-primitive convention: its `SSet`, `stdSimplex`, `horn`,
  `Quasicategory`, cartesian tensor and internal hom are the existing Mathlib
  notions, used directly here; its coherent-cone construction is not copied.
- `lem-coef-joyal-model-structure`:
  `Sheaf.AlgebraicTopology.JoyalModelStructure`,
  `SSet.exists_joyal_model_structure`. I read the whole signature and proof
  docstring; `hcof` and `hweak` are precisely its first two class descriptions,
  including the unrestricted enlargement universe. `M` is the structure whose
  own fibration/cofibration/weak-equivalence fields are used in the conclusion.
- Direct Mathlib construction interfaces:
  `SSet.horn₂₀.isPushout`, `SSet.horn₂₂.isPushout` and
  `CategoryTheory.IsPushout.desc` in `HornColimits` and `IsPullback.Defs`;
  `SSet.boundary`, `boundary_eq_iSup`, `boundary_zero` in `Boundary`;
  `SSet.Subcomplex.unionProd`, `unionProd.isPushout` in `Monoidal`;
  `SSet.Subcomplex.range` and `.ι` in `Subcomplex`;
  `SSet.anodyneExtensions` and its cellular characterization in
  `AnodyneExtensions.Basic`; `innerHornInclusions.rlp` in
  `Quasicategory.InnerFibration`; `SSet.Finite` in `SimplicialSet.Finite`.

The proof docstring retains all twelve node proof steps in full. Proof-only
imports cover the recorded modules for isofibration exponentiation, inner
anodyne pushout products, trivial Kan lifting of monomorphisms, boundary-cell
filtrations, accessible small-object factorization, and finite presentability
of presheaves. There is no recorded Lean module for the proof-only nodes
`lem-coef-homotopy-category-triangle-calculus`,
`lem-coef-infinity-core-kan-fibration`,
`lem-coef-presheaf-cylinder-model-recognition`, or
`lem-coef-presheaf-naive-fibration-whitehead` in the read snapshot, so there
is no proof import to add for them yet. None is needed to type this statement.

Edge cases checked before writing:

- `n = 0` is retained by the `ℕ` binder. `boundary_zero` makes the first piece
  empty, so the source is `Δ[0]` times the endpoint image, canonically the
  specified endpoint. There is no erroneous positive-dimension restriction.
- Both `ε = 0` and `ε = 1` occur, by `Fin 2`; the source point does not assume
  an arbitrary inhabited quasicategory.
- The interval has exactly two vertices, three nondegenerate edges a, b, c,
  and the two attached nondegenerate triangles. The two horns contain all their
  vertices, and the two attachments have distinct new missing edges. In the
  first triangle [0,2] is constant at 0; in the second it is constant at 1.
  The reverse edges b and c are not identified with each other.
- Finite means finitely many nondegenerate simplices, not finitely many total
  simplices across all degrees. Degeneracies are retained in every degree.
- Empty X and/or Y are allowed; there is no `Nonempty` hypothesis. In particular
  the map from the empty quasicategory to any quasicategory is covered; lifting
  tests whose top map cannot exist are simply vacuous, as required.
- All products, pushouts, simplicial subsets and p live in `SSet.{u}`. The
  independent `v` only enlarges the categorical-equivalence tests to `max u v`;
  no universe equality is imposed, including when u or v is zero.
- `HasLiftingProperty` is existence of a strict diagonal for each commutative
  square, exactly the node's condition; it imposes no chosen lift or uniqueness.

Searches for an existing statement or definition (all via the prescribed wrapper
unless a direct `rg` is explicitly named):

1. `leanfinder`, query “Finite simplicial interval built from two inverse triangles
   endpoint inclusions anodyne and Joyal fibrations tested by boundary cylinders”.
   Eight hits, chiefly `SSet.modelCategoryQuillen.J`, `.I`, simplex edges, and
   triangle witnesses. None states this finite-interval/Joyal boundary criterion.
2. `loogle`, query `SSet.horn, SSet.boundary`. Twelve hits for
   `SSet.prodStdSimplex` pairings of horns times boundaries. They concern Kan or
   inner-anodyne product combinatorics, not J or these Joyal cylinder tests.
3. `leansearch`, query “A finite simplicial interval formed by attaching two
   inverse triangles has anodyne endpoints and tests Joyal fibrations by its
   boundary cylinders”. Eight hits for Kan-Quillen fibrations, boundary/horn
   generating classes and abstract model cylinders; no matching theorem.
4. `grep`, query `anodyneExtensions|weaklySaturated|horn.*desc`, subdirectory
   `AlgebraicTopology`. Twenty-five hits; read `AnodyneExtensions.Basic` and
   `HornColimits` and reused their exact all-horn class and gluing maps.
5. `grep`, query `horn₂₀|horn₂₂|freely.*inverse|walking.*[Ii]so|JoyalInterval`,
   subdirectory `AlgebraicTopology`. Nine hits: the two horn pushout APIs and
   `CoherentIso`. The latter defines the nerve of the walking-isomorphism
   category, which identifies the inverse edges and contains arbitrarily high
   nondegenerate alternating simplices. It is not this finite free J.
6. Direct `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and the upstream-name
   index for `JoyalInterval|joyal_interval_boundary_tests` found no declaration.
   Direct `rg` in the upstream and project sources for
   `KanAnodyne|kanAnodyne|boundaryTests|intervalBoundary|hornPushout` also found
   no match. Searching the item id in the upstream source found no occurrence.
7. Direct `rg` for `horn₂₀|horn₂₂|freely.*inverse|free.*inverse.*triangle|walking.*[Ii]so|invertibleInterval|invertible_interval|joyalInterval|JoyalInterval`
   in Mathlib algebraic topology, upstream and project sources found only the
   horn APIs, Mathlib `CoherentIso`, and a proof-docstring mention of a different
   walking-isomorphism nerve. Existing project modules
   `JoyalQuasicategoryCharacterizations` and `JoyalFunctorEquivalenceTest` have
   different statements; only their model-parameter convention was followed.
8. DAG search for `Kan anodyne|Kan-anodyne|anodyneExtensions|anodyne.*saturat`
   found other anodyne results and the item itself, not a second finite-J
   definition. All pieces apart from the finite construction already belong
   to Mathlib or the two stated dependencies.

No statement correction, disputed statement, new node, or unusable statement
dependency was found. The two gluing compatibilities are checked by `decide`
inside the actual constructors; no postponed proof is hidden in a definition.

Validation: `scompile.py Q54 lem-coef-joyal-interval-boundary-tests` compiled the
module cleanly on the server under the default 60-second per-file limit, with
no warnings. The node's `lean.statement` is extracted verbatim from the final
signature. Only `lean` changes in the copied node. The required dry-run result
is recorded below after it completes.

## Second reading by Q54

I reread the node statement, its Cisinski source place, both dependency records, and
the complete Lean signature. The item-by-item correspondence is:

- The ambient simplicial sets, standard simplices, horns, degreewise products and
  functor simplicial sets are the `SSet`/`stdSimplex`/`horn`/tensor primitives from
  `EnhancedDiagramsCones`, all in universe `u`.
- The Joyal model structure is the explicit parameter
  `M : HomotopicalAlgebra.ModelCategory SSet.{u}` with `hcof` identifying its
  cofibrations with degreewise injective maps and `hweak` identifying its weak
  equivalences with the enlarged-universe hFun tests from
  `SSet.exists_joyal_model_structure`. These are exactly the two class hypotheses
  used by the sibling Joyal characterization and add no condition on the maps.
- The node's finite free interval `J` is rendered by
  `JoyalInterval.obj`: `firstAttachingMap` and `first` attach the edge `b` and the
  triangle `(a,b,id_0)` through `Λ[2,0]`, while `secondAttachingMap` and `obj`
  attach the distinct edge `c` and `(c,a,id_1)` through `Λ[2,2]`. The pushout
  universal properties give precisely the stated identifications and no others.
- Finiteness is `JoyalInterval.obj.Finite`, Mathlib's finite set of nondegenerate
  simplices. The distinguished edge is `JoyalInterval.edge`; the endpoint objects
  are `JoyalInterval.endpoint ε` for every `ε : Fin 2`.
- The boundary is Mathlib's `boundary n`, including `boundary 0 = ⊥`. The union
  `(∂Δ^n × J) ∪ (Δ^n × {ε})` is exactly
  `JoyalInterval.boundaryCylinderSubcomplex ε n`, formed with `unionProd` and the
  actual image `Subcomplex.range (endpoint ε)`, and its inclusion is
  `JoyalInterval.boundaryCylinder ε n`.
- Kan anodyneness is Mathlib's `anodyneExtensions`; its documented cellular
  characterization is the saturated closure of all `Λ[n,i] → Δ[n]` for `n ≥ 1`,
  with isomorphisms, pushouts, retracts and transfinite composition. The theorem
  asserts `∀ ε : Fin 2, anodyneExtensions (endpoint ε)`.
- The trivial-cofibration clause is rendered for every `ε : Fin 2` and `n : ℕ` as
  membership of `boundaryCylinder ε n` in the intersection of `M`'s cofibration
  and weak-equivalence classes.
- The final quantified objects are exactly arbitrary `X Y : SSet.{u}` equipped
  with `[Quasicategory X] [Quasicategory Y]` and an arbitrary map `p : X ⟶ Y`.
  The equivalence is between `M`'s fibration class and the conjunction of
  `innerHornInclusions.rlp p` with lifting against every endpoint cylinder.

The source construction (Cisinski, Construction 3.3.1, Proposition 3.3.2,
Definition 3.3.3, Remark 3.3.4, Definition 3.3.7, and Theorem 2.4.19, PDF
pp.92--95 and 57) confirms the left-inverse triangle has vertices `(0,1,0)` and
the right-inverse triangle `(1,0,1)`, with the long edges degenerate at 0 and 1.
The Lean attaching maps have exactly those faces. The source's saturated Kan
anodyne class agrees with `anodyneExtensions`, and its Joyal generators are the
same boundary cylinders and inner horns.

Edge cases checked: `n = 0` is included and gives the endpoint image because the
boundary is empty; both endpoints occur via `Fin 2`; `b` and `c` remain distinct;
the empty simplicial set is allowed for either quasicategory; no nonemptiness,
characteristic, or extra finiteness/Noetherian hypothesis is present; and `u` and
`v` remain independent, with `v` used only in `max u v` for hFun tests.

I repeated the required LeanSearch, Loogle/LeanFinder, and direct `rg` searches in
Mathlib, `WeilConjectures`, project `lean/Sheaf`, the upstream-name index, and DAG
nodes. They found only the reused horn, boundary, subcomplex, anodyne, and Joyal
model APIs; the walking-isomorphism nerve is a different infinite object. No
existing declaration states this theorem or defines this finite interval, and no
dependency declaration is unusable. No statement correction, new node, or
dependency repair was needed. The copied node's `lean.statement` is byte-for-byte
the theorem signature above. I found no mismatch to change.

Validation after this reading: `scompile.py Q54 lem-coef-joyal-interval-boundary-tests
lean/Sheaf/AlgebraicTopology/JoyalIntervalBoundaryTests.lean` completed cleanly in
1.5 seconds with no warnings other than the permitted postponed proof.
