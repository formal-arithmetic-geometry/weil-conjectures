## Worker report

The single module `Sheaf.CategoryTheory.EnhancedDiagramsCones` states the whole
notion in `def-cbc-enhanced-diagrams-cones`. Its main declaration is
`SSet.Enhanced.coneCategory`; every helper is listed in `lean.declarations`.
All data are constructed. There are no theorems, axioms, `sorry`s, choices from
unproved existence statements, new nodes, or dependency modules. The node's
natural statement and dependencies are unchanged.

### Sources and dependency interfaces

Read the full node (statement, source, dependencies, proof, searches), both
statement-dependency nodes, and their recorded source declarations and docstrings.
The source is Scholze, *Six-Functor Formalisms*, Lecture II, Definitions 2.1--2.2
and facts (1)--(7), printed pp. 13--15. Read the archived PDF with `pdftotext`.
The right-pinched and comma conventions are specified explicitly in the node;
no closure theorem or cone-calculus theorem is added to this definition delivery.
Read the current `main-20261015` proof of `thm-cbc-finite-level-proetale`, whose
opening compactification choice is the historical use of this definition.

- `def-weil-size-convention` has `lean.convention: true`, with no declaration or
  module to import. Its explicit universe-bound convention is implemented by
  `universe u v`, `SSet.{u}`, and explicit topological-map universes `u`, `v`.
  All simplicial constructions take place in the same chosen upper bound; smaller
  data may be lifted into it. No additional smallness or nonemptiness assumption
  is imposed. All variables are bound, with `autoImplicit false`.
- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Its `mathlib_match` is used
  literally: `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`,
  `SSet.degenerate` and `SSet.nonDegenerate` in `...Degenerate`,
  `SSet.Subcomplex` in `...Subcomplex`, and `SSet.Finite` in `...Finite`.
  Their signatures and docstrings were read. No private simplicial-set or
  simplicial-subset interface is introduced. The last three primitives are
  part of the dependency's broader statement; finiteness is not assumed here.

### Hypothesis and clause correspondence

All names below that do not name Mathlib are in namespace `SSet.Enhanced`.
Auxiliary constructions on `SSet` are defined for arbitrary simplicial sets,
so they also apply to the quasicategories and Kan complexes specified by the node.
They do not assert that the construction is a quasicategory or a Kan complex;
those are the downstream cone-calculus node's theorems.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Chosen universes and simplicial sets | Explicit `u`, `v`; existing `SSet.{u}` = `SimplexCategoryᵒᵖ ⥤ Type u` |
| Standard simplex, monotone maps, precomposition | Existing `SSet.stdSimplex`, `SSet.stdSimplex.objEquiv`; the universe lift of Yoneda |
| Horn omits a vertex other than its index | Existing `SSet.horn`, imported through `Quasicategory.Basic` |
| Enhanced category = inner-horn quasicategory | Existing `SSet.Quasicategory`, whose inner-horn condition is used directly; no second bundled notion is introduced |
| Equivalence edge has one inverse and both inverse triangles | `IsEquivalenceEdge`: existential `g`, two 2-simplices `t`, `s`, six face equalities; the long edges are the degeneracies of the source and target of `f` |
| Space = Kan complex, all positive-dimensional horns including outer horns | Existing `SSet.KanComplex`, used to define the full subcategory in `spaceWeakEquivalences`; its documented horn-filling convention starts at dimension one |
| Spaces and maps up to weak homotopy equivalence | `spaceHomotopyCategory` is the existing localization construction applied to `spaceWeakEquivalences` on the full subcategory of Kan complexes |
| Products and pullbacks degree by degree | Existing cartesian monoidal `⊗` on `SSet`; `commaSubcomplex.obj` is a subset of its degreewise product, with both endpoint equations in that degree, and inherited coordinatewise operators |
| Geometric realization, discrete simplices, usual topological simplex and affine operators | Existing `SSet.toTop` in `Mathlib.AlgebraicTopology.SingularSet`; its left Kan extension uses `SimplexCategory.toTop` and is the standard quotient/coend realization, not a discrete realization |
| Path components | Existing `ZerothHomotopy`, the quotient by `Joined`; `componentsMap` is postcomposition on that quotient |
| Positive based homotopy groups via cubes relative to the whole boundary | Existing `HomotopyGroup (Fin r) X x` and `GenLoop.Homotopic.setoid`; `homotopyGroupMap` postcomposes the actual cubical maps and their relative homotopies |
| Bijective components and isomorphic positive based homotopy groups at every source point | `IsWeakHomotopyEquivalence` requires `Function.Bijective (componentsMap ...)` and, for every `r` with `1 ≤ r` and every `x` in the source realization, bijective `homotopyGroupMap`; postcomposition commutes with the first-coordinate concatenation, so bijectivity is exactly the group-isomorphism condition |
| Contractible = weakly equivalent to the one-point simplicial set | `IsContractible A` tests the canonical map `stdSimplex.isTerminalObj₀.from A` to the actual `Δ[0]` |
| Ordinary nerve of any small category | Existing `CategoryTheory.nerve` from `Mathlib.AlgebraicTopology.SimplicialSet.Nerve`, imported publicly; its simplices are `ComposableArrows` and operators are restriction |
| Internal coherent functor simplicial set | Existing `(ihom K).obj C`, whose Mathlib implementation is `K.functorHom C`; the representative has `HomObj` data equivalent to maps `K ⊗ Δ[n] ⟶ C` |
| Operators precompose on the simplex factor | The existing `Functor.functorHom` operators precompose the covariant represented test object; under `Functor.homObjEquiv` this is precisely precomposition by `id_K × Δ(α)` |
| Objects are diagrams, edges transformations, higher simplices compatibilities | `diagramVertex F` is the actual internal-hom vertex corresponding to the map `F : K ⟶ C`; all internal-hom higher data are kept |
| Full subcategory contains exactly simplices whose vertices satisfy the predicate | `fullSubcomplex C P`, quantifying every `i : Fin (n+1)` and restricting the simplex along the corresponding vertex map |
| `Fun_eq` is full on edge-inverting diagrams | `equivalenceDiagrams K C` uses `fullSubcomplex` and requires `IsEquivalenceEdge` on the image of every `e : K _⦋1⦌` |
| Constant diagram from `K → Δ[0]` | `constantDiagrams K C := MonoidalClosed.curry (snd K C)`; under adjunction this ignores the index coordinate, exactly the unique-map-induced constant diagram |
| Evaluation by vertex restriction | `evaluation K C k` precomposes the internal hom with the actual map from the terminal simplicial set representing `k`, then uses the existing unit internal-hom isomorphism |
| Homotopy fiber of `f : A → B` at `b` | `homotopyFiber f b := comma A B f b true`; an entire path simplex has initial evaluation `f(a)` and final evaluation the constant simplex at `b` |
| Right-pinched mapping-space n-simplices | `mappingSpace C x y` is a subtype of `C _⦋n+1⦌`: the last face is the entire constant initial n-face at `x`, and the final vertex is `y` |
| Mapping-space operators extend the monotone map by its new last vertex | `appendLast` is `Fin.lastCases` of the new last vertex and the original map followed by `castSucc`; `mappingSpace.map` applies this operator |
| Enhanced functor = simplicial map between given quasicategories | Existing simplicial-set morphisms `C ⟶ D` for simplicial sets bearing the existing `SSet.Quasicategory` predicate |
| Full faithfulness on the stated mapping spaces | `mappingSpaceMap` is canonical postcomposition by `f`; `IsFullyFaithful f` requires it to be a weak equivalence for every `x`, `y` |
| Coherent natural equivalence uses an equivalence edge | `AreNaturallyEquivalent F G` has an actual internal-hom edge with source `diagramVertex F`, target `diagramVertex G`, and `IsEquivalenceEdge` |
| Functor equivalence has quasi-inverse and both coherent inverse equivalences | `IsFunctorEquivalence f` existentially quantifies an actual `g` and the two `AreNaturallyEquivalent` propositions for `f ≫ g` and `g ≫ f` |
| Core contains exactly simplices whose every edge is an equivalence | `core C` quantifies every map `[1] → [n]`, including degenerate edges |
| A cone has a varying apex and coherent transformation from its constant diagram | A vertex of `coneCategory F` is a subtype of `(C ⊗ (ihom Δ[1]).obj ((ihom K).obj C)) _⦋0⦌`; its first component is its apex and its second component is the coherent transformation |
| Comma cone category's two endpoint equations hold on whole n-simplices | `commaSubcomplex ... true` requires `ev₀(b) = constantDiagrams(a)` and `ev₁(b) = const F` at every degree, not merely on vertices |
| Cone operators and compatibility homotopies | `commaSubcomplex.map` is inherited from the product, restricted by naturality of both endpoint maps; higher simplices are retained |
| Limiting cone = terminal in that cone category | `IsLimiting F t := IsTerminal (coneCategory F) t` |
| Terminal = weakly contractible mapping spaces from all objects | `IsTerminal C t := ∀ x, IsContractible (mappingSpace C x t)` |
| Space of limiting cones = core of full subcategory, varying apex | `limitingConeSpace F` is exactly `core (fullSubcomplex (coneCategory F) (IsLimiting F)).toSSet` |
| Initial = weakly contractible mapping spaces to all objects | `IsInitial C t := ∀ x, IsContractible (mappingSpace C t x)` |
| Cocones with reversed endpoints | `coconeCategory F` uses `comma ... false`, requiring `ev₀(b) = const F` and `ev₁(b) = constantDiagrams(a)` at every degree |
| Colimiting = initial in cocone category | `IsColimiting F t := IsInitial (coconeCategory F) t`; `colimitingCoconeSpace` is the dual full-subcategory core |
| `holim`, `hocolim` mean supplied universal apex, without unproved choice | `holim F t` and `hocolim F t` project the first component of a supplied cone/cocone together with its limiting/colimiting property; they choose no object from mere existence |

The cocone's product coordinates put the apex first; swapping that coordinate
with the singleton endpoint gives the node's displayed dual pullback. The actual
endpoint conditions and their operators are exactly the displayed ones. No
additional hypothesis or universal-property clause is introduced.

### Edge cases checked

- Dimension zero for spaces: the existing Kan definition has no zero-dimensional
  horn condition. An empty space is permitted. `IsContractible` still fails for
  the empty simplicial set because its empty component set cannot map bijectively
  onto the component of `Δ[0]`.
- Empty indexing simplicial set: the actual internal hom is terminal, the constant
  diagram is unique, and the cone construction retains all possible apices.
  No inhabited-index or nonempty-category premise is present.
- Mapping-space dimension zero is precisely an edge from `x` to `y`; dimension one
  requires the whole edge on the two initial vertices to be degenerate at `x`.
  For higher dimensions it requires the whole initial face, so a simplex with only
  the correct vertices but nonconstant initial face is excluded.
- `appendLast` handles constant and noninjective ordinal maps, as well as identity
  and composite maps; no injectivity or face-only restriction is imposed.
- Core and edge-inverting-diagram tests include degenerate edges, as the node says.
- Empty source in a homotopy fiber gives an empty fiber. No path or fiber element
  is chosen or assumed. The fixed endpoint is imposed on all higher simplices.
- `IsTerminal` and `IsInitial` quantify all objects of the actual comma category;
  they are not constant propositions and do not assume uniqueness or existence.
- `holim`/`hocolim` require the actual supplied universal cone/cocone; no global
  selection or unproved existence theorem determines their apex data.

### Search and reuse audit

The required searches were repeated through `msearch.py NP
 def-cbc-enhanced-diagrams-cones` (all succeeded):

1. LeanFinder: `Quasicategories with coherent functor simplicial sets right
   pinched mapping spaces and comma cone categories` returned `SSet.QCat`,
   `SSet.Quasicategory`, the ordinary nerve and horn-filling declarations.
   They supply the primitive quasicategory notion, not this node's whole package.
   The existing primitive is used directly; no duplicate bundled category is defined.
2. Loogle: `"Quasicategory"` returned the existing `SSet.Quasicategory`, its
   constructors and lifting-property interfaces, which are reused.
3. Mathlib grep: `rightMapping|pinched|coneCategory|coherent.*cone` in
   `AlgebraicTopology` returned no hits for the missing constructions.
4. LeanSearch: `Quasicategories coherent diagrams mapping spaces comma cone
   categories and limiting cones` returned ordinary `CategoryTheory.Comma`
   and ordinary cone/colimit declarations. Their categorical objects do not
   contain the node's simplicial coherence data, so these are not full matches.
5. Read-only `rg -n` in the source `WeilConjectures` and shared `lean/Sheaf` for
   `pinched|coneCategory|coherent.*cone|def-cbc-enhanced-diagrams-cones` found no
   existing declaration for this node. The shared matches concerned unrelated
   quasi-coherent module cone lemmas. An additional sandbox search found a foreign
   draft with arbitrary simplicial sets for diagrams and `True` for limiting
   cones. It is not a published dependency and is not used.
6. Direct Mathlib source searches and reads located `FunctorToTypes.rightAdj`,
   `Functor.functorHom`, `Functor.homObjEquiv`, `Functor.natTransEquiv`, `ihom`,
   `MonoidalClosed.pre`, `MonoidalClosed.unitIsoSelf`, `SSet.toTop`,
   `ZerothHomotopy`, `HomotopyGroup`, and `MorphismProperty.Localization`.
   Those exact existing notions are reused. The only new helpers implement
   remaining coordinate formulas or maps belonging to this single definition.

No `STATEMENT-DISPUTED` issue, statement correction, or dependency fault was found.
The initial retry message's claim of an already installed record was checked:
the assigned sandbox contained only dispatcher marker files; the shared/server
node had no `lean` record, and the source service reported this module unavailable.
This delivery therefore supplies the missing construction rather than re-recording
an unchanged published declaration.

### Validation

The sole delivered module compiled cleanly through the prescribed `scompile.py`
wrapper with its local overlay, in both sandbox and library-module checks (about
2.6 and 3.7 seconds). No warnings, `sorry`s, or auto-bound variables remain.
The local textual stage-2 check also reports no findings. The required `deliver2.py NP def-cbc-enhanced-diagrams-cones --no-push`
dry run printed `OK (dry run)` for commit `04ad4d3388`: compilation and server
preflight passed, with only the independent second reading left for the second
reader. Nothing was pushed.

## Second reading by NP

I reread the current node JSON, its Stacks/Scholze source references, the two dependency
records, and `Sheaf/CategoryTheory/EnhancedDiagramsCones.lean` independently of the worker
report. The node is a single definition package; the following list records each object or
clause and the declaration that renders it.

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Fixed size convention and simplicial sets | Explicit `universe u v`; Mathlib `SSet.{u}` and its existing operators. Exact. |
| Standard simplex and monotone operators | Existing `SSet.stdSimplex`/`stdSimplex.objEquiv`; no duplicate definition. Exact. |
| Horns and inner-horn enhanced categories | Existing `SSet.horn` and `SSet.Quasicategory`. Exact. |
| Equivalence edge and two inverse triangles | `IsEquivalenceEdge`, with one inverse edge and two 2-simplices and the six face equations. Exact orientation. |
| Kan spaces, including outer horns and no nonemptiness | Existing `SSet.KanComplex`, used by `spaceWeakEquivalences`; no extra inhabitedness. Exact. |
| Weak equivalence and components | `componentsMap`, `homotopyGroupMap`, and `IsWeakHomotopyEquivalence` use `SSet.toTop`, `ZerothHomotopy`, and positive `HomotopyGroup` maps. Exact; bijectivity is the induced group-isomorphism condition. |
| Geometric realization and affine operators | Existing `SSet.toTop`; it is the standard quotient/coend realization with discrete simplices and the stated affine maps. Exact. |
| Contractibility and spaces up to weak equivalence | `IsContractible`, `spaceWeakEquivalences`, and `spaceHomotopyCategory`; target is the actual `Delta[0]`. Exact. |
| Ordinary nerve | Existing `CategoryTheory.nerve`; no duplicate. Exact. |
| Internal coherent functor simplicial set | Existing `(ihom K).obj C`; `diagramVertex` identifies maps `K ⟶ C` with its vertices. Exact. |
| Internal-hom operators and coherent diagrams | Existing internal-hom operators, with `equivalenceDiagrams` and `fullSubcomplex` retaining all higher compatibilities. Exact. |
| Constant diagrams and vertex evaluation | `constantDiagrams` and `evaluation` via the monoidal closed adjunction. Exact. |
| Homotopy fiber | `homotopyFiber := comma A B f b true`; endpoint path data are retained in every degree. Exact (the construction is generalized to arbitrary simplicial sets and specializes to the stated Kan case). |
| Right-pinched mapping spaces | `appendLast` and `mappingSpace`; the whole initial face is constant and the final vertex is fixed. Exact, including dimension zero. |
| Mapping-space maps and full faithfulness | `mappingSpaceMap` and `IsFullyFaithful`; postcomposition is canonical and tested by weak equivalence. Exact. |
| Coherent natural equivalence | `AreNaturallyEquivalent` uses an internal-hom edge with the stated endpoints and `IsEquivalenceEdge`. Exact. |
| Functor equivalence | `IsFunctorEquivalence` supplies a quasi-inverse and coherent equivalences of both composites with identities. Exact. |
| Core | `core` requires every edge map, including degenerate edges, to satisfy `IsEquivalenceEdge`. Exact. |
| Cone comma category | `commaSubcomplex`, `comma`, and `coneCategory`; both endpoint equations hold on whole simplices, with the apex first and coherent transformation second. Exact. |
| Cocone comma category | `coconeCategory` reverses the two endpoint equations as in the node. Exact. |
| Terminal and initial objects | `IsTerminal` and `IsInitial` quantify all objects through the right-pinched mapping spaces. Exact. |
| Limiting and colimiting cones | `IsLimiting` and `IsColimiting` are terminal/initial predicates on the corresponding comma simplicial sets. Exact. |
| Spaces of limiting/colimiting cones | `limitingConeSpace` and `colimitingCoconeSpace` take the core of the full subcomplex, allowing the apex to vary. Exact. |
| `holim` and `hocolim` | The declarations project the apex from an explicitly supplied universal cone/cocone, with no choice from mere existence. Exact. |

Edge cases checked: the empty indexing simplicial set gives the unique constant diagram and
allows arbitrary apices; the empty simplicial set is allowed as a Kan space and is not made
contractible; `n = 0` mapping simplices are exactly edges with the prescribed initial vertex;
noninjective, constant, identity, and composite ordinal maps are handled by `appendLast`;
full-subcomplex and core tests include degenerate edges; empty homotopy fibers remain empty;
terminal/initial predicates quantify over the actual comma object; and no characteristic,
Noetherian, finiteness, nonemptiness, or universe equality assumption was added.

Searches repeated for this reading: `msearch.py NP def-cbc-enhanced-diagrams-cones` with
LeanFinder, Loogle, and grep; `rg` over Mathlib AlgebraicTopology, the read-only
`WeilConjectures` source, and shared `lean/Sheaf`; and direct reads of the declarations
`SSet.stdSimplex`, `SSet.horn`, `SSet.Quasicategory`, `SSet.KanComplex`,
`CategoryTheory.nerve`, `(ihom K).obj C`, `SSet.toTop`, `ZerothHomotopy`, and
`HomotopyGroup`. These found only the reused primitives, not an existing package matching
this node. The dependency records were also checked: `def-weil-pbc-simplicial-set` is an
exact Mathlib match and `def-weil-size-convention` is the recorded universe convention.

No semantic mismatch was found. I corrected one misleading helper docstring: the edge
restriction in `equivalenceDiagrams` uses the unique degree-one to degree-zero map, not an
identity map. The definition and node record are unchanged. There are no new nodes,
no dependency modules, no statement correction, and no `STATEMENT-DISPUTED` issue.


The independent searches used a different semantic query, "Simplicial full subcategory of
 equivalences and terminal objects defined by contractible incoming mapping spaces"
(LeanFinder: eight primitive/enrichment hits, no match), `"HomotopyGroup"` (Loogle:
twelve homotopy-group hits, reused), and
`fullSubcomplex|rightMapping|commaSubcomplex|IsWeakHomotopyEquivalence` (Mathlib grep:
zero hits). Direct `rg` of the project and Mathlib AlgebraicTopology likewise found no
implementation of the new constructions. Read Scholze's archived PDF, printed pp.13--15,
and [Kerodon the project server--2](https://kerodon.net/tag/01KW), whose whole-initial-face and
last-vertex formulas agree with `mappingSpace`. This source has no additional ring,
scheme, or finiteness hypotheses. The general simplicial-set formulas do not assert the
quasicategory/Kan closure theorems, which belong to the downstream calculus node.

H5/H6/H8/H9 checks: every data definition is explicit; the `by` fields prove only required
structure laws and subtype closure, not extra theorem declarations. There are no `sorry`s,
axioms, private copies, local notation or instances, or unbound universes/variables.
All declarations have source/blueprint docstrings. The node's empty proof needs no postponed
proof docstring. Its `lean.statement` reproduces the `def coneCategory` signature exactly.
The sole module passed both sandbox and library compilation via `scompile.py`, without
errors or warnings.
