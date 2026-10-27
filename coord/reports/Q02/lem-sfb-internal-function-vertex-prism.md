## Worker report

The delivery states `CategoryTheory.CondensedBar.internal_function_vertex_prism` in
`Sheaf.CategoryTheory.InternalFunctionVertexPrism`. Its only postponed proof is this
named theorem, whose docstring contains all seven steps of the accepted DAG proof.
The accompanying structure packages the prescribed complexes, pullbacks and prisms;
it is not an additional hypothesis. The theorem supplies this structure for every
commutative condensed ring. No object is selected from the existence theorem.

The node copy changes only `lean`. In particular the accepted Q84 stage-1 split,
statement, dependencies and source are preserved. The inherited unchanged-item
failure was from attempting a stage-1 delivery; this is its stage-2 statement.
No repair note exists for this item. No new nodes or dependency modules are needed.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Any commutative condensed ring on the small coherent profinite site | `A : CondensedBar.Ring.{u}` is the existing `CommMon (Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u+1})`. Its underlying `A.toMon` is the recorded `Profinite.CondensedRing`. There is no topological presentation or extra ring hypothesis. |
| Any internal A-module M | The structure quantifies over every `M : Modules A`; this is the dependency's actual `CategoryTheory.Mod` specialization, not a replacement module category. |
| Profinite Z, including empty | `Z : Profinite.{u}` is unrestricted, with no `Nonempty` instance. The same holds for all X,Y,W,Z,S,T. |
| B_Z^n(M)=internal Hom from A[Z^(n+1)], n≥0 | `term Z n` identifies the degree-n functor with `F.functor (power Z (n+1))`. The existing `InternalFunctions.internalHom` identifies this with `Mod.ihom (freeParameter A (power Z (n+1)))`. The theorem supplies F together with the structure. |
| B_Z^n=0 for n<0 | `InternalFunctionVertexPrism.integerComplex` is the actual Mathlib `extend ComplexShape.embeddingUpNat` of the nonnegative complex. This construction has zero objects in negative degrees. |
| Displayed alternating deletion differential | `differential` is the displayed signed sum over `j : Fin (n+2)`; `j.succAbove` deletes exactly coordinate j. `complex` is a genuine `CochainComplex`, hence already carries d²=0. |
| Continuous u,v and their internal linear cochain pullbacks | `pullback` takes every `C(X,Y)` to a natural transformation `complex Y ⟶ complex X`; each component is a genuine cochain map in `Modules A`. `pullback_formula` fixes its evaluation to coordinatewise composition. |
| P_(u,v,0)=0 | `InternalFunctionVertexPrism.prismZero` is defined as the actual zero morphism into degree -1 of `integerComplex`. |
| Prescribed prism for n≥1 | `prism u v n M` is P_(u,v,n+1), with source degree n+1 and target degree n. `prism_formula` sums over `i : Fin (n+1)` with sign `(-1 : ℤ)^i.val`. `vertexPrismTuple` has u on j≤i and v on j>i; `i.predAbove` keeps j≤i and replaces j>i by j-1, duplicating coordinate i exactly once. |
| Internal A-linearity | Differential, pullback and prism components are morphisms in the actual internal module category; linearity is part of that morphism type. |
| δP+Pδ=v*-u* in every nonnegative degree | `identity_zero` gives d_Y^0 followed by P_1 = v* - u* in degree 0. `identity_succ` gives P_(n+1) followed by d_X^n plus d_Y^(n+1) followed by P_(n+2) = v* - u* in degree n+1. Composition `≫` reads in the categorical order. |
| Formulas on generalized evaluations after every profinite base change | `vertexPrismValue` calls the dependency's `F.evaluate` on arbitrary `S,T,f:T⟶S` and tuples of continuous maps T→Z. Every formula quantifies over all these variables. `InternalFunctions.restriction`, `FunctionFamily.IsNatural`, and naturality of the internal module maps ensure all base changes, not merely ordinary point evaluations. |
| Commutes with every coefficient map M→N | `complex Z` is a functor, `term Z n` a natural isomorphism, and `pullback u` a natural transformation. Therefore differential and pullback commute with every coefficient map. `coefficient_naturality` explicitly states `map(a) ≫ P_N = P_M ≫ map(a)` for the prism. The dependency's `InternalFunctions.map` fixes these coefficient maps on generalized values to the given a, excluding arbitrary actions on maps. |
| b*P_(u,v)=P_(u∘b,v∘b) | `source_naturality`, for every `b : C(W,X)`, every M and every n. |
| P_(u,v)c*=P_(c∘u,c∘v) | `target_naturality`, for every `c : C(Y,Z)`, every M and every n. Its composition starts with c* in degree n+1, then P_(u,v,n+1). |
| Explicit degree-zero evaluated identity | `degree_zero_formula`, on every S,T,f and length-one tuple g, states P_1δF(g)=F(vg)-F(ug). |
| No group action or resolution required | The sole theorem input is A. There is no group, injective resolution, projectivity, acyclicity or function-model hypothesis. F and the prescribed structures are in the conclusion. |

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`, `Profinite.CondensedRing`: the actual
  ring-object encoding, specialized here to its bundled commutative objects.
- `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`, `ModObj`, `Mod.Hom`:
  the recorded module objects and their linear maps. The imported bar-data module
  specializes these as `CondensedBar.Modules`.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `CondensedBar.Ring`, `Modules`,
  `sections`, `power`, `tupleMap`, `freeParameter`, `FunctionFamily.IsNatural`,
  `InternalFunctions` with `internalHom`, `evaluate`, `map`, `restriction`, `add`,
  `smul` and `additive`. Their full signatures and docstrings were read.
- `def-weil-size-convention` is a metatheoretic convention without a declaration;
  its sizes are explicit here: `Profinite.{u}` and coefficient abelian groups in u+1.
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`,
  `HomologicalComplex.extend` and `ComplexShape.embeddingUpNat`: actual extension
  by zero, not an independently chosen negative part.

The proof dependency `lem-sfb-profinite-free-hom-resolution-evaluation` currently
has no `lean` record. Its statement was read and its use remains in the theorem's
proof docstring. No import can be added for an unstated proof dependency, and it
is not needed to type the statement. The other proof dependency is the imported
bar-data definition. The source place in simplicial.tex (the signed homotopy formula,
the four sums, endpoint cancellation and lemma-homotopy-s-N) and the current latest
blueprint direct-images proof, paragraph (3), were read.

Edge cases checked before drafting and again against the final fields:

- Degree zero: the sole prism summand has coefficient +1 and tuple `(u x,v x)`.
  Deletion evaluates δF(u x,v x)=F(v x)-F(u x), fixing the orientation of the
  entire equation. P_0 is the zero map to the extended negative degree.
- Positive degree: P_(n+1) uses n+1 summands and a tuple of length n+2; its source
  and target degrees match the node. The equation in degree n+1 has the two
  compositions with exactly these domains and codomains.
- X empty: positive tuple powers are empty, and sections on the empty object
  vanish by the empty coherent cover; no vertex is chosen. If Y is empty, the
  quantified maps X→Y force X empty. Empty S and T are also allowed.
- u=v: the endpoint difference is zero; the statement still prescribes the same
  possibly nonzero signed prism, rather than incorrectly forcing P itself zero.
- Zero ring and zero coefficient module are not excluded. Signed sums are over ℤ
  and work in every characteristic, including 2. No division is used.
- Source/target naturality has been checked with the displayed types: b* is applied
  after P, whereas c* is applied before P. Negative and degree-zero prism naturality
  is automatic for the prescribed zero map, so the fields cover all positive terms.

Searches actually run (the msearch output is saved by the wrapper in searches.jsonl):

- LeanFinder: `Alternating vertex prism cochain homotopy between pullbacks on internal
  functions from tuples of profinite sets`. Eight hits include Homotopy constructors,
  Dold--Kan homotopies, alternatingConstHomotopyEquiv, and alternatingCofaceMapComplex.
  None states the specified internal-function prism or its generalized evaluation.
- Loogle: `"Homotopy", "alternating"`. Six hits are the alternating-constant and
  normalized-Moore/alternating-face equivalences, not this profinite-parameter result.
- Mathlib grep via msearch: `prism|vertexPrism` in `AlgebraicTopology`. Zero hits.
- LeanSearch: `Internal condensed module function cochains alternating deletion vertex
  prism homotopy`. Eight hits give abstract cochain homotopy constructors and ordinary
  group cohomology, not internal condensed modules with both parameter naturalities.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `lem-sfb-internal-function-vertex-prism|vertexPrism|vertex.prism`: the existing
  `InternalBarFiniteIndexTransfer` mentions the item in its proof docstring; it does
  not state it. Broader `prism|homogeneous` searches read the nearby homogeneous
  function and resolution interfaces, which require group actions and do not give
  arbitrary profinite parameter maps. The final declaration names were searched in
  Mathlib, WeilConjectures and Sheaf; no existing declarations have these names.

No statement correction or disputed statement is needed. All definitions contain
real data, and all automatically implicit variables are forbidden by
`set_option autoImplicit false` with explicit universe u.

## Second reading by Q02

The dispatcher brief forbids starting another agent and assigns independent delivery
review to the maintainer. This section records the dispatched worker's separate
second pass, not a claim of another reviewer's work.

I reread the source, node and complete module. The table above matches each hypothesis
and clause. In particular the prism index is deliberately shifted: `prism ... n` is
P_(n+1), so its Fin (n+1) sum and Fin (n+2) evaluated tuple agree; `identity_zero`
and `identity_succ` partition all nonnegative degrees. `Fin.predAbove` was read in
Mathlib/Data/Fin/SuccPred.lean: its cutoff is `castSucc i`, so the two entries at i
and i+1 use the same x_i with u and v, respectively. Both naturality directions
match the contravariant compositions in the node. The term isomorphisms are natural
in coefficients, and the explicit prism coefficient equation includes every map.
The two negative-degree helpers use only genuine extension-by-zero and zero maps.

The first draft used prism natural transformations into complex-evaluation functors.
Lean's addition elaboration did not identify their partially unfolded endpoints.
The repaired final version writes the same prism maps with explicit endpoints and
states their coefficient naturality equation. No mathematical clause changed.

Validation: `scompile.py Q02 lem-sfb-internal-function-vertex-prism` compiled both the
sandbox module and its library name cleanly (14.1 s and 14.6 s), with no errors or
warnings. The unused parameter names in the prism field were changed to `_u _v`;
these are still explicit continuous-map binders and all formula fields use the
corresponding arguments. The module has no line longer than 100 characters.
