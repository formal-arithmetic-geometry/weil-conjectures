## Worker report

The module is `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`, with namespace
`CategoryTheory.Dg`. Its main theorem is `freeCellCalculus : FreeCellCalculus R`.
The proposition `FreeCellCalculus` has nine fields, collectively stating the entire
node; the main theorem is not merely the completeness or smallness clause.
The item copy changes only `lean`. There are no statement corrections, additional
nodes, dependency repairs, or disputed statements.

The source read was Tabuada, *Théorie homotopique des DG-catégories*,
arXiv:0710.4303, Definition 1.1 on printed p. 25, the scalar and two-object
categories on p. 27, and §1.3.1, the smallness paragraph and Lemma 1.10 on
pp. 28–30. The disk-adjoining calculation is a direct sum of complexes;
the contraction-adjoining calculation on pp. 29–30 is only a direct sum of
graded modules, with a differential lowering length. The finite-limit-sketch,
finite-presentation and arbitrary-degree generalizations are those explicitly
written in this node's twelve proof steps, rather than claims that these
extra assertions appear verbatim in Tabuada. The final theorem's docstring
contains all twelve steps; each field also explains its own proof route.

Definitions have actual data. The module does not select a category, comparison,
or normal form from a theorem proved by `sorry`. The free constructions are
existential conclusions with explicit generators, universal properties and
canonical word comparisons. The only postponed proofs are `fun_unit_laws`,
`fun_assoc`, `mul_d`, and the main `freeCellCalculus`. The first two give the
proof fields of the ordinary category structure; its objects, Hom types,
identities and composition are explicitly fixed independently of these proofs.
All four belong to this DAG node and are listed in `lean.declarations`.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Small universe and arbitrary commutative ring R | `universe u`; `(R : Type u) [CommRing R]`. No field, nontriviality, flatness or characteristic assumption. |
| Small objects and small morphism modules | `Cat R` specializes Mathlib `EnrichedCat.{u,u+1,u}` to `CochainComplex (ModuleCat.{u} R) ℤ`. Both objects and every homogeneous module have universe u. |
| Cochain differential of degree 1 and square zero | Mathlib `CochainComplex` with shape `ComplexShape.up ℤ`. |
| Associative unital R-linear composition | The existing `EnrichedCategory` structure. Its chain-map compositions are bilinear and its unit/associativity laws are part of the structure. |
| Right-to-left Leibniz convention | `comp` reverses Mathlib's tensor order with the Koszul braiding; `mul` evaluates on homogeneous tensors. `mul_d` explicitly states `d(ba)=d(b)a+(-1)^p b d(a)` for p the degree of b, transporting only equal integer degrees. |
| Dg functors preserve all the data | `Fun R C D` is the existing `EnrichedFunctor`; `catCategory` supplies the ordinary strict category with these functors as morphisms. It is not the category of natural transformations or a localization. |
| Small Hom sets | `FreeCellCalculus.category_properties`, first conjunct, `LocallySmall.{u}`. |
| All small limits and colimits | The second and third conjuncts, `HasLimitsOfSize.{u,u}` and `HasColimitsOfSize.{u,u}`. |
| Small finitely presentable filtered generating family | Fourth conjunct, Mathlib `IsLocallyFinitelyPresentable.{u}`. Its definition is small filtered generation by finitely presentable objects plus small cocompleteness. |
| Filtered means finite diagrams admit cocones | Mathlib `IsFiltered` on the small index category, including nonemptiness. |
| Finitely presentable means Hom preserves filtered colimits | Mathlib `IsFinitelyPresentable.{u}` (`Presentable.Finite`), not termwise finite generation. |
| Finite dg presentations | `Term` is finite homogeneous syntax with generators, identities, zero, addition, scalar multiplication, composition and degree casts. `FinitePresentation` specifies finitely many objects, homogeneous arrows, their differential words, and finitely many homogeneous relations, together with their realization and the universal property for assignments satisfying those equations. Relations written as equalities are encoded by their difference. The object equivalence labels exactly the finite object set. |
| Finite presentations are finitely presentable | `FreeCellCalculus.finitePresentation_presentable`, for every displayed presentation. |
| Filtered-colimit object set | `filteredColimit_description` says `objects.mapCocone c` is colimiting for every colimit cocone c. |
| Fixed-endpoint filtered-colimit complex over i/I | The same field gives a diagram `D : Under i ⥤ CochainComplex ...`, its exact object formula, exact transition maps, and a colimiting cocone with the exact Hom complex as vertex and canonical structure maps. `Under i` is the category i/I, so this also covers non-posetal index categories and parallel arrows. |
| One-object scalar category | `exists_scalarCategory` gives an object labeling by the singleton and an invertible scalar unit map. Thus the endomorphism complex is R in degree zero, with its multiplication and unit forced by the dg unit laws. |
| T(V) has two objects, scalar endomorphisms, reverse Hom zero and forward Hom V | `exists_twoObjectCategory` labels objects by `ULift (Fin 2)`, makes both scalar unit maps and the displayed map from V invertible, and states `IsZero` for the reverse Hom complex. |
| Functors T(V) to C classify pairs and chain maps | `Function.Bijective` for the actual restriction map `F ↦ (F(0),F(1),v ≫ F.map 0 1)`. It includes equal object images. Restriction is canonical and therefore natural under postcomposition; under a map of V the corresponding functor is uniquely specified by this bijection. |
| Finitely presented V implies finitely presentable T(V) | The last implication of `exists_twoObjectCategory`, using categorical finite presentability of the whole complex V. |
| Attach a degree-n arrow with prescribed closed differential a | `exists_arrowCell` quantifies every C,s,t,n,a and the closedness equation `d a = 0`. `ArrowCell.arrow` is a graded map from rank one in degree n; `generator` extracts its element e and `differential` states `d e = inclusion(a)`. There is no change in degree conventions. |
| Free adjoining, no further relations and unchanged objects | `ArrowCell.universal` is unique extension for every old dg functor and every graded image of e satisfying its differential equation. `objects_bijective` identifies the target object set with the old set through the inclusion: it permits neither omitted nor new objects. This is the labeled formulation of identity on the old object set. |
| Actual word normal form | `wordEval` recursively evaluates every tensor factor by the old functor and new generator. `HasWordFiltration` first requires its canonical degreewise coproduct map to be an isomorphism. No arbitrary comparison is substituted. |
| Increasing exhaustive filtration by occurrences of e | `wordRange` is the supremum of the images of word evaluations for lengths at most m. The complexes F(m), injective maps j(m), transition maps i(m), compatibility, and exact range equations in `HasWordFiltration` realize these partial sums as actual subcomplexes. Its explicit exhaustivity clause represents every element at a finite stage. |
| F0 is C(x,y) | The isomorphism `q : hom R C x y ≅ F 0` satisfies `q.hom ≫ j 0 = inclusion.map x y`. |
| Filtration inclusions split as graded modules | For every m and integer k the successor inclusion has a retraction in `ModuleCat R` in degree k. Composites give retractions for all m ≤ m'. No chain-map retraction is asserted. |
| Quotient is the displayed tensor complex | `word C (single R n) s t x y (m+1)` expands to `C(t,y) ⊗ Re ⊗ (C(t,s) ⊗ Re)^m ⊗ C(x,s)`. `single R n` has zero differential. The quotient is `cokernel (i m)` in cochain complexes. Its isomorphism is characterized by lifting the actual length-(m+1) word evaluation to F(m+1) and then applying the quotient projection. |
| Leibniz differential and lowering terms | Composition is a chain map and satisfies `mul_d`; `differential` fixes d(e)=a. Therefore the derivation on each word differentiates old factors without changing length and replaces e by a with one fewer occurrence. The subcomplex and canonical quotient clauses retain this differential, including its tensor signs. |
| Adjoining a whole complex V | `ComplexCell` has the same free extension property for every chain map from V, with bijective old-object inclusion and a displayed chain map of new arrows. |
| Direct sum including length zero, with tensor differential on each summand | `ComplexCell.HasWordSum` states that `Sigma.desc (wordChainEval ...)` is invertible as a map of complexes. Its source is the coproduct of all length-m word complexes, including m=0. The recurrence uses the actual cochain tensor product, so the differential is the tensor differential with total degree the sum of factor degrees. |
| Naturality in the attaching data | `arrowCell_natural` and `complexCell_natural` give unique extensions of an old functor (and, in the latter case, a chain map V→W), fixing the new generators. They also state the tensorwise word-evaluation squares for every length. Thus partial word ranges, filtration quotients, the direct-sum comparisons and their inverses commute with these extensions. Uniqueness gives the identity and composition laws. |

Heterogeneous equalities occur only where functoriality or a cocone identifies
object images. They specify equality after the canonical transport, rather
than permitting different endpoints or an unspecified arrow. In particular the
filtered diagram maps and all word comparison squares are fixed.

Dependency declarations read and used:

- `def-weil-size-convention`: its `lean` record is explicitly metatheoretic
  (`convention: true`, no declaration). Its prescription is rendered by the
  explicit small level u, the category at u+1, and size-u limits and colimits.
- `def-weil-pbc-module-tensor-product` is a Mathlib leaf, with no missing Lean
  record: `TensorProduct` in `Mathlib.LinearAlgebra.TensorProduct.Defs`;
  `TensorProduct.mk`, `TensorProduct.lift`, `lift.tmul`, `ext'` in `Basic`;
  `LinearMap.rTensor`, `rTensor_tmul`, `rTensorHom` in `Map`. I read the recorded
  signatures and docstrings. The module uses this tensor product via
  `ModuleCat` and the cochain tensor construction, and directly uses `tmul`.
- Proof dependency `lem-weil-pbc-filtered-colimit-sets-elementwise` is the
  Mathlib leaf for `Limits.Types.jointly_surjective` and
  `Types.FilteredColimit.isColimit_eq_iff`, `isColimit_eq_iff'`; its module is
  already publicly imported by `Presentable.Finite`. The theorem docstring
  names its representative and equality clauses where used.
- Proof-only `lem-coef-finite-limit-sketch-models` has no recorded declaration
  yet. It is named in the proof documentation. It is not a statement dependency
  and no statement of that separate DAG node is added here.

Searches actually run for this item:

1. `msearch.py ... leanfinder` query
   `Small differential graded categories free adjoining arrows word length filtration locally finitely presentable`:
   eight hits, including `HomologicalComplex.instHasFilteredColimitsOfSize`
   and `HomologicalComplex.locallySmall`, but no dg-category theorem or free-cell calculus.
2. `msearch.py ... loogle` query `EnrichedCat, CochainComplex`:
   zero hits; the service reported unknown identifier `EnrichedCat`.
   This is a search-service limitation, not absence of the declaration:
   I opened Mathlib `Enriched/EnrichedCat.lean` and `Enriched/Basic.lean`
   directly and used their actual bundled category and enriched functor definitions.
3. `msearch.py ... grep` query `DGCategory|dgcat|free.*dg.?categor`:
   zero Mathlib hits.
4. `msearch.py ... leansearch` query
   `The category of small differential graded categories has filtered colimits and free dg categories obtained by adjoining arrows`:
   eight hits about filtered colimits of complexes, modules, monoids and groups;
   no match for the dg-category theorem.
5. Direct `rg` on Mathlib, the read-only WeilConjectures sources, and side
   `lean/Sheaf`, for `DgCategory|DGCategory|dgCategory|dgcat|graded.*category|Cochain.*Category`
   and `dg[Cc]at|DGCategory|free.*dg.?categor`; search by the full node id in
   WeilConjectures and in `dag/lean_names_upstream.json`: no existing whole theorem.
6. A repeated side search found the newly published integer-only
   `IntegralDGCategory` in `SemiFreeDGModule` and the recorded
   `DGModuleCategory` in `DGModuleSemiFreeReplacement`. I read the former
   locally and the latter through `scompile.py --source`. Both are confined to
   integer complexes; neither defines small dg categories over arbitrary R or
   states this calculus. This delivery specializes Mathlib's existing
   `EnrichedCat` and `EnrichedFunctor`, with the Koszul interchange converting
   their forward tensor convention to the node's right-to-left convention.
7. DAG text search found the free-cell node and its consumers, not a separate
   existing definition node for its internal finite presentations or word cells.
   `tools/blueprint_refs.py search 'dg category'` returned zero blueprint nodes.
   The definitions here spell out notions introduced by this very node; no
   independent missing notion is manufactured or restated as another theorem.

Edge cases checked before and during writing:

- R may be the zero ring or have characteristic 2; no nontriviality is required.
  The sign is integer scalar multiplication and correctly specializes in every characteristic.
- The empty dg category is among `Cat R`; no global nonempty-object hypothesis is imposed.
  A cell at specified s,t naturally requires these particular objects to exist.
- The finite presentation may have zero objects, arrows or relations. The syntax
  includes identities and zero; all quantifiers over empty generator families
  have their expected vacuous meanings.
- T(0) still has exactly two labeled objects. A functor may send them to one
  object; no distinctness hypothesis is imposed. An unbounded termwise-finite
  complex is not silently assumed finitely presentable.
- n is any integer, including 0 and negative values. The boundary has degree n+1.
  Word length zero is exactly the old Hom, and the first quotient uses length one.
- s=t is allowed; the recurrence then gives the repeated endomorphism factors
  without discarding words or imposing a non-loop condition.
- A filtered index is nonempty and may have parallel morphisms. The fixed-endpoint
  diagram is the full category i/I, not a cofinal tail of a poset.
- The single-cell differential may be nonzero. Only its image a is required
  closed; the filtration splitting is degreewise, and the quotient has the
  zero-differential rank-one factor. For a whole complex V the actual d_V is kept.
- Every tensor is over the original R. There is no flatness assumption, no
  derived tensor product, no localization of dg functors, and no universe equality
  added to match an overly specialized interface.

Validation: every compile uses the prescribed `scompile.py` wrapper, with the
normal file-only 60-second limit. Initial import, finite-syntax universe and
singleton universe errors were repaired. The final sandbox and library-form compiles both passed with no errors or warnings
(20.3 s and 19.8 s). The required delivery dry run follows.


## Second reading by NX

I read the corrected node statement in `dag/nodes/sec-six-functors/lem-coef-dgcat-free-cell-calculus.json`, its twelve proof steps, the dependency records, and Tabuada, *Théorie homotopique des DG-catégories*, §1.3.1, Lemma 1.10 (arXiv:0710.4303, printed pp. 28--30). The source gives the direct-sum word decomposition for the disk attachment and the differential-lowering word filtration; the node explicitly records the stated arbitrary-degree, arbitrary-closed-boundary and whole-complex generalizations.

Step-by-step statement check:

1. The small universe and arbitrary commutative ring are `universe u`, `(R : Type u) [CommRing R]`; `Cat R` is `EnrichedCat` on cochain complexes of `ModuleCat R`, with object and homogeneous-module universes as required. No field, nonzero, flatness, characteristic, or universe-equality hypothesis is added.
2. `FreeCellCalculus.category_properties` gives `LocallySmall`, `HasLimitsOfSize`, `HasColimitsOfSize`, and `IsLocallyFinitelyPresentable` for the strict dg-category category. `Fun` and `catCategory` are the ordinary dg-functor category, with the signed right-to-left Leibniz rule supplied by `mul_d`.
3. `filteredColimit_description` quantifies a small filtered `I`, uses the full `Under i` category (including parallel arrows), gives the object-set colimit and the exact fixed-endpoint cochain-complex diagram and colimit cocone. The `HEq` clauses only transport the stated endpoint equalities.
4. `FinitePresentation` has finite object, homogeneous-arrow, differential-word, and relation data, realizes the finite object labels by an equivalence, and has the required universal property. `finitePresentation_presentable` states finite presentability for every such presentation.
5. `exists_scalarCategory` supplies the one-object scalar dg category up to the displayed unit-complex isomorphism. `exists_twoObjectCategory` supplies the two labeled objects, scalar endomorphism unit isomorphisms, zero reverse Hom, the forward `V` map isomorphism, the functor classification bijection (allowing coincident images), and finite presentability when `V` is finitely presentable.
6. `ArrowCell` and `exists_arrowCell` quantify arbitrary objects, every integer degree, and every closed boundary, preserve the old object set bijectively, and state the strict extension universal property. `word` and `ArrowCell.HasWordFiltration` give length zero, the displayed tensor quotient, exhaustivity, subcomplex inclusions, degreewise graded splittings, and the lowering Leibniz differential.
7. `ComplexCell`, `exists_complexCell`, and `HasWordSum` give adjoining an entire cochain complex, including its own differential, as the direct sum of all word lengths with the tensor differential.
8. `arrowCell_natural` and `complexCell_natural` state unique extension maps and tensorwise word-evaluation naturality in the old functor and attaching data; these are the canonical comparison clauses used by the node.

Edge cases checked: the zero ring and characteristic two; empty dg categories; zero and empty finite presentations; `V = 0`; coincident two-object images; every integer degree including `0` and negative degrees; `s=t`; nonempty filtered categories with parallel arrows; and nonzero closed boundaries. No edge case is excluded by a hidden nonemptiness, finiteness, or characteristic assumption. The index universe is `Type u`, matching the dg-category universe.

Searches: the recorded LeanFinder, Loogle, LeanSearch, and grep searches in `searches.jsonl` were rerun/inspected. Direct `rg` searches of Mathlib, the read-only `WeilConjectures` source, and the side `lean/Sheaf` found no existing free dg-category calculus, `ArrowCell`, `ComplexCell`, or `FreeCellCalculus`; Mathlib's `EnrichedCat` and `EnrichedFunctor` are the declarations actually used. The dependency declarations for the size convention and module tensor product were read.

No statement mismatch was found, so no Lean or node repair was needed. The sandbox module compiled with `scompile.py` both in its sandbox overlay and as a library-form compile, with no errors or warnings. The node copy remains verbatim except for its existing `lean` record.

