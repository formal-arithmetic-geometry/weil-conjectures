## Worker report

The delivery states `SSet.Enhanced.infinity_pointwise_adjoint_criterion` in
`Sheaf.CategoryTheory.InfinityPointwiseAdjointCriterion`. Its only postponed theorem
is the item itself, with the four-step natural-language proof in its docstring.
All six helper definitions have real bodies. Nothing is proved in this delivery.
The source was read online: HTT Proposition the project server and Lemma the project server,
Definition the project server and Proposition the project server, and Kerodon 02FV and 02F1.
HTT the project server states the criterion using representable right fibrations, and its
preceding lemma explains the mapping-presheaf interpretation. The delivery uses
that equivalent model directly, avoiding a choice of straightening or of composition
on right-pinched mapping spaces.

Hypotheses and clauses, individually:

* The categories C, D, E are `SSet.{max (u + 1) v}` with separate explicit
  `Quasicategory` instances. The small universe is u; the ambient universe is
  `max (u + 1) v`. This retains arbitrarily large ambient categories and does not
  force the ambient and small universes equal or consecutive. All universes and
  variables are bound explicitly, and `autoImplicit` is false.
* Small mapping spaces are `_hC`, `_hD`, `_hE`, each using
  `HasSmallMappingSpaces.{u, v}`. For every pair of vertices this requires an
  actual u-small Kan model K and a weak equivalence from its canonical universe
  lift to the right-pinched `mappingSpace`. It does not require the chosen large
  mapping simplicial set to be degreewise small. The targeted `checkUnivs` linter
  setting on this definition is needed because the small universe occurs in its
  body rather than independently in the type of this Prop-valued definition.
* The dependency `def-coef-complete-algebroid` is cited by the item solely for
  the metatheoretic convention U in U'. No algebroid object or construction occurs
  in this statement. Its whole statement was read; it has no Lean record, and
  none is needed to declare the two explicit Lean universes. The enhanced-category
  dependency's full signatures and docstrings were read and used directly.
* The functor F is the simplicial map `(F : C ⟶ D)`, with no added hypotheses.
  The functor i is independently `(i : E ⟶ C)`.
* Having a right adjoint is `∃ R : D ⟶ C, Nonempty (CoherentAdjunction F R) ...`.
  This is actual coherent functor data, not an ordinary homotopy-category adjoint.
* For each d, right representability is
  `∀ d : D _⦋0⦌, ∃ r : C _⦋0⦌, MappingPresheafRepresentedBy F d r true`.
  The total right fibration of the presheaf is the already constructed
  `comma C D F d true`, with source projection `mappingCommaProjection`.
  Its fiber at c is the fixed-endpoint arrow model of Map_D(Fc,d).
  `comma C C (𝟙 C) r true` similarly models Map_C(c,r).
  `MappingPresheafRepresentedBy` requires a simplicial map between these total
  spaces strictly over C, and `IsFunctorEquivalence` for that map. Thus this is
  a natural equivalence of the presheaves in their right-fibration model. It is
  not merely a family of unrelated equivalences on fibers. Equivalences over
  the base preserve right-cartesian edges; all simplicial families are present.
* The first `↔` is both necessity and sufficiency, without assuming the initial
  choice of r is functorial. There is no chosen family in the hypothesis.
* Having a left adjoint to i is
  `∃ L : C ⟶ E, Nonempty (CoherentAdjunction L i) ...`.
  The second `↔` uses
  `∀ c : C _⦋0⦌, ∃ l : E _⦋0⦌, MappingPresheafRepresentedBy i c l false`.
  Here `false` reverses the endpoint conditions in the existing comma definition.
  The fibers are Map_C(c,i(e)) and Map_E(l,e), and the equivalence over E is
  exactly the covariant representing equivalence, in the left-fibration model.
* Assembly into a coherent functor is witnessed by the actual simplicial maps
  R and L in the respective existential conclusions.
* Equivalence of mapping-space bifunctors is
  `MappingBifunctorsEquivalent F R` and `MappingBifunctorsEquivalent L i`.
  `mappingBifunctorTotal A B` is the actual pullback of both arrow-endpoint
  evaluations along `(c,d) ↦ (Ac,Bd)`. Its fiber is Map(Ac,Bd).
  The equivalence is a map of the entire correspondences strictly over C × D
  (respectively C × E), with `IsFunctorEquivalence`. For correspondences
  cartesian in the source and cocartesian in the target this is exactly the
  natural equivalence of their space-valued bifunctors. Equivalence over the
  base preserves those cartesian/cocartesian edges, hence includes both variances
  and all higher parameters. No arbitrary mapping-space action is substituted.
* Universal representing maps being the unit/counit are included in the existing
  `CoherentAdjunction.universal_unit` and `.universal_counit`. They identify the
  actual unit/counit evaluations with initial/terminal comma vertices whose
  first coordinates are L(c) and R(d). Thus the assembled functor supplies
  representing objects, with its own universal maps.
* Units and counits are `.unitEdge` and `.counitEdge` in the full internal functor
  simplicial sets, with their specified endpoints. `.left_triangle` and
  `.right_triangle` are 2-simplices of the full functor simplicial sets with
  degenerate identity long edges. The transformations, triangles and universal
  comma properties retain coherent diagram parameters and their higher
  simplices. This is the published universal-arrow model of coherent adjunction,
  equivalent to the unit-transformation definition of HTT the project server--8.
* No presentability, completeness, nonemptiness or existence of other adjoints
  is assumed. Both criteria are conjoined; neither variance is omitted.

Dependency declarations used:

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.mappingSpace`, `IsWeakHomotopyEquivalence`, `comma`,
  `commaSubcomplex`, `IsFunctorEquivalence` and the coherent internal-hom
  conventions. Read their entire signatures and docstrings.
* `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  `HomotopicalAlgebra.ModelInfinity.CoherentAdjunction`, read lines 61--99,
  including every structure field. Its definition is independent of the
  Quillen theorem later in that module. It is bound by the new definition node.
* `Sheaf.CategoryTheory.RightPinchComparison`:
  `arrowEndpoints` supplies the actual canonical endpoint map used in the
  bifunctor construction. The theorem `right_pinch_comparison` is retained as
  a proof-dependency import. Its signature and full docstring were read.
* `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`:
  `enhanced_functor_cone_calculus` is a stated proof dependency and retained as
  a nonpublic import. Its signature and docstring were read.
* Mathlib's `SSet`, `SSet.Quasicategory`, `SSet.KanComplex`, internal hom,
  `SSet.uliftFunctor`, and degreewise categorical pullback/product primitives.
  Read `SimplicialSet/Basic.lean:73--74` for the exact lift signature.

Edge cases checked before writing: if C is empty and D nonempty, the right
representability condition fails because no r exists, as does existence of R.
If both are empty, representability is vacuous and the unique empty functor has
empty unit/counit diagrams; the criterion holds. Dually E empty and C nonempty
fails both left-adjoint conditions. Empty mapping spaces are permitted small Kan
models: no nonemptiness is imposed by `HasSmallMappingSpaces`. For the terminal
category and the identity functor, the identity comma equivalences represent
both variances. An identity functor on a noncomplete category, for example the
nerve of the rational order, still has its adjunction and representables, showing
that no completeness has slipped in. A large discrete category with small Hom
spaces is admitted by the independent ambient universe and the small-model test.
For an ordinary category, the two comma projections reduce to categories of
elements of the stated Hom functors, and their equivalences over the base reduce
to natural representing bijections, checking both endpoint orientations.

Searches actually run:

* msearch leanfinder: "A functor of infinity categories has a right adjoint iff
  each mapping space presheaf is representable with coherent unit and counit".
  Eight hits, all ordinary adjoint/representable or nerve-adjunction statements.
* msearch loogle: `"isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top"`.
  One hit. Read `CategoryTheory/Adjunction/PartialAdjoint.lean:286--300`:
  this uses ordinary categories and Hom sets, not our quasicategories.
* msearch grep: `adjunction|adjoint|representable` in
  `AlgebraicTopology/Quasicategory`: zero hits.
* msearch leansearch: "An equivalence of right fibrations over a quasicategory
  is a natural equivalence of space valued presheaves; representable mapping
  presheaf". Eight hits concerning ordinary presheaves, no matching criterion.
* msearch leansearch: "Coherent adjunction of quasicategories with unit counit
  triangle simplices and universal comma objects". Eight ordinary categorical
  or bicategorical hits, no coherent quasicategorical structure.
* msearch leanfinder: "Representability of infinity categorical mapping
  presheaves via equivalences of right fibrations over the base". Eight hits,
  ordinary representables or standard simplices, no matching criterion.
* msearch grep: `CoherentAdjunction|representable|adjunction` in
  `AlgebraicTopology/Quasicategory`: zero hits.
* rg in upstream `WeilConjectures` by item id: no hit; by adjunction/adjoint
  in SixFunctors: ordinary categorical adjunctions only. rg for proposed names
  and for representability in project `lean/Sheaf/CategoryTheory` found the
  published CoherentAdjunction helper and the specialized pointed-model
  endofunctor adjunction, not this criterion or these correspondence helpers.
* Whole-DAG definition-node searches for representability and the exact
  `CoherentAdjunction` primary declaration found no independent definition node
  for these data. The ModelInfinity theorem node does list the helper among
  its declarations; its theorem statement is a different, Quillen-specific
  assertion. `blueprint_refs.py search 'coherent adjunction'` and
  `... search 'mapping presheaf'` both returned zero blueprint nodes.
  The broader `... search 'representable'` was also examined.

The single module compiled cleanly using scompile.py, both as a sandbox and as
its intended library path. Initial import-path and intentional two-universe
linter issues were repaired; the final compile has no errors or warnings.
No STATEMENT-DISPUTED and no mathematical statement correction.

## New nodes

`def-coef-coherent-adjunction-data` binds the already published general
`HomotopicalAlgebra.ModelInfinity.CoherentAdjunction` with `existing: true`;
it introduces no Lean file and no duplicate definition. The definition statement
lists the exact coherent edges, triangles and universal comma fields of that
structure. Its source is HTT the project server--8 and the equivalent universal-arrow
formulation. Searches above found no independent DAG definition node or exact
Mathlib match. Its existing project match is recorded explicitly. This separates
the helper's definition dependency from the Quillen theorem that currently owns
its source module: adding the latter theorem as a statement dependency would
create a cycle through cosimplicial frames, hammock localization, coherent nerve
comparison and system localization back to this criterion. The extracted
existing binding depends only on enhanced diagrams and has no such DAG cycle.
The item adds this definition id to stmt_deps. Its other helper definitions are
coordinate constructions for this item's own representability/bifunctor clauses,
all recorded in lean.declarations, rather than independent new notions.

## Second reading by NV

Independent second reading, 2026-10-17. I opened the item node, all of its
statement dependencies, the delivered module, the complete shared adjunction
structure, the comma/mapping-space/equivalence definitions, and the signatures
and proof docstrings of the two available theorem dependencies. The theorem
says what the node says; no statement correction is needed.

Source check: this node has no Stacks source. I read [HTT, §5.2.4,
Lemma the project server and Proposition the project server](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
printed pp. 350--351, and Definition the project server / Proposition the project server,
printed pp. 342--343. The former gives representability after pullback of
representable right fibrations as the right-adjoint criterion; the latter
characterizes adjunction by a unit inducing equivalences on mapping spaces.
Neither assumes completeness or presentability. I also read
[Kerodon 02FV](https://kerodon.net/tag/02FV) and
[02F1](https://kerodon.net/tag/02F1): the local left-adjoint criterion and the
mapping-space formula agree with both orientations used here. The comma
presentation is an equivalent model of those space-valued functors.

Object/hypothesis/conclusion inventory, with Lean and verdict for each:

1. Two fixed size levels, small U and ambient U' containing U:
   `universe u v` and `SSet.{max (u + 1) v}`. The ambient level can be
   arbitrarily larger than u, while u+1 enforces the required strict size gap.
   The categories share an ambient universe, as the node requests. Pass.
2. Infinity categories C, D, E: explicit `Quasicategory C`, `Quasicategory D`,
   `Quasicategory E`. `SSet` and `Quasicategory` are the actual Mathlib notions
   used by `def-cbc-enhanced-diagrams-cones`, not an ordinary-category model.
   Pass.
3. U-small mapping spaces for every pair: `_hC`, `_hD`, `_hE` use
   `HasSmallMappingSpaces.{u, v}`. Its actual body supplies a Kan complex
   `K : SSet.{u}` and a weak equivalence from `SSet.uliftFunctor.obj K`
   to the dependency's `mappingSpace`. I checked Mathlib's lift signature
   in `SimplicialSet.Basic`: the codomain is in the maximum of the two levels.
   This tests small homotopy type, not the number of simplices in a chosen
   large model. The dependency's `IsWeakHomotopyEquivalence` tests realization
   components and every positive based homotopy group. Pass.
4. Arbitrary coherent functors F:C→D and i:E→C: `(F : C ⟶ D)` and
   `(i : E ⟶ C)` are simplicial maps. No exactness, accessibility,
   nonemptiness, finiteness, or other categorical property is assumed. Pass.
5. Right-adjoint existence: the first existential is an actual simplicial
   map `R : D ⟶ C` with `Nonempty (CoherentAdjunction F R)`. This uses
   the shared general definition, not the subsequent Quillen theorem or
   an adjunction of ordinary homotopy categories. Pass.
6. Right representability at each d: `∀ d, ∃ r,
   MappingPresheafRepresentedBy F d r true`. Opening `commaSubcomplex`
   verifies that `true` fixes the target at d and the source at F(c)
   in every degree. Thus its projection encodes Map_D(F(c),d), and the
   identity-functor comma encodes Map_C(c,r). The comparison is an actual
   simplicial map strictly over C and an `IsFunctorEquivalence` of entire
   total categories. In the right-fibration model this is a natural
   representing equivalence, with all parameters retained. Pass.
7. Both directions and pointwise quantifier order: the first `↔` has exactly
   `∀ d, ∃ r`, with no prechosen coherent assignment on the hypothesis side.
   The existential functor is on the adjunction side. Pass.
8. Dual left-adjoint existence and representability: the second `↔` uses
   `∃ L : C ⟶ E, Nonempty (CoherentAdjunction L i) ...` and
   `∀ c, ∃ l, MappingPresheafRepresentedBy i c l false`. The `false`
   endpoint conditions fix the source at c and target at i(e), so the
   fibers are Map_C(c,i(e)); the identity comma has fibers Map_E(l,e).
   This is the covariant left-fibration version, with no reversal error.
   Both criteria are conjoined. Pass.
9. Assembly into coherent functors: R and L are themselves simplicial maps,
   hence include all coherent action, rather than only assignments on
   objects or on homotopy classes. Pass.
10. Natural equivalence of mapping-space bifunctors:
    `MappingBifunctorsEquivalent F R` and its `(L,i)` counterpart compare
    the pullbacks `mappingBifunctorTotal (𝟙 C) R` and
    `mappingBifunctorTotal F (𝟙 D)` over C×D. I checked the definition of
    `arrowEndpoints` in `RightPinchComparison`: first source, then target.
    The fibers are respectively Map_C(c,Rd) and Map_D(Fc,d). This is the
    entire two-sided arrow correspondence, retaining contravariance in c
    and covariance in d; a comparison over the base preserves the relevant
    Cartesian/cocartesian transport, since the fibers are spaces. The
    equivalent total correspondences express the natural bifunctor
    equivalence, not an unconnected family of fiber equivalences. Pass.
11. Universal representing maps are unit/counit components:
    `CoherentAdjunction.universal_unit` and `.universal_counit` specify
    initial/terminal comma vertices. Their first coordinates are L(c)/R(d),
    and their second coordinates are evaluations of the very
    `.unitEdge`/`.counitEdge` in the same structure. These are neither
    unrelated universal arrows nor arbitrary choices of transformations.
    Initial representing choices may be replaced by equivalent ones, as
    the node's proof explicitly allows. Pass.
12. Coherent units, counits, triangles, and higher parameters:
    `.unit_src`, `.unit_tgt`, `.counit_src`, `.counit_tgt` fix endpoints
    in full internal homs. `.left_triangle` and `.right_triangle` require
    2-simplices there with the whiskered edges and degenerate identity long
    edge, with the orientations Lη followed by εL and ηR followed by Rε.
    The internal homs retain arbitrary diagram simplices, so these are
    coherent transformations and homotopies, not equations only in hC.
    The universal-arrow fields express the full mapping-space universal
    properties. This is the shared equivalent adjunction presentation. Pass.

Dependency/new-node reading: `def-coef-coherent-adjunction-data` is new as a
DAG binding, not as a Lean definition. I read all fields of
`HomotopicalAlgebra.ModelInfinity.CoherentAdjunction` in
`Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`, lines 69--99.
The new node lists exactly its unit, counit, endpoints, triangle simplices,
and evaluated universal comma objects. Its source supports this equivalent
universal-arrow presentation. Its sole statement dependency is the shared
enhanced-diagram definition. The existing declaration record matches its
signature verbatim; it adds no model-category or Quillen hypotheses. The
owning theorem's DAG record lists this helper, but no independent definition
node already binds it. Reusing the helper does not add that downstream theorem
as a mathematical prerequisite. I checked the required definition-node fields,
search kinds, empty proof fields, audit state, chapter/unit, and blueprint
ancestor `prop-coef-integral-exceptional-adjoint` with `blueprint_refs.py ancestor`.
There is no new dependency module. The available proof-dependency modules are
imported; pointwise Yoneda evaluation and the local adjoint criterion have no
recorded Lean declaration yet, so there is no module to import for them.

Edge cases: empty C with nonempty D has neither a representing r nor a map
R:D→C; empty D makes both sides of the right criterion true when F exists.
Empty E with nonempty C makes both sides of the left criterion false; empty C
makes the dual conditions vacuous when i exists. No Kan definition requires
vertices, so empty mapping spaces are admitted. Terminal categories and identity
functors give the usual identity correspondences. Identity on an incomplete
category still satisfies the criterion: completeness has not been introduced.
Large discrete quasicategories with small Hom spaces are permitted by the size
levels. The ordinary-category nerve specializes to the usual Hom-representability
criterion and confirms both variances. Zero objects impose no extra condition.
Schemes, characteristic, n, and external index sets are not parameters of this
statement; no corresponding case is excluded. All variables/universes are
explicitly bound under `autoImplicit false`.

Independent searches, using words different from the author's queries:

- `msearch leansearch "Quasicategory right adjoint criterion represented
  contravariant mapping functor"`: eight ordinary category-theory hits.
  Opened `Functor.rightAdjointObjIsDefined_iff` and
  `Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top` in Mathlib's
  `CategoryTheory.Adjunction.PartialAdjoint`; both concern Hom sets and
  ordinary categories, so neither states this node.
- `msearch leanfinder "Universal unit and counit in comma infinity categories
  defining an adjunction"`: eight ordinary/bicategorical hits, including
  `CategoryTheory.Bicategory.LeftLift.IsKan.adjunction`; no quasicategorical
  adjunction-data structure.
- `msearch grep "IsLeftAdjoint|IsRightAdjoint|Representable"` in
  `AlgebraicTopology/Quasicategory`: zero hits. Direct broader `rg` there
  found only uses of “representative” for edge classes.
- Direct `rg` in all upstream `WeilConjectures`, project `lean/Sheaf`,
  and the upstream name index for pointwise adjoints, representable right
  fibrations, `CoherentAdjunction`, and the proposed helper names found only
  the shared adjunction structure and citations of this criterion. Further
  searches for small mapping spaces / local smallness found ordinary
  `LocallySmall` category instances, not a competing quasicategory notion.
- Whole-DAG searches and `blueprint_refs.py search 'coherent adjunction'` /
  `'mapping presheaf'` found no existing independent definition node for
  these data. The only primary binding of the exact structure in the base
  DAG was the helper list of the model-infinity theorem, already reused.

Repairs: the module header called the project server a definition; it now correctly says
Definition the project server and Proposition the project server. The item's `lean.note` incorrectly
referred to an algebroid dependency which is absent from its actual dependency
list; I replaced that sentence by the explicit two-level universe explanation.
The same algebroid assertion in the preserved worker report above is stale;
this reading supersedes it. No mathematical statement, helper construction,
new-node binding, or dependency list was changed. The six definitions all have
real bodies; the sole postponed theorem is this item, with the four node proof
steps in its docstring. No theorem was proved. Every declaration has the source
and blueprint docstring, all module lines are at most 100 characters, and the
recorded `lean.statement` is verbatim the theorem signature.

Validation: the final delivered file compiled through `scompile.py` in both
sandbox and intended library-path modes (1.2 s / 1.3 s), with no error or warning.
The delivery dry run and push below run the server preflight and also check the
reused existing adjunction declaration.
