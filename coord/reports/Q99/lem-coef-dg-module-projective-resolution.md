## Worker report

Item: `lem-coef-dg-module-projective-resolution`, group Q99, stage 2.
Module: `Sheaf.CategoryTheory.DGModuleProjectiveResolution`.
Main declaration: `CategoryTheory.DGModuleProjectiveResolution.exists_projective_enhancement`.

The module states the complete result with one postponed theorem. All other declarations
are definitions or a structure spelling out data in this node. There is no `sorry` in
data, no axiom, no arbitrary proposition parameter, and no assumed projective replacement
or localization. The theorem concludes existence of a fully normalized dg presentation
and all of the asserted replacement and localization properties.

I refreshed the node copy from the shared base after reading the Q23 maintenance report
and repair note. Neither withdrawn scratchpad nor its binding was restored. The
complete-algebroid prerequisite now has the landed Q80 interface. I read its actual
`completeCategory`, `IsComplete`, `homObject`, `IsFullyFaithful`, and the coherent total
and fixed-object algebra definitions. The rectification theorem remains exclusively a
proof dependency. No other unstated DAG theorem is formalized here.

### Clause-by-clause reading

* **Sizes and a small integral dg category.** The theorem binds
  `B : IntegralDGCategory.{u, v}` and the module declares every universe explicitly.
  Its object and mapping universes are independent. Module values use `max u v w`,
  a chosen bound containing the objects, mapping groups and module values. The full
  category of these modules and its coefficient lift use `max u v w + 1`. The lift is
  `ULift ℤ`, not a change of coefficient ring. There is no equation between input
  universes and no `Small` or nonemptiness hypothesis.
* **Complexes, differential, composition, and identities in B.** The recorded
  `IntegralDGCategory` uses `CochainComplex AddCommGrpCat ℤ`, a bilinear homogeneous
  composition, closed identities, the two unit laws, associativity and the graded
  Leibniz identity. These are precisely unital associative chain-map composition with
  differential of degree one and square zero.
* **Right modules.** The recorded `IntegralDGCategory.RightModule` has `val` complexes,
  bilinear `act`, `act_unit`, `act_assoc`, and `d_act`. These encode the action
  `M(V) ⊗ B(U,V) -> M(U)` with the stated sign convention. No second module definition
  is introduced. `ModuleDGModel.modules` is a bijection onto ALL such modules at the
  chosen bound, including unbounded ones.
* **The displayed Hom complex.** `ModuleDGModel.dg` uses the recorded `Dg.Cat`.
  `graded x y r` is a bijection from its degree-r Hom group to the recorded
  `RightModule.GradedMap (modules x) (modules y) r`. Its action equation is unsigned
  `f(ma)=f(m)a`. `graded_zero` and `graded_add` fix the additive structure, and
  `differential` fixes the differential to Mathlib's `HomComplex.δ r (r+1)`, namely
  `d_N f - (-1)^r f d_M`. This fixes every integer degree, rather than only H^0.
  `identity` and `composition` identify the dg units and multiplication with the
  identity cochain and componentwise composition of graded maps, including the
  degree-order identification `q+p=p+q`.
* **Closed degree-zero maps.** `Ordinary` is Mathlib's `ForgetEnrichment` for the
  cochain enrichment. Its arrows are maps from the tensor unit to a Hom complex,
  equivalently closed degree-zero elements. `closedElement` evaluates such a map on
  the canonical generator 1 in degree zero. `evaluation_obj` and `evaluation_map`
  fix evaluation on objects and arrows to the actual objectwise module chain maps;
  the heterogeneous equality transports only across the specified object equalities.
* **Acyclicity, quasi-isomorphisms, projectivity.** `IsProjective` is exactly the
  recorded `RightModule.IsHomotopicallyProjective`, whose tests quantify over all
  objectwise acyclic right modules, all integer degrees, all closed graded module
  maps, and their boundary primitives. Objectwise acyclicity is the recorded
  `(val U).Acyclic`. `weakEquivalences` requires `QuasiIso` of the actual evaluation
  chain map for EVERY `U`; Mathlib's `QuasiIso` tests all cohomology degrees. It is
  neither a condition on degree-zero components nor on only one cohomology group.
* **Replacement of EVERY module.** The first conjunct of the theorem is
  `∀ M, ∃ Q q, D.IsProjective Q ∧ D.weakEquivalences q`. The `modules` equivalence
  identifies this quantifier with all input right modules. In particular there is
  no given replacement as a hypothesis and no functorial strict enriched replacement
  requirement.
* **The full projective dg category.** `projectiveDG` is a literal subtype of `D.dg`
  on `IsProjective`. Its Hom objects, units, and composition are the original ones.
  `inclusion` is the enriched inclusion and is the identity on Hom complexes. No
  smaller family of selected projective replacements is substituted for the full
  subcategory.
* **Enhanced localization, including all coherent composition.**
  `PresentsEnhancedLocalization` concludes an actual
  `FiniteReedy.IsLocalization D.weakEquivalences q`. That published predicate requires
  a quasicategory, inversion of the specified arrows, and an equivalence on the
  ENTIRE coherent functor category into every quasicategory. It does not merely
  localize an ordinary H^0 category or compare sets of equivalence classes.
  The projective dg category has the recorded `DgRealization`, with its exact
  Alexander--Whitney Hom composition on every simplex, identities, and the actual
  coherent nerve. The comparison functor `F` is fixed on objects and on every
  closed zero-degree arrow by `IsRealizationComparison` and `simplexValue`.
  `IsOrdinaryNerveMap θ` fixes every path in every coherent simplex to the ordinary
  composite. The functor equivalence `e` then identifies THIS coherent nerve with
  the localization. Retaining the full normalized dg category together with this
  coherent presentation is a concrete dg presentation of the enhanced localization;
  one does not replace the dg enhancement by its nonpositive mapping spaces alone.
  Its complete derived-enrichment interpretation is the proof's application of the
  existing dg-enrichment-rectification node, not an added statement assumption.
* **Compatibility with localization and composition.** The specified
  `AreNaturallyEquivalent` compares `nerve(inclusion) ≫ q` with
  `nerve(F) ≫ θ ≫ e`. This is an equivalence EDGE in the entire coherent functor
  category, including all higher transformation simplices. The comparison is the
  single actual dg inclusion and the normalized realization, not unrelated
  pairwise equivalences of Hom objects. Thus all compositions and units are those
  of the same dg presentation, and the localization square commutes coherently.
* **Derived Hom with ANY target.** `postcompose Q f` is the real chain map obtained
  by inserting the closed arrow `f` via the right unitor and then composing in the
  dg category. The second theorem conjunct states that it is a quasi-isomorphism
  for every projective Q and every objectwise quasi-isomorphism f, with no
  projectivity restriction on either target. For a replacement `q_M:QM -> M`, this
  is the canonical comparison
  `Hom(Q,QM) -> Hom(Q,M)`. Its source is the Hom complex in the projective dg
  enhancement just identified with the localization. Therefore the unreplaced
  `Hom(Q,M)` represents the same derived mapping complex. This description is in
  complexes at all integer degrees, not only in H^0 or in sets of maps. The formula
  for postcomposition, the single dg composition, and the coherent localization
  square fix its target naturality and composition compatibility. No flatness of
  the mapping complexes or exactness of an underived tensor is asserted.
* **Quasi-isomorphisms between projectives.** The third theorem conjunct assumes
  precisely that both source and target are projective and that the given arrow
  is objectwise a quasi-isomorphism. `HasHomotopyInverse` concludes an ordinary
  (hence closed degree-zero) inverse and degree-minus-one elements h and k with
  `dh = gf-1` and `dk = fg-1` in the actual Hom complexes.
* **Equivalences versus H^0 isomorphisms.** The last clause inside
  `PresentsEnhancedLocalization` quantifies over every pair of projective modules.
  On the left it requires an equivalence edge with the specified localization
  endpoints. On the right it requires a closed zero-degree map and precisely the
  two boundary equations above. This is exactly invertibility in the category
  with H^0 Hom morphisms; representatives are used to avoid introducing a second
  quotient category. Both directions are stated.

### Dependencies and source inspection

The following recorded interfaces were read and used:

* `Sheaf.CategoryTheory.SemiFreeDGModule`: `IntegralDGCategory`, `RightModule`,
  `RightModule.GradedMap`, `RightModule.IsAcyclic`, and
  `RightModule.IsHomotopicallyProjective`.
* `Sheaf.CategoryTheory.DgCategoryFreeCellCalculus`: `Dg.Cat`, `Dg.Fun`, `Dg.hom`,
  `Dg.unit`, `Dg.mul`, and its existing cochain monoidal structure.
* `Sheaf.Paper.DoldKanHomology`: `DgRealization`, `simplexValue` and the
  fixed Hom-composition, identity, and coefficient-universe interfaces.
* `Sheaf.CategoryTheory.SimplicialModelNerveLocalization`:
  `SimplicialModelLocalization.IsOrdinaryNerveMap`.
* `Sheaf.CategoryTheory.FiniteReedyLocalization`: `largeNerve`, `IsLocalization`,
  and the full local-diagram category in its definition.
* `Sheaf.CategoryTheory.CompleteAlgebroid` and its prerequisites: the actual coherent
  enhanced-category primitives, including `AreNaturallyEquivalent`,
  `IsFunctorEquivalence` and `IsEquivalenceEdge`. The complete-algebroid interface
  was read in full as described above; the statement gives a concrete dg presentation
  rather than choosing an unspecified complete algebroid from rectification.
* Mathlib: `ForgetEnrichment`, enriched categories and functors, `QuasiIso`,
  `CochainComplex.HomComplex.Cochain`, `HomComplex.δ`, unitors and `singleObjXSelf`.
  The actual `HomComplex.δ` source was inspected for its sign convention.

The five extra `stmt_deps` are the already landed owning nodes for the first five
interfaces above. They supply notions used to state this item, not new theorem
hypotheses. Their records are not changed. A read-only traversal of both dependency
edge types found no path from any added node back to this item. The stated proof
dependencies `SemiFreeDGModule` and `DGModuleSemiFreeReplacement` are imported;
the as-yet-unbound quotient and rectification theorem nodes are retained in the
DAG and the proof docstring, not made statement gates or re-stated here.

The mathematical source was read at Keller Sections 3.1--3.2, Proposition 3.1 and
Theorem 3.2, at https://webusers.imj-prg.fr/~bernhard.keller/publ/dgcat.pdf.
The proof docstring follows all six steps of the refreshed DAG proof, including the
derived (not underived) tensor correction term and the inverse-lifting calculation.

### Edge cases and semantic audit

* The empty dg category is permitted: its right-module and action data are vacuous,
  but the zero module and its identity replacement still exist. Nothing assumes an
  object of B or a nonempty indexing type.
* For zero mapping complexes and the zero module, the unit and boundary equations
  still have their ordinary meaning; no cancellation or nonzero hypothesis is used.
* The complexes and graded maps range over ALL integers. There is no boundedness,
  degreewise projectivity, flatness, or connective hypothesis anywhere.
* Independent u, v and w are retained. The common maximum and its successor are
  universe enlargement for modules and their category, not universe equalities.
* `graded` is an equivalence onto ALL action-compatible maps, so the model cannot
  discard Hom elements. Differential, addition, identity and composition are
  normalized; the model cannot replace the mapping complex by zero, a truncation,
  a degree-zero Hom set or an arbitrary object.
* Every category, functor, comparison and equality has a concrete type. There are no
  abstract `Prop` law fields, tautological localization predicates, mere `Nonempty`
  placeholders, hidden `let` hypotheses, private definitions or local notation.
* Acyclicity and quasi-isomorphisms are the recorded all-degree notions. Closed
  zero-degree inverses and the two actual degree-minus-one boundaries ensure the
  homotopy-inverse condition has not been weakened to objectwise invertibility.

No statement correction or disputed statement is required. No new independent
notion or unusable dependency interface required an extra node or dependency module.
`ModuleDGModel` and its helper definitions spell out only the dg Hom, projective
subcategory, and enhanced-presentation clauses explicitly introduced by this item.

### Searches

Fresh prescribed `msearch.py` calls:

* LeanFinder: `Every unbounded differential graded module over a small dg category
  has a homotopically projective resolution computing derived mapping complexes`:
  eight ordinary projective-resolution and K-projective-complex hits, including
  `CategoryTheory.projectiveResolutions` and `HomotopyEquiv.isKProjective`; none
  states the unbounded dg-module and coherent-localization result.
* Loogle: `"DGModule", "DGCategory", "IsKProjective"`: zero hits.
* Mathlib grep: `DGCategory|DgCategory|dgCategory|dgModule|homotopically.?projective`:
  zero hits.
* LeanSearch: `Enhanced localization of differential graded modules by homotopically
  projective modules`: eight hits about scalar/module localizations, ordinary
  derived categories and projective objects; no dg-module enhanced-localization match.

Direct `rg` searches of the upstream source and `lean/Sheaf` for dg-category,
right-module, graded-map and homotopical-projectivity names found the two landed
module conventions and the existing dg-category interface listed above. The
independent-universe `IntegralDGCategory.RightModule` is reused. Searches for the
item id in the upstream source found no declaration. Searches for a dg nerve found
the published Dold--Kan/coherent-nerve infrastructure, which is reused rather than
reimplemented. The upstream declaration-name index was searched for the new names;
no name collision was found.

### Validation

The complete delivered module compiled through `scompile.py` both as a sandbox
module and at its library module path, with no errors or warnings. The initial
universe-inference issue was repaired by explicit coefficient-complex levels;
the three subsequent long-line warnings were removed. The last clean run took
37.7 seconds for the sandbox file and 29.2 seconds for the module-path confirmation,
each within the prescribed 60-second per-file limit. No global build was run.

`deliver2.py Q99 lem-coef-dg-module-projective-resolution --no-push` returned
`OK (dry run)`: its generated commit passed the server preflight and compilation.
The packet has exactly the item's module, node record and worker report. A final
comparison with the shared node confirms that only `lean` and the five added landed
statement dependencies differ; the mathematical statement and proof are unchanged.

## Second reading by Q99

Independent maintainer second reading, 2026-10-17, of immutable delivery
19c6192634d15b42e50dab5f8245de7b6dc3ae19. This section records the independent
review requested by the launcher; the reader did not author the delivery.

1. **Objects and sizes — correct.** The binder `B : IntegralDGCategory.{u, v}`
   uses the recorded small integral dg category, including closed identities and
   signed Leibniz composition. Its right modules are the recorded `RightModule`,
   with unital associative bilinear actions satisfying `d_act`. The independent
   input sizes remain independent; `max u v w` and its successor enlarge the
   universe to contain modules and their full category. No boundedness, flatness,
   projectivity of B's complexes, or nonempty-object hypothesis was introduced.
2. **Full Hom complex — correct.** `ModuleDGModel.modules` covers all modules;
   `graded` covers all action-compatible maps in every integer degree. Its zero,
   addition, differential, identity and composition equations fix the complex and
   dg operations, rather than leaving unspecified laws. In Mathlib `δ r (r+1)`
   has coefficient `(r+1).negOnePow` on the source-differential term, hence exactly
   `d_N f - (-1)^r f d_M`. `Dg.mul` includes the braiding for reversed tensor
   order; the stated composition normalization is ordinary graded composition.
3. **Closed arrows and quasi-isomorphisms — correct.** `Ordinary` has tensor-unit
   maps as arrows. `closedElement` evaluates their degree-zero component at 1.
   `evaluation_obj` and `evaluation_map` force these arrows to be the actual
   objectwise module chain maps. `weakEquivalences` tests `QuasiIso` at every
   object and thus every cohomology degree. The recorded homotopical-projectivity
   predicate tests all acyclic modules and all integer-degree Hom cycles.
4. **Replacements — correct.** The first conjunct quantifies over every module
   through `modules`, and concludes a projective source and a quasi-isomorphism
   to that module. Replacement data are conclusions, not extra assumptions.
5. **Enhanced localization — correct.** `projectiveDG` is the literal full dg
   subcategory, and `inclusion` has identity Hom maps. `DgRealization` retains the
   specified Dold--Kan Hom spaces and Alexander--Whitney compositions.
   `IsRealizationComparison` fixes closed arrows; `IsOrdinaryNerveMap` fixes the
   ordinary-to-coherent map on all simplices. `FiniteReedy.IsLocalization`
   includes inversion and the universal property on whole coherent functor
   categories into every quasicategory at the bound. The functor equivalence
   and specified natural equivalence identify this presentation with localization.
   Together with the normalized full dg model, this retains the complexes and
   coherent compositions, rather than merely H^0.
6. **Derived Hom and compatibility — correct.** The second conjunct is preservation
   of every quasi-isomorphism in the target by actual Hom postcomposition from
   any projective source. In particular `Hom(Q,QM) -> Hom(Q,M)` is a canonical
   all-degree quasi-isomorphism for each replacement. The source is the mapping
   complex in the full projective presentation. Associative dg composition and
   the coherent localization square supply the stated compatibility. There is no
   projectivity assumption on M or an underived-tensor exactness assumption.
7. **Homotopy equivalences and H^0 — correct.** The third conjunct treats every
   quasi-isomorphism between projectives. `HasHomotopyInverse` requires a closed
   inverse and two degree-minus-one primitives for the identity defects. The
   final biconditional compares equivalence edges with these same boundary
   equations, exactly invertibility in H^0, in both directions.
8. **Dependencies and uniqueness — checked.** Read all seven snapshot statement
   dependency records and the actual interfaces in `SemiFreeDGModule`,
   `DgCategoryFreeCellCalculus`, `DoldKanHomology`, `CompleteAlgebroid`,
   `SimplicialModelNerveLocalization`, `FiniteReedyLocalization`, and the enhanced
   diagram primitives they use. The size node is explicitly metatheoretic.
   The five added owning nodes are already recorded; a traversal of statement
   and proof edges found no cycle back to this item. Read the Q23 repair note:
   the complete-algebroid dependency is retained and now has its Q80 binding.
   No discarded arbitrary-Prop draft was reused. Read the semi-free replacement
   proof dependency as context; its alternative module encoding will require
   transport when implementing the proof, not a changed mathematical assertion.
   Independent rg searches of Mathlib, slopmaster2 and side-project Lean found
   the reused module interfaces, but no duplicate of the delivered theorem.
   Mathlib `CochainComplex.IsKProjective` and ordinary projective resolutions
   concern different objects and do not replace this dg-module statement.
9. **Sources and proof plan — checked.** Read the blueprint ancestor's second
   proof paragraph (finite derived Hom adjunction), Keller §§2.2 and 3.1--3.2,
   Proposition 3.1 and Theorem 3.2, Genovese §4.1 (Definition 4.3,
   Propositions 4.4/4.6, Remark 4.5 and Corollary 4.7), and Drinfeld §14.8.
   The six-step theorem docstring follows the node's replacement, projectivity,
   cone, derived-quotient, coherent-presentation and inverse-lifting argument.
   Quotient and rectification remain proof dependencies; their future proofs
   are not assumed as hypotheses in the delivered statement. There is no
   statement correction, so a §1(C) citer audit is inapplicable.
10. **Edges and gates — checked.** Empty B, the zero module, zero Hom groups,
    all positive and negative degrees (including 0 and -1), torsion integral
    coefficients, and independent universes are covered. Definitions contain
    real data or explicit predicates; the existential model is never chosen
    into a definition from the postponed theorem. The sole delivered theorem
    has exactly `by sorry`. All 15 declaration names are recorded; the signature
    equals `lean.statement` verbatim, and all lines have at most 100 characters.
    Source/blueprint docstrings and all six proof steps are present. No pro-etale
    substitute, live Lean edit, direct ssh, repository mutation or global build
    was used in this review.

Independent compile reproduction used:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q99 lem-coef-dg-module-projective-resolution snapshot/lean/Sheaf/CategoryTheory/DGModuleProjectiveResolution.lean`

The installed wrapper uses the server private side overlay (its current
2026-10-17 implementation), and checked the immutable bytes first as
`Sheaf/Stage2/Sandbox0.lean` (8.1 s), then at
`Sheaf/CategoryTheory/DGModuleProjectiveResolution.lean` (9.0 s). Exit code 0;
no errors or warnings. Each invocation retained the wrapper's 60-second limit.
The worker's earlier compile/dry-run claims were read; no delivery or merge
wrapper was invoked by this reader.

**Finding and fix:** H11: the delivered second-reading section was only a
placeholder. Replaced that section with this independent reading, preserving
the complete Worker report. No Lean or node changes were needed. This is a
report-only landing repair, supplied as a complete replacement report.
