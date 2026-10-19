## Worker report

The module `Sheaf.CategoryTheory.RezkLocalModel` states
`SSet.RezkLocalModel.exists_rezk_model_structure`, with `sorry` as its whole proof.
All other declarations are explicit definitions or abbreviations for the objects,
canonical maps and clauses of this same node. There are no postponed helper theorems,
axioms, data chosen from unproved existence assertions, new nodes, dependency-module
repairs or statement corrections. The source node's statement and proof are unchanged.
The existing landed node `def-coef-segal-space` is added to `stmt_deps` because its
actual definitions of Reedy fibrancy, equivalence components and completeness are used.

The statement is rendered clause by clause as follows.

- **Small simplicial spaces and nested universes.** `universe u` is explicit and
  `Bisimplicial := SimplexCategoryᵒᵖ ⥤ SSet.{u}` stores vertical degree first:
  `(X.obj q).obj p = X_(p,q)`. This is the full category of bisimplicial sets, with
  no condition on objects. `Functor.uncurry.obj X.flip` is its canonical outer-first
  form in the already recorded `CategoryTheory.SegalSpace.Space`. Nerves and coherent
  presheaves live in `u+1`; the simplex index category stays in universe zero.
  This is a choice of the node's fixed nested universes, not a restriction equating
  object and morphism universes of any site or category.
- **Reedy matching maps, including degree zero.** `SegalSpace.IsComplete` unfolds to
  `IsSegal` and the degeneracy condition; `IsSegal` includes `IsReedyFibrant`.
  The latter uses `Reedy.matchingFrom (monomorphisms SimplexCategory).op` and the
  actual horn-defined Kan fibration property. Its matching diagram is precisely
  the proper opposite-injective diagram; degree zero has the empty matching diagram.
- **Homotopy Segal condition and hX.** In this Reedy-fibrant situation, the recorded
  strict consecutive-edge products in `SegalSpace.IsSegal` compute the homotopy
  products in `HomotopySegal.IsHomotopySegalSpace`: the endpoint map is a Kan
  fibration and each row is Kan. Strict endpoint fibers likewise represent the
  path-model homotopy fibers used by `HomotopySegal.simplexFiber`. Both recorded
  composition descriptions use the degree-two comparison and d1; hence the two
  inverse equations in `SegalSpace.IsEquivalenceArrow` describe invertibility in
  exactly the hX of `lem-coef-segal-dk-diagonal-equivalence`. No Reedy condition is
  being imposed on that dependency theorem; it is used here on the fibrant objects
  that the current node itself requires.
- **Equivalence components and completeness.** The actual recorded
  `SegalSpace.equivalenceArrows` is saturated by equality in pi0 and includes a
  simplex when all its vertices belong to these components.
  `SegalSpace.IsComplete` requires a factor of the actual s0 through its inclusion,
  with equality of the composite to s0 and realization-based weak equivalence of
  that factor. Thus there is no arbitrary map in place of the degeneracy.
- **Model structure.** `∃ M : ModelCategory Bisimplicial` supplies the three classes
  and all model axioms, including retract closure, two-out-of-three and the two
  lifting systems. Completeness and cocompleteness of this presheaf category are
  supplied by the existing Mathlib instances, without assumptions on X.
- **Cofibrations.** The first conjunct is an iff with `Mono f`, which in this
  set-valued presheaf category means injectivity in every bidegree.
- **Fibrant objects.** The second conjunct is an iff between M's fibrations on
  `terminal.from X` and the existing complete Segal predicate just described.
- **Exactly the specified weak equivalences.** The third conjunct is an iff with
  `Enhanced.IsWeakHomotopyEquivalence (eHomWhiskerRight SSet f Z)` for every complete
  Segal Z. The native `SimplicialObject` enrichment is vertical because of the
  chosen storage order. Expanding its `Functor.functorHom` in vertical degree q
  gives natural families parameterized by Hom(q,r); Yoneda identifies these with
  `Hom_ss(A × (Delta[q])_vert,Z)`. Its precomposition map is exactly the displayed
  `eHomWhiskerRight`, not a map on homotopy categories. The weak-equivalence
  predicate tests components and all positive based realization homotopy groups.
- **Functorial factorizations.** The next two conjuncts are
  `HasFunctorialFactorization C (F ⊓ W)` and
  `HasFunctorialFactorization (C ⊓ W) F`, with all three classes projected from
  this same M, so no independently chosen model structure can enter either one.
- **Simplicial model structure.** `SimplicialClause M` requires the recorded
  `SimplicialTensorCotensor` for this fixed native enrichment and
  `SimplicialModelLocalization.SatisfiesSM7` explicitly for M. The tensor is
  isomorphic to `X ⊗ (K ⋙ Functor.const SimplexCategoryᵒᵖ)`, namely the degreewise
  product with K in the vertical direction. Tensor/cotensor universal elements
  and their enriched representing isomorphisms give the adjunctions; SM7 is the
  actual induced corner map and Kan fibration/weak-equivalence conditions.
- **Full infinity subcategory of complete Segal objects.** `Spaces` is the actual
  coherent nerve of small Kan complexes used in the nerve-localization dependency.
  `Presheaves` is its full internal coherent functor category on N(Delta-op).
  `completeSegalObjects q` is a full subcomplex, saturated under equivalence, on
  the objectwise images of strict Reedy-fibrant complete Segal representatives.
  This is the standard presentation of complete Segal objects in space-valued
  presheaves: Reedy rectification gives representatives, and the strict products
  of those representatives compute homotopy products; conversely these conditions
  are invariant under objectwise equivalence. In particular this definition is
  independent of M, its weak equivalences and the claimed Rezk localization. It
  does not define the target to be the unknown localization. It includes all
  coherent morphisms and higher simplices between the specified vertices.
- **Objectwise comparison and coherent universal property.** `LocalizationClause`
  supplies q localizing simplicial sets at their realization-based weak equivalences.
  Its restriction to Kan complexes is normalized by `IsOrdinaryNerveMap`, so the
  space objects and all coherent-nerve simplices are the actual ones of the
  dependency, rather than an unnormalized target equivalence. Q then localizes
  the full bisimplicial category at precisely M's W into that full subcomplex.
  `FiniteReedy.IsLocalization` tests the entire coherent functor category into
  every infinity category, not just cores or homotopy categories. Finally its
  restriction along the ordinary inclusion of `Complete` is naturally equivalent
  to `objectwise q`. The latter is an actual composite of nerve maps and the
  previously constructed `FiniteReedy.comparison`, hence fixes the comparison on
  every simplex of the nerve of natural transformations. This retains mapping
  spaces and coherent composition, as requested.
- **External products and the canonical arrow.** `(box A B).obj q` has outer
  degree p equal to A_p times B_q. `boxMap` applies the two specified maps in
  these coordinates. `boxPushout i j` is `pushout.desc` of the two product maps
  from exactly the displayed span. Its commutativity proof is degreewise equality;
  no comparison is postulated or chosen.
- **Mixed cofibration and both acyclic cases.** The final conjunct universally
  quantifies arbitrary i,j and assumes `Mono i` and `Mono j`; these are exactly
  Joyal and Kan cofibrations, respectively. It asserts M-cofibrancy of the actual
  `boxPushout` and M-weak-equivalence if either i satisfies the Joyal categorical
  equivalence test or j satisfies `IsWeakHomotopyEquivalence`. The former is exactly
  `exists_joyal_model_structure` at its small-universe test (its v=0 specialization);
  that dependency proves the test independent of enlargement. It uses the entire
  ordinary category hFun(-,C), not just components or object classes.

Dependency declarations read and reused:

| Module | Declarations / purpose |
| --- | --- |
| `Sheaf.CategoryTheory.EnhancedDiagramsCones` | `SSet.Enhanced.IsWeakHomotopyEquivalence`, `fullSubcomplex`, `diagramVertex`, `AreNaturallyEquivalent`; weak equivalences and coherent subcategories |
| `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction` | `HomotopicalAlgebra.ModelInfinity.quillenAdjunctionInfinityLocalization`, including the full coherent-localization convention, read with its docstring and complete signature; retained as statement/proof import |
| `Sheaf.AlgebraicTopology.JoyalModelStructure` | `SSet.exists_joyal_model_structure`; the exact hFun categorical-equivalence test in the final conjunct |
| `Sheaf.AlgebraicTopology.KanQuillenRightProper` | `SSet.KanQuillen.right_proper_kan_quillen`; Kan cofibrations are monos, fibrations are horn lifts, weak equivalences use the given realizations |
| `Sheaf.CategoryTheory.SegalDKDiagonalEquivalence` | `SSet.segal_dk_diagonal_equivalence` and its `HomotopySegal` mapping-fiber and homotopy-Segal definitions, read in full |
| `Sheaf.CategoryTheory.SimplicialModelNerveLocalization` | `SimplicialModelLocalization.SatisfiesSM7`, `inclusionNerve`, `IsOrdinaryNerveMap`, the spaces construction of `SpacesClause`; tensor/cotensor interface is its existing public dependency |
| `Sheaf.CategoryTheory.SegalSpace` | `Space`, `IsComplete` and its actual Reedy, Segal, mapping-fiber, inverse-equation and component definitions, reused without private copies |
| `Sheaf.CategoryTheory.FiniteReedyLocalization` | `largeNerve`, `comparison`, `diagram`, `EquivalentObjects`, `IsLocalization`; reached through existing public dependency imports |
| Mathlib `SimplicialCategory.SimplicialObject` | native vertical `SimplicialCategory` and its composition/precomposition |

The already stated proof dependencies are imported without `public`: Reedy model
structure, Segal inverse evaluation, Segal vertical inner restriction, core Kan fibrations, Joyal fibration
characterizations, nondegenerate decomposition, presheaf local presentability, and
anodyne pushout products. The three proof-only nodes that still have no Lean record
are not imported: all-cofibrant left properness, simplicial presheaf localization
comparison, and simplicial Bousfield model structure.
None is needed to type the present statement. The ten-step natural-language proof
is included in the main theorem's docstring, following the original DAG proof.

Edge cases checked before finalizing:

- The empty bisimplicial set is allowed and is complete: all rows and strict
  mapping fibers are empty where appropriate, and the empty degeneracy is a weak
  equivalence. There is no `Nonempty` hypothesis on X, simplicial sets or indices.
- The terminal bisimplicial set is complete and its degree-zero matching map is
  the correct terminal map. Nothing discards the n=0 matching condition.
- The nerve of [1] with discrete vertical direction is admitted as a complete
  Segal space, so the statement does not accidentally require the outer direction
  to be Kan. A nontrivial one-object discrete group nerve is Segal but fails
  completeness because s0 is point-to-G; the predicate does not confuse it with
  a complete object.
- Empty A or B and identity i or j use the same categorical pushout construction.
  Both identities satisfy their weak-equivalence tests. There are no boundary
  dimension, endpoint, cardinality or surjectivity assumptions on i,j.
- `autoImplicit false` binds every variable and universe. All objects lie in the
  stated small universe, while the two localization nerves and coherent functor
  category use u+1, retaining their full morphism spaces.

Searches (all made for group NH and this item):

- `msearch.py leanfinder "Rezk model structure on simplicial spaces complete Segal spaces and external pushout product"`: eight hits, including Kan I/J and QCat, no Rezk model structure.
- `msearch.py loogle "SSet, HomotopicalAlgebra.ModelCategory"`: zero hits.
- `msearch.py grep "Rezk|CompleteSegal|completeSegal|rezk"`: one bibliographic hit, `Mathlib/CategoryTheory/LiftingProperties/PushoutProduct.lean:22`.
- `msearch.py leansearch "Rezk model structure on bisimplicial sets complete Segal spaces localization"`: eight hits on ordinary Kan model interfaces, strict Segal simplicial sets and ordinary localization; no exact statement.
- `rg` for `Rezk|CompleteSegal|completeSegal|rezk` in upstream `WeilConjectures` found no relevant declaration; the node-id search there also found none. The same search in `lean/Sheaf` found the Segal-space definitions and explicit completion, which were read and do not state this theorem. Searches for the proposed namespace and declaration names in upstream, Mathlib, the side library and `dag/lean_names_upstream.json` found no collision.

Source checked online: [Joyal--Tierney](https://arxiv.org/html/math/0607820),
Theorem 4.1 and Proposition 4.6. No local Rezk or Joyal--Tierney archive was found
in the permitted literature directory; archive WANTED. The mathematical proof
remains the node's already recorded proof. No statement is disputed.

Validation: the required `scompile.py NH lem-coef-rezk-local-model` wrapper compiled
both the sandbox check and the actual module path cleanly, with per-file compiler
times below three seconds and no warnings. The only sorry is the main theorem.
The required delivery dry run is the final check.

Resumption self-check (2026-10-17 UTC): the saved packet passed the initial required
dry run at commit `224ba0f458` (only the separate second reading remains). The theorem
signature matches `lean.statement` verbatim, the only `sorry` is the main theorem,
all Lean lines have at most 99 characters, and the source statement is unchanged.
The now-landed proof dependency `lem-coef-segal-vertical-restriction-inner` was read
in `Sheaf.AlgebraicTopology.SegalVerticalRestrictionInner`; its theorem
`SSet.segal_vertical_restriction_inner` supplies precisely proof steps 8--10's inner
restriction input. Its required proof-only import was added; the statement and all
definitions were retained. Compilation and a final dry run are repeated for that import.

## Second reading by NH

I did not write the statement. I read the base node, the sandbox node and the whole
module independently, together with the signatures and definitions of its recorded
statement dependencies. There is no repair note for this item. The only differences
from the base node are its Lean record and the addition of the already landed
`def-coef-segal-space` to `stmt_deps`. There is no `statement_change`, new definition
node or dependency module to audit. No mathematical mismatch was found; I preserved
the Lean source and node record and added this independent reading and searches.

Source check: this node has no Stacks source place. I opened
[Joyal--Tierney](https://arxiv.org/html/math/0607820), Sections 2--4, especially
Theorem 4.1 and Proposition 4.6, and
[Rezk](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/rezk-segal-spaces.pdf),
Sections 5--7 and 12, especially the definition in Section 6 and Theorem 7.2.
These concern arbitrary small bisimplicial sets; no nonemptiness or finiteness
hypothesis is assumed throughout. Joyal--Tierney's first box variable is Joyal
and the second is Kan, exactly as in the node. The coherent-presheaf clause is
the node's explicit formulation using its presheaf-localization dependency; it
is not incorrectly attributed to a separate clause of Theorem 4.1. The literature
archive remains WANTED as the worker reported.

Here is my object/hypothesis/conclusion checklist, in the order of the node.

| Node object, hypothesis or clause | Lean rendering and second-reader verdict |
| --- | --- |
| Fixed nested universes and all small simplicial spaces | `universe u`; `Bisimplicial := SimplexCategoryᵒᵖ ⥤ SSet.{u}`. This has every small bisimplicial set, with coordinates stored in the reverse order. `Functor.uncurry.obj X.flip` recovers the exact outer-first `SegalSpace.Space`. The nerves and coherent diagram categories live in `u+1`; no object/morphism universe equality is added. Pass. |
| Matching maps in every outer degree, including zero | `SegalSpace.IsComplete` includes `IsSegal`, which includes `IsReedyFibrant`. I opened the latter: it uses the actual matching map for `(monomorphisms SimplexCategory).op`, with the horn-defined Kan right lifting class. Thus the diagram contains the proper opposite-injective restrictions, and includes the empty matching diagram in degree zero. Pass. |
| Homotopy Segal condition and the specified homotopy category | I read `HomotopySegal.IsHomotopySegalSpace`, its constant-path comparison and path-product target, and `segal_dk_diagonal_equivalence`. The statement uses the already landed strict Segal predicate only in the Reedy-fibrant case. Its endpoint map is a Kan fibration, all levels are Kan, so the strict edge products and strict mapping fibres compute precisely these homotopy products and fibres. The degree-two Segal comparison and long face give the same composition. This is an equivalent encoding, without adding a hypothesis to the dependency theorem. Pass. |
| Union of components of invertible arrows | I opened `SegalSpace.IsEquivalenceArrow`, `SameMappingComponent` and `equivalenceArrows`. The inverse has both prescribed triangle equations on components in the fixed endpoint fibres. The subcomplex is saturated by equality in `π₀` of the whole edge space and tests every vertex. It selects the component union in the node, rather than just the identity arrows or a core in the outer direction. Pass. |
| Completeness of the actual degeneracy | `SegalSpace.IsComplete` requires `s ≫ equivalenceArrows.ι = s₀` and weak homotopy equivalence of `s`. Since the inclusion is mono, this factor is fixed; there is no arbitrary completeness map. Pass. |
| Existence of a model structure | `∃ M : ModelCategory Bisimplicial` uses Mathlib's actual model axioms. I read `ModelCategory`: retract stability, two-out-of-three, both lifting axioms and both factorizations are fields, and the two lifting pairs are characterized weak factorization systems. This presheaf category already has all small limits and colimits. Pass. |
| Cofibrations exactly monomorphisms | The first conjunct is `M...cofibrations f ↔ Mono f`, universally for every arrow. In this presheaf category monos are precisely bidegreewise injections. Pass. |
| Fibrant objects exactly complete homotopy Segal spaces | The second conjunct is an iff for `M...fibrations (terminal.from X)` and the above complete predicate. Neither implication nor the Reedy condition is omitted. Pass. |
| Exact weak-equivalence test for every complete test object | The third conjunct is an iff, for arbitrary source and target, universally testing `Enhanced.IsWeakHomotopyEquivalence (eHomWhiskerRight SSet f Z)`. I opened Mathlib's `SimplicialObject` enrichment, `Functor.functorHom` and enriched precomposition. In vertical degree q these are families of outer natural maps parameterized by maps into q; Yoneda identifies them with maps from the source times the vertical q-simplex. Precomposition is the specified induced map. `Enhanced.IsWeakHomotopyEquivalence` tests realization path components and every positive based homotopy group. Pass. |
| Both functorial factorizations | The next conjuncts are `HasFunctorialFactorization C (F ⊓ W)` and `HasFunctorialFactorization (C ⊓ W) F`, with all classes projected from the same witness M. Pass. |
| Simplicial model structure for the prescribed enrichment | `SimplicialClause M` supplies `SimplicialTensorCotensor` for the fixed native vertical enrichment and `SatisfiesSM7` with M explicitly supplied. I opened both dependency definitions: tensors and cotensors have enriched universal elements and actual representing isomorphisms; SM7 tests the induced corner map, its Kan fibration property and both trivial cases. The tensor comparison is with `X ⊗ (K ⋙ Functor.const ...)`, the specified vertical product. Pass. |
| Actual infinity category of spaces and full complete-Segal subcategory | `Spaces` is the dependency's coherent nerve of small Kan complexes; `Presheaves` is the entire internal functor simplicial set on the lifted nerve of the opposite simplex category. `completeSegalObjects q` is the full subcomplex on vertices equivalent to objectwise images of strict complete Reedy representatives. Reedy rectification gives precisely the complete Segal objects of space-valued diagrams; conversely their homotopy-limit conditions are invariant under objectwise equivalence. This predicate is independent of the unknown Rezk W and localization. It includes all higher simplices between its vertices. Pass. |
| Objectwise comparison including mapping spaces and coherent functors | `LocalizationClause` supplies the spaces localization q, normalized on all ordinary Kan-nerve simplices by `IsOrdinaryNerveMap`, and a localization Q at exactly M's W into that full subcomplex. I opened `FiniteReedy.IsLocalization`: it tests the entire coherent functor category into every quasicategory at the ambient universe, with the factorization equal to actual precomposition. `objectwise q` is the nerve of inclusion/flip followed by canonical curried evaluation. The final natural equivalence normalizes Q on the entire nerve of complete representatives. This retains mapping spaces and coherent transformations. Pass. |
| External products and the displayed canonical pushout arrow | `box A B` is `(p,q) ↦ A_p × B_q`. `boxMap` applies precisely i and j. `boxPushout` is `pushout.desc` of the two indicated product maps on the displayed span; its commuting equation is pointwise reflexivity. Its orientation is exactly the node's arrow. Pass. |
| Mixed cofibration assertion and either acyclic case | The final conjunct quantifies all four simplicial sets and arbitrary i,j, with only `Mono i` and `Mono j`. The recorded Joyal and Kan nodes identify these with the two cofibration hypotheses. It asserts cofibrancy of `boxPushout i j` and weakness if either the Joyal hFun equivalence test for i or the realization weak-equivalence test for j holds. I read the Joyal theorem and its universe-enlargement proof description: the small test here is equivalent to its larger-universe test. The disjunction includes each acyclic case independently. Pass. |

Edge cases: the empty simplicial space and the terminal one are admitted, with
no `Nonempty` binder. The zero-degree matching condition is retained, while the
Segal comparisons start at degree two. Empty external factors and empty pushout
corners are formed by the same canonical constructions. Identity i or j is
allowed; neither weak-equivalence alternative requires the other variable to be
weak. The outer nerve of the walking arrow with discrete vertical direction is
complete, and is not forced to be Kan in the outer direction. A nontrivial
discrete group nerve is Segal but fails completeness, as its degeneracy is the
point-to-group inclusion. There are no ring, characteristic, scheme or integer
parameters, so characteristic and empty-scheme cases do not arise. `u` is arbitrary,
including zero, and every variable is bound under `autoImplicit false`.

Independent duplicate searches, run through `msearch.py NH lem-coef-rezk-local-model`:

- LeanFinder: `model category of simplicial presheaves localized at spines and
  walking equivalence with mixed box product`: eight hits, including `SSet.QCat`,
  the Kan class structures and `SimplicialNerve`; none states the Rezk theorem.
- LeanSearch: `complete Segal space model structure with weak equivalences tested
  by enriched mapping complexes`: eight hits on general model structures, Kan
  lifting classes and homotopical functors; no complete Segal model theorem.
- Loogle: `SSet → Prop`: twelve hits including `KanComplex`, `Quasicategory` and
  `IsStrictSegal`. Those predicates do not define complete Segal spaces or supply
  this model structure. An earlier `ModelCategory, SimplexCategory` query was
  rejected for an unknown unqualified identifier; the valid query replaced it.
- Wrapper grep: `complete.*Segal|Segal.*complete|simplicial.*localization`: no hits.
  I also ran local `rg` with `Rezk|rezk|completeSegal|CompleteSegal` over the allowed
  upstream source, Mathlib and project Lean. Upstream has no matching theorem;
  Mathlib has a bibliographic Rezk reference. The project has the already reused
  Segal definitions, inverse evaluation and explicit completion, whose signatures
  do not state this model-structure theorem. I read the actual native enrichment
  rather than introducing another enriched Hom.

H4/H5/H6/H8/H9 audit: all twelve declarations are public and listed in
`lean.declarations`. The helpers construct this node's coordinate convention,
canonical maps and conclusion clauses with real data. The only `sorry` is the
main theorem; the short proofs inside constructors check functoriality or a
commuting equation. Each declaration has its source and blueprint docstring,
and the theorem docstring follows all ten proof steps, including the degree-zero
boundary test in the final step. All currently recorded proof modules are
imported, including `SegalVerticalRestrictionInner`; the three unstated proof-only
nodes are explicitly listed in the worker report. No new helper node or dependency
repair is required. No file-local notation or instance hides a statement parameter,
and every Lean line has at most 100 characters.

Validation: the theorem signature equals `lean.statement` verbatim. I independently
ran the prescribed `scompile.py NH lem-coef-rezk-local-model
lean/Sheaf/CategoryTheory/RezkLocalModel.lean`: both sandbox and actual module checks
passed cleanly, in 1.6 s and 1.9 s respectively, with no warning or error. The
independent reading leaves the mathematical statement and module unchanged.
