## Worker report

The module `Sheaf.AlgebraicTopology.SimplicialSpaceReedyCartesian` states
`SSet.SegalSpace.reedy_cartesian_simplicial`, with its sole theorem proof `sorry`.
It defines the mapping simplicial set and its two variance maps, the canonical
mapping pullback map, and abbreviates the recorded Reedy cofibration and
objectwise weak-equivalence predicates. All definitions contain real data.
The pullback commutativity proof is an application of the existing naturality
law of `MonoidalClosed.pre`; no mathematical property is assumed to construct
this map. The module and theorem docstrings cite Rezk Sections 2.3--2.5 and the
node; the theorem docstring expands all seven DAG proof steps.

I read the item, both statement-dependency nodes and their recorded source
modules, the proof-dependency Mathlib signatures, and Rezk Sections 2.3--2.5,
printed pages 5--7, at the PDF URL recorded in the item. The item agrees with
this source. No statement correction, new node or dependency repair is needed.
No STATEMENT-DISPUTED flag applies.

Hypothesis and clause correspondence:

- Small simplicial sets in fixed, freely enlargable universes: the explicit
  `universe u` and `SimplicialSpace`, namely
  `SimplexCategoryᵒᵖ ⥤ SSet.{u}`. No equality between independent site universes,
  cardinal bound, nonemptiness or fibrancy of objects is imposed.
- The Kan model structure is the existing `SSet.modelCategoryQuillen` scoped
  cofibration/fibration data together with realization weak equivalences
  `SSet.Enhanced.IsWeakHomotopyEquivalence`, as in the recorded Kan dependency.
- Reedy cofibrations are `Reedy.leftClass (epimorphisms SimplexCategory).op
  (cofibrations SSet.{u})`, the opposite-simplex positive (surjection) arrows.
  `IsReedyFibration` is reused unchanged from the published Segal module: it is
  `Reedy.rightClass (monomorphisms SimplexCategory).op (fibrations SSet.{u})`,
  the opposite-simplex negative (injection) arrows. Reedy weak equivalences are
  `∀ n : SimplexCategoryᵒᵖ, Enhanced.IsWeakHomotopyEquivalence (f.app n)`.
- Discrete outer representables `F(n)` are the existing `discreteRepresentable n`,
  whose definition is `(stdSimplex.obj ⦋n⦌) ⋙ Functor.const SimplexCategoryᵒᵖ`.
  In bidegree `(k,q)` this is `Hom([k],[n])`, constant in `q`.
  Constant spaces `cK` are the existing `constant K`.
- The cartesian internal hom is the existing `ihom`, using
  `SSet.SegalSpace.instMonoidalClosed`, which is the Mathlib complete functor
  category construction. Adjunction and Yoneda identify its `(n,q)` simplices
  with `Hom(A × F(n) × cΔ[q], X)`. These formulas characterize the same
  internal hom up to canonical isomorphism, and need no additional assumption.
- `mappingSpace A X` is `((ihom A).obj X).obj (op ⦋0⦌)`. Since `F(0)` is
  terminal, the preceding formula is exactly `Hom(A × cΔ[q],X)` in degree `q`.
  Its operators are the inherited functor operators, hence precomposition in
  the standard-simplex variable. `mappingSpacePre` is evaluation of
  `(MonoidalClosed.pre i).app X`; `mappingSpacePost` is evaluation of
  `(ihom A).map p`.
- The first theorem conjunct says `IsReedyCofibration i ↔
  ∀ n q : SimplexCategoryᵒᵖ, Function.Injective ((i.app n).app q)`.
  This is both directions of precisely the bidegree monomorphism assertion.
- For all four spaces and both maps, the next conjunct assumes exactly
  `IsReedyCofibration i` and `IsReedyCofibration j`. It asserts the same
  predicate of `((Arrow.pushoutProduct.obj (Arrow.mk i)).obj (Arrow.mk j)).hom`.
  This is Mathlib's canonical map from the displayed pushout to `B × D`;
  exchanging the two pushout legs only changes the canonical presentation.
- The remaining part of that conjunct assumes
  `IsReedyWeakEquivalence i ∨ IsReedyWeakEquivalence j` and concludes
  `IsReedyWeakEquivalence` of that same pushout-product map. Both alternatives
  remain present, without requiring the other factor to be weak.
- The final conjunct quantifies over arbitrary `A B X Y`, `i`, and `p` and
  assumes exactly `IsReedyCofibration i` and `IsReedyFibration p`.
  `mappingPullback i p` is the actual `pullback.lift` of restriction and
  postcomposition, to `pullback (mappingSpacePost A p) (mappingSpacePre i Y)`.
  Thus its target is exactly the displayed fibre product over `Map(A,Y)`.
  The conclusion `Fibration (mappingPullback i p)` is Kan fibrancy of the map.
- Its triviality clause retains both alternatives
  `IsReedyWeakEquivalence i ∨ IsReedyWeakEquivalence p` and concludes Kan
  fibration plus realization weak homotopy equivalence of that map. This is
  exactly a trivial Kan fibration, with no separate fibrancy requirement on
  either `X` or `Y`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.ReedyModelStructure`:
  `HomotopicalAlgebra.Reedy.relativeLatching`, `relativeMatching`, `leftClass`,
  `rightClass`, `model_structure`, and `simplex_reedy_structure`. The first two
  are the canonical relative pushout/pullback arrows; the next two test them
  at every object. `model_structure` supplies their model interpretation and
  the objectwise implications. Its small indexing universe can be zero for
  `SimplexCategoryᵒᵖ` and the target is `SSet.{u}`.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`:
  `SSet.KanQuillen.right_proper_kan_quillen` and `weakEquivalenceStructure`.
  The signature fixes the three model classes, identifies cofibrations with
  monos, fibrations with horn RLP and trivial fibrations with boundary RLP,
  and uses exactly the realization weak equivalences used here.
- `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`:
  `SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
  `unique_nonDegenerate_simplex`, `unique_nonDegenerate_map` (the recorded
  Mathlib match of the nondegenerate-decomposition proof node).
- `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct`:
  `SSet.anodyneExtensions_pushoutObjObjι` (the recorded Mathlib match of the
  anodyne pushout-product proof node). These last two modules are proof-only
  imports, as required for the node's proof plan.
- `Sheaf.AlgebraicTopology.SegalCartesianExponent`: reuse only its existing
  `SSet.SegalSpace.SimplicialSpace`, `instMonoidalClosed`,
  `discreteRepresentable`, `constant`, and `IsReedyFibration`. The downstream
  `cartesian_exponent` theorem is never used. Reusing these definitions avoids
  the duplicate Reedy-fibration declaration in the earlier sandbox attempt.
- `Mathlib.CategoryTheory.Monoidal.PushoutProduct`: the existing cartesian
  `CategoryTheory.MonoidalCategory.Arrow.pushoutProduct`; inspected its
  signature and canonical Leibniz-pushout definition.

Import-plan observation for the second reader/maintainer: the existing Segal
module houses foundational definitions used here, although its theorem cites
this item in its proof plan. Adding a reverse proof-only import there would
close an import cycle, so that import must be omitted under
`stages/2-statements.md` §3(7). This statement does not depend on that theorem.
The current import graph compiles. The downstream module was not edited and no
cyclic DAG statement dependency was added. If its stage-3 proof needs to import
this theorem, the shared definitions will need an authorized source reorganization.

Edge cases checked mathematically before finalizing the statement:

- Both bidegrees include zero; the degree-zero latching subset is empty.
- The empty simplicial space is allowed as any domain; all objects remain
  cofibrant and the empty-domain pushout product is the expected product map.
- Empty codomains are not excluded by new assumptions.
- Identity/isomorphism maps are covered by both triviality disjunctions.
- Either factor may be the weak equivalence, independently; the proof uses
  the coordinate flip for the other pushout-product case.
- The mapping axiom treats arbitrary Reedy fibrations, rather than fibrant
  total and base spaces; boundary lifting includes `∂Δ[0] = ∅`.
- The only object size is arbitrary `u`; all simplices and the simplex category
  are small and no finite dimension is excluded.

Searches (fresh calls, also logged by the prescribed msearch wrapper):

- LeanFinder: `Reedy model structure on simplicial spaces has monomorphisms as
  cofibrations and cartesian pushout products satisfy the simplicial mapping
  space fibration axiom`. Eight ordinary simplicial-set hits, including
  `cofibration_of_mono`, `mono_of_cofibration`, and `cofibrations_eq`; no
  simplicial-space or whole-statement match.
- Loogle: `"Reedy"`. Twelve hits, mostly unrelated Lean greedy iterator
  declarations, plus `HomotopicalAlgebra.ReedyStructure`, its degree field
  and skeletal lemma; no model structure or cartesian compatibility theorem.
- LeanSearch: `Reedy model structure bisimplicial sets cofibrations
  monomorphisms cartesian simplicial mapping space`. Eight hits on ordinary
  SSet cofibrations/fibrations, `ModelCategory.mk'`, and stability of fibrations
  under products; no exact match.
- Mathlib grep: `Reedy|latching|simplicial space` in `AlgebraicTopology`.
  Five hits, all in `Reedy/Basic.lean`, whose TODO includes constructing the
  Reedy functor model structure. No theorem matching this item.
- `rg` on upstream `WeilConjectures` for
  `Reedy|latching|SimplicialSpace|reedy_cartesian_simplicial` and literal
  `grep -rn` for the item id: no hits.
- Project `lean/Sheaf/AlgebraicTopology` search for
  `IsReedyCofibration|IsReedyWeakEquivalence|def mappingSpace|def mappingPullback|SimplicialSpace`:
  found the existing Segal definitions described above, not this theorem.
  Broader project/name-index search also found no declaration of this theorem.

Repairs to the incomplete earlier attempt: made the three internal-hom mapping
constructions noncomputable, reused the published `IsReedyFibration`, replaced
an invalid extensionality tactic with the existing naturality equality, wrapped
all lines to at most 100 characters, expanded the proof docstring, and supplied
the missing node Lean record and worker report. Every variable and universe is
bound explicitly, with `autoImplicit false`. Validation uses only `scompile.py`
and the required `deliver2.py --no-push`; no global build or direct repository
mutation is performed. The independent second reader supplies their own review.

## Second reading by Q14

I independently opened the node and the delivered module together, both recorded
statement-dependency nodes and their Lean declarations, and the published
SegalCartesianExponent definitions. I read Rezk Sections 2.1--2.5 in the node's
PDF (printed pages 5--7), including the standing convention that spaces are
simplicial sets and unnamed model structures on simplicial spaces are Reedy.
The source imposes no separate fibrancy, connectedness, finiteness, or
nonemptiness hypothesis. I also read Stacks `simplicial.tex`,
`lemma-splitting-simplicial-sets` (Tag 017R), and the four matching Mathlib
nondegenerate-decomposition signatures used in the proof plan.

My object/hypothesis/conclusion inventory and correspondence is:

| Node item | Lean rendering and verdict |
| --- | --- |
| Small simplicial sets, in any fixed universe | `universe u`; `SimplicialSpace.{u}` abbreviates `SimplexCategoryᵒᵖ ⥤ SSet.{u}` in the published Segal module. Correct; no object universe is fixed to zero. |
| Kan structure, realization weak equivalences | Scoped `SSet.modelCategoryQuillen` cofibrations/fibrations; `Enhanced.IsWeakHomotopyEquivalence` uses the actual realization, components and all positive homotopy groups. `right_proper_kan_quillen` identifies exactly these classes. Correct. |
| Reedy model on the opposite simplex category | `IsReedyCofibration` is `Reedy.leftClass (epimorphisms SimplexCategory).op (cofibrations SSet.{u})`; imported `IsReedyFibration` is `Reedy.rightClass (monomorphisms SimplexCategory).op (fibrations SSet.{u})`. `relativeLatching` and `relativeMatching` are the actual relative pushout/pullback arrows. `simplex_reedy_structure` and `model_structure` justify the identification. Correct signs and variance. |
| Reedy weak equivalences | `IsReedyWeakEquivalence f` quantifies over every outer degree and asks for the recorded weak equivalence of `f.app n`. Correct; this is not diagonal weak equivalence. |
| `F(n)` discrete in the inner direction | Existing `discreteRepresentable n := (stdSimplex.obj ⦋n⦌) ⋙ Functor.const SimplexCategoryᵒᵖ` has outer value `Hom([k],[n])`, constant in the inner index. Correct. |
| Constant outer simplicial space `cK` | Existing `constant K := (Functor.const SimplexCategoryᵒᵖ).obj K`. Correct; the two simplicial directions are not exchanged. |
| Internal hom with the displayed bidegree formula | Existing `ihom` uses the complete functor-category cartesian closed instance. Its adjunction followed by Yoneda gives `Hom(A × F(n) × cΔ[q], X)`. Correct up to the canonical representability isomorphism; no arbitrary exponential is supplied as a hypothesis. |
| Mapping simplicial set and its operators | `mappingSpace A X` evaluates that internal hom at outer degree zero. Since `F(0)` is terminal, its inner degree `q` is `Hom(A × cΔ[q],X)`. Operators are the inherited inner functor operators. `mappingSpacePre` evaluates `MonoidalClosed.pre i`; `mappingSpacePost` evaluates `(ihom A).map p`. Correct contravariance and covariance. |
| Reedy cofibrations precisely bidegree injections | First conjunct is the biconditional `IsReedyCofibration i ↔ ∀ n q, Function.Injective ((i.app n).app q)`. Correct in both directions and all bidegrees. |
| Pushout product of two Reedy cofibrations | Second conjunct universally quantifies over all four spaces and the two maps, then assumes exactly the two cofibration predicates. `Arrow.pushoutProduct` is the canonical Leibniz tensor arrow to `B ⊗ D`, with the cartesian tensor here. Its domain is the displayed pushout with its two legs interchanged. Correct canonical presentation of the same arrow. |
| Pushout product weak if either factor is weak | Same conjunct retains `IsReedyWeakEquivalence i ∨ IsReedyWeakEquivalence j`, and concludes objectwise weak equivalence of that very arrow. Correct, including both alternatives. |
| Relative mapping map for any cofibration and fibration | Third conjunct quantifies over arbitrary `A B X Y`, `i`, `p` and assumes exactly `IsReedyCofibration i` and `IsReedyFibration p`. `mappingPullback i p` is the actual pullback lift of restriction and postcomposition to `pullback (mappingSpacePost A p) (mappingSpacePre i Y)`. Correct target and canonical legs. |
| Kan fibration, trivial in either weak case | Conclusion is `Fibration (mappingPullback i p)` and, under `IsReedyWeakEquivalence i ∨ IsReedyWeakEquivalence p`, fibration plus realization weak equivalence. Correct notion of trivial Kan fibration; no fibrancy of `X` or `Y` is added. |

The commutativity proof in `mappingPullback` is the evaluated naturality
identity of the existing internal-hom transformation, with the required
symmetry. This is structural data for the canonical map. Definitions have real
data; the sole postponed theorem is `reedy_cartesian_simplicial`, with proof
exactly `sorry`. Its docstring carries each of the seven proof steps, including
the other-factor symmetry and the empty zero-dimensional boundary. Every
declaration has the source and the correct blueprint marker. No new definition
nodes or dependency repair modules are delivered, and no correction or citer
audit is required. Repair-note files for the item and its two statement
dependencies are absent.

Edge cases: the first conjunct includes outer and inner degree zero; the
degree-zero latching colimit is empty. All spaces may be empty, including the
domains of the two pushout-product inputs. Identity and isomorphism maps are
included. Either weak-equivalence disjunct can hold independently of the other.
The mapping axiom includes arbitrary Reedy fibrations with nonfibrant bases;
its triviality includes boundary degree zero. There is no ring, characteristic,
scheme or index-family hypothesis to check. `u` is arbitrary; the small simplex
indices impose no dimension or cardinal bound on the simplicial sets. All
variables and universes are explicitly bound under `autoImplicit false`.

Independent H4 searches, made with different terms from the worker:

- LeanFinder via `msearch.py`: `Leibniz tensor of bisimplicial monomorphisms is
  a weak equivalence if either input is levelwise weak equivalence`. Eight
  ordinary model-category and simplicial-set hits; no exact theorem.
- Loogle via `msearch.py`: `MonoidalClosed.pre`. The service reported the
  identifier unknown. I read that existing construction in the imported
  closed-structure API instead; this result is not claimed as a match.
- LeanSearch via `msearch.py`: `simplicial enrichment of functors from the
  opposite simplex category to simplicial sets evaluated at zero internal hom`.
  This returned `SimplicialCategory.sHom` and the simplicial-object enrichment.
  I opened `SimplicialCategory/SimplicialObject.lean`, `Basic.lean` and
  `Functor/FunctorHom.lean`: on `A` and `X` themselves this enrichment varies
  the outer representable and is not the inner enrichment of the node. After
  flipping directions it can present the same mapping space, but supplies no
  theorem in this node; the present helper already uses the existing
  cartesian internal hom rather than implementing another exponential.
- Mathlib grep via `msearch.py`: `pushoutProduct|mappingSpace|Reedy` in
  `AlgebraicTopology`. It found ordinary simplicial-set pushout-product
  machinery and Reedy categories; the Reedy basic file still lists the
  diagram model structure as a TODO. I opened the exact anodyne
  pushout-product signature and the monoidal `Arrow.pushoutProduct` definition.
- Direct `rg` in Mathlib, upstream `WeilConjectures/`, project `lean/Sheaf/`
  and the upstream name index found no existing delivered names or theorem.
  Nearby project `Enhanced.mappingSpace` and `SegalSpace.mappingSpace` are
  vertex-to-vertex mapping spaces inside a quasi-category/Segal space, not
  mappings between two simplicial spaces. The reusable foundational definitions
  in `SegalCartesianExponent` are imported unchanged.

No mathematical or interface mismatch was found; I changed only this report.
In particular I checked the worker's import-plan observation: the imported
Segal module contains the shared definitions but no import of this module, so
the present import graph is acyclic. Its downstream theorem is not used. A
later stage-3 import reorganization, if needed, must retain these same shared
definitions rather than duplicate them.

Validation: `scompile.py Q14 lem-coef-simplicial-space-reedy-cartesian` compiled
the delivered file cleanly in both sandbox and library modes. A direct text
check confirmed that `lean.statement` equals the theorem signature verbatim,
all Lean lines meet 100 columns, and there is exactly one `sorry` theorem.
