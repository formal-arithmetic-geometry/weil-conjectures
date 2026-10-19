## Worker report

The item is stated in `lean/Sheaf/AlgebraicTopology/TwoObjectLocalizationPullback.lean`,
namespace `SSet.Bergner`. There are two postponed theorems in this delivery, each
with its own existing DAG node and source/proof docstring. All other declarations
are concrete definitions or structures. No source or natural-language statement
was changed, and no definition node was added. The supplied groupoid-completion
prerequisite is also added to stmt_deps because its completion interface occurs
in the Lean signature, as the human's bottom-up instructions require.

The original quantification over chosen replacements, completion maps,
factorizations and pullbacks is retained universally. The conclusion first
constructs the equivalence subcategory and the prescribed walking-arrow maps;
for every stipulated choice it then asserts the canonical factorization and the
four weak-contractibility conclusions. Choosing a pullback by its universal
property rather than by equality of its carrier admits every concrete degreewise
pullback and its canonical isomorphic copies.

Clause-by-clause rendering:

| Node clause or hypothesis | Lean rendering |
| --- | --- |
| Simplicial sets, maps and simplicial operators | Existing `SSet.{u}` and natural transformations; `_⦋0⦌` means vertices. |
| Two distinct labelled objects x,y | Existing `Two.{u} = ULift Bool`, with `ULift.up false` and `ULift.up true`. |
| Simplicial categories, associative composition, units | Existing `Fixed Two.{u} = EnrichedCategory SSet Two`, with `Hom`, `comp`, `id` and the enrichment laws. |
| Functors fix the labels | Existing `FixedHom`/`fixedCategory`; all arrows in the file are in that category. |
| Component category and homotopy equivalence | Existing `IsEquivalenceVertex E₀ e`, whose two inverse equations use `SSet.π₀`; that quotient is the edge-zigzag presentation of realized path components. It imposes no Kan hypothesis. |
| Given E' and prescribed equivalence e | The binders `E₀`, `e`, `he`. |
| Subsets whose every vertex is a homotopy equivalence | `IsHomotopyEquivalenceSubcategory E E₀ j` identifies each mapping set, over its ambient inclusion, with `Enhanced.fullSubcomplex ... (IsEquivalenceVertex E₀)`. |
| Composition and identities restrict | `E : Fixed Two` and `j : E ⟶ E₀` already include the composition/unit laws and preservation by the inclusion. No arbitrary map replaces the inclusion. |
| e belongs to E(x,y) and F → E sends its arrow to e | `f`, `f₀`, the equation `f ≫ j = f₀`, and the displayed equation for the forward vertex of `f₀`. Together these say the vertex of `f` is a lift of precisely e. |
| Discrete walking arrow F | Existing `U (𝟙_ SSet.{u})`, whose forward mapping set is the point and reverse mapping set is empty. |
| Mappingwise model structure and cofibrant replacements | `FixedCofibrantReplacement`: a functor `Q`, natural counit, cofibrancy of every `Q.obj A` via `fixedCofibrations (discreteInclusion ...)`, and mappingwise weak equivalence of its counit (maintainer review: the former extra Kan-fibration field was removed). These are the ordinary cofibrant replacement conditions in the sorted mappingwise model. |
| Replacement of F is an isomorphism | `rF` and `rF.hom = R.counit.app F`. It is the replacement map itself that is invertible. |
| Naturality gives F → Q(E) | Real definition `replacedWalkingArrow f R rF = rF.inv ≫ R.Q.map f`; naturality is part of the counit. |
| Degreewise groupoid completions | `CF`, `CE : DegreewiseGroupoidCompletion ...`, with actual target and unit plus existing `IsDegreewiseLocalization` at all arrows in every degree. This uniquely characterizes formal-word completion; no unknown object is chosen. |
| Induced functor on completions | `r` with `CF.unit ≫ r = R.Q.map f ≫ CE.unit`. The strict degreewise universal property uniquely determines it. |
| Factorization through Z | Binders `Z`, `i`, `p`, equality `i ≫ p = r`, and hypotheses `fixedWeakEquivalences i`, `fixedCofibrations i`, `fixedFibrations p`. In particular the first leg is both a cofibration and a weak equivalence. |
| G is the mappingwise simplicial pullback | `IsMappingwisePullback CE.unit p gE gZ`, including the enriched square and mappingwise isomorphisms to Mathlib's actual simplicial pullbacks, commuting with both projections. |
| Compatible F maps induce F → G | Existential `hG` with `hG ≫ gE = replacedWalkingArrow ...` and `hG ≫ gZ = rF.inv ≫ CF.unit ≫ i`. These characterize the induced map uniquely by the pullback. |
| The factorization recovers prescribed F → E' | `hG ≫ gE ≫ R.counit.app E ≫ j = f₀`. |
| All four mapping simplicial sets of G are weakly contractible | `∀ a b : Two, Enhanced.IsContractible (G.Hom a b)`. This is exactly weak equivalence to Δ⁰, including nonempty connected components, and imposes no local Kan condition. |

Dependency declarations read and used:

- Mathlib `AlgebraicTopology.SimplicialSet.Basic`, `Degenerate`, `Subcomplex`, `Finite`:
  the complete recorded `def-weil-pbc-simplicial-set` interface was inspected; the
  statement uses `SSet` and the subcomplex interface, and makes no finiteness assumption.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `fullSubcomplex`, `IsContractible`,
  `IsWeakHomotopyEquivalence`, and their realization/component/homotopy-group definitions.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`: `right_proper_kan_quillen` and
  its realization-based weak equivalences, with fibrations exactly horn lifting.
- `Sheaf.AlgebraicTopology.SortedSimplicialAlgebraModel`: `SortedTheory`,
  `StrictSimplicialAlgebra`, `evaluation`, `sorted_simplicial_algebra_model`; the
  same fixed-object model's classes are the already published `fixed*` definitions.
- `Sheaf.AlgebraicTopology.SimplicialIntervalLifting`: only its foundational
  `Fixed`, `FixedHom`, `Two`, `U`, `IsEquivalenceVertex`, `fixedWeakEquivalences`,
  `fixedFibrations`, `fixedCofibrations`, `discreteInclusion` declarations are used.
  Its downstream interval-lifting theorem is not an input to this theorem.
- `Sheaf.CategoryTheory.CofibrantSimplicialInversion`: only `Degree`,
  `degreeCategory`, `degreeFunctor`, `IsDegreewiseLocalization` (and the existing
  `bundle`/`bundleMap`) supply the already recorded degreewise localization notion.
  Its downstream inversion theorem and its `Nonempty Statement` are never used or chosen from.
- The existing proof prerequisite `lem-coef-cofibrant-homotopy-groupoid-completion`
  had no Lean record; its module is supplied in this delivery. Its theorem is the
  mathematical Step 3 of this item's six-step proof.

The two imports from downstream modules above reuse definitions only. As with
other already landed definition-only uses in this family, the DAG's proof route
is not changed into a circular appeal to those downstream theorems. No import
cycle is introduced by these files.

Edge cases checked before finalizing: arbitrary universe u, even u=0; e has the
specified distinct labels but its image may be an identity under a later functor;
no local Kan hypothesis on E₀, E, Q(E), Z or G; no countability/cofibrancy condition
on G; repeated labels a=b in both endomorphism mapping sets are included; the
walking arrow has an empty reverse mapping set before completion and a point
after completion; the completion comparison dependency allows O empty, disconnected
component categories and empty off-diagonal mapping sets. An empty E₀(x,y) simply
has no specified vertex e, as in the node. The replacement functor is arbitrary
subject to the stated normalization at F, not globally normalized on other objects.

Searches (all via the prescribed msearch wrapper or read-only rg):

- LeanFinder: `two object simplicial category homotopy equivalence mapping spaces contractible`:
  eight hits on truncated homotopy categories/terminal nerves; no enriched pullback match.
- Loogle: `SimplicialCategory,EnrichedOrdinaryCategory,Localization`: zero hits;
  index reports unknown `SimplicialCategory`. The actual declaration was inspected locally.
- Mathlib grep: `groupoid.?completion|SimplicialCategory` in CategoryTheory:
  two references to simplicial enrichment, no theorem matching this item.
- LeanSearch: `A cofibrant simplicial category with invertible homotopy category has mappingwise weak equivalence to its groupoid completion`:
  eight generic cofibrant homotopy-category/Quillen hits; no exact statement.
- Mathlib grep: `DegreewiseGroupoidCompletion|IsMappingwisePullback|FixedCofibrantReplacement|homotopy_groupoid_completion`
  in AlgebraicTopology: zero hits.
- `rg` of simplicial categories, walking arrows, groupoid completion and cofibrant
  replacement in the upstream WeilConjectures source and published `lean/Sheaf`
  found the reusable fixed-object and degreewise-localization interfaces above.
  None states the item or the local groupoid-completion comparison.
- Exact item-id/name searches in upstream WeilConjectures, published `lean/Sheaf`
  and `dag/lean_names_upstream.json` find only CountableEquivalenceWitness's proof
  citation of this item, not a declaration implementing it.

Sources opened: Bergner https://arxiv.org/pdf/math/0406507, Section 4, pp. 13–14,
and Dwyer–Kan https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf,
Section 9, especially Proposition 9.5 and its proof. The factorization explicitly
retains Z, rather than assuming the original localization map is a fibration.
No statement dispute or source correction was needed.

Validation: both delivered files compiled individually, in dependency order,
through `scompile.py`, with no errors or warnings. The initial `deliver2.py --no-push`
printed `OK (dry run)` for commit `17d4d9cf95`: compile and preflight passed except
for the independent second reading, which belongs to the next worker. A final
dry run checks the added stmt_deps entry as well. Nothing was pushed.

## Dependency modules

`lem-coef-cofibrant-homotopy-groupoid-completion` is an existing genuine DAG node
and a proof prerequisite of this item, but has neither a `lean` record nor a
`mathlib_match` in the shared snapshot. The human's 2026-10-16 bottom-up guidance
authorizes stating such a prerequisite in the same delivery. Its module
`Sheaf.AlgebraicTopology.CofibrantHomotopyGroupoidCompletion` states exactly its
cofibrant, component-groupoid, mappingwise-completion assertion, retaining empty
object/mapping cases and no Kan hypothesis. `DegreewiseGroupoidCompletion` packages
actual data with the existing strict universal property, rather than choosing
unspecified data or supplying a mere arbitrary map. The dependency node changes
only in `lean`, with an explanatory `lean.note`.

## Second reading by Q55

I independently compared the node statement, its source description (Bergner, Lemma 4.1 and the construction preceding Lemma 4.2, pp. 13--14), and both delivered modules. The item introduces: a fixed two-object simplicial category `E₀`; the labelled degree-zero arrow `e` and its `IsEquivalenceVertex` hypothesis; witnesses `f₀`, `E`, `j`, and `f`; an arbitrary fixed-object functorial cofibrant replacement `R` and an isomorphism `rF` satisfying the counit equation; degreewise completions `CF` and `CE` and a comparison `r`; a factorization through `Z` with `i` a mappingwise weak equivalence and cofibration and `p` a mappingwise fibration; and a mappingwise pullback object `G` with projections `gE`, `gZ`. The conclusion has the node's clauses in order: `f₀` sends the walking arrow to `e`; `E` is the homotopy-equivalence subcategory and `f` restricts to `f₀`; completion compatibility; `i ≫ p = r` and the three stipulated mappingwise properties; the pullback condition; an induced `hG` with both projection equations and recovery of `f₀`; and weak contractibility of all four mapping simplicial sets.

The Lean renders these exactly. `Fixed`, `Two`, `U`, and `IsEquivalenceVertex` are the recorded upstream definitions. `IsHomotopyEquivalenceSubcategory` uses a mappingwise isomorphism onto `Enhanced.fullSubcomplex` on precisely the vertices satisfying `IsEquivalenceVertex`, together with the inclusion equation. `FixedCofibrantReplacement` records cofibrancy, weak equivalence, and fibration of every counit component; `replacedWalkingArrow` is the naturality map `rF.inv ≫ R.Q.map f`. `DegreewiseGroupoidCompletion` and its `unit` are the dependency module's strict localization interface. `IsMappingwisePullback` includes the enriched commutative square and a mappingwise isomorphism to the actual simplicial pullback, commuting with both projections. The theorem's nested universal quantifiers preserve every choice and every implication from the node, and the final `∀ a b : Two, Enhanced.IsContractible (G.Hom a b)` gives all four clauses, including the repeated-label endomorphism cases.

I found no mismatch and made no semantic edits. In particular, no Kan, Noetherian, finiteness, countability, connectedness, or extra universe hypothesis was added; the single universe `u` covers `u = 0`. Empty object or mapping sets, the empty reverse mapping of the walking arrow before completion, identity arrows, and the case where the chosen equivalence maps to an identity are all admitted. The dependency module `lem-coef-cofibrant-homotopy-groupoid-completion` is included because the shared node had no usable Lean record; its `DegreewiseGroupoidCompletion` has concrete data and the theorem states the recorded mappingwise comparison, with no hollow definition. Its node record changes only the authorized `lean` field and note.

The three-kind existing-definition searches in the worker report were checked (LeanSearch/LeanFinder, Loogle, and repository/Mathlib grep); they found no duplicate statement or notion. Both modules compile separately through `scompile.py` with no diagnostics. The delivery dry run was then rerun after this report update.

Independent second-reader searches used different queries from the first worker: LeanFinder `Simplicial enriched two point category contractible hom objects pullback groupoid inversion` returned eight unrelated simplicial-enrichment/truncated-homotopy-category hits; Loogle `CategoryTheory.Localization, CategoryTheory.Groupoid` returned no hit (unknown first identifier); LeanSearch `The local mapping complexes of a cofibrant enriched homotopy groupoid are equivalent to those of its groupoid of fractions` returned eight general model-category localization declarations. An independent `rg` search for `groupoid.?completion|localization.?pullback|contractible.*mapping|invertible.*component` in Mathlib AlgebraicTopology and CategoryTheory, upstream WeilConjectures and published Sheaf found the already reused completion interface and related ordinary nerve statements, and no exact replacement. I opened `SimplicialIntervalLifting` lines 40--110 and 283--288, `CofibrantSimplicialInversion` lines 43--91, and `EnhancedDiagramsCones` lines 50--102: the fixed-object maps, component inverse equations, lifting classes, strict localization property and realization-based weak contractibility all have the claimed meanings.

I also independently opened the actual online sources: [Bergner Section 4, pp. 13--14](https://arxiv.org/pdf/math/0406507) and [Dwyer--Kan Sections 7 and 9, especially Proposition 9.5 and its proof](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf). Their standing smallness and fixed-object conventions agree with the dependency signatures. Bergner's intermediate object Z is retained explicitly; no local fibrancy restriction is imported. Dwyer--Kan's if direction is exactly the supplied dependency theorem, whose proof docstring follows its augmented-nerve, quasifibration, and nerve-comparison argument. No new definition node or statement correction requires a citer audit. A direct normalized-text comparison confirmed each node's `lean.statement` equals its file's signature, and inspection found no unbound variables, universe binders, hollow data, private notation or extra proof.

## Maintainer review fix (2026-10-17)

`FixedCofibrantReplacement` no longer requires its counit to be a mappingwise Kan
fibration. The node only says "functorial cofibrant replacement" with the replacement
of F an isomorphism; the proof (steps 2--3) uses only cofibrancy of Q(E) and the
mappingwise weak equivalence Q(E) → E. The extra field narrowed the universally
quantified replacements and excluded the Dwyer--Kan standard resolution, the natural
functorial replacement whose value on the free walking arrow is the walking arrow
itself, so the citer lem-coef-countable-equivalence-witness might have had no
admissible R to instantiate. No other declaration or the recorded statement changes.

