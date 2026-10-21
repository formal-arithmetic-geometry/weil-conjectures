# Stage-1 delivery: lem-sfb-coefficient-mate-diagonal-graph

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-sfb-coefficient-mate-diagonal-graph.json`: existing statement, now split into four steps. Statement and statement dependencies unchanged; no exact Mathlib match.
- `citations.json`: eight step/node citations with verbatim extracts from the statements actually used.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by the prescribed search tool; `write_split.py` is a sandbox-only writing script.

New nodes: 0. Mathlib leaves: 0. No Lean files, library, unit records, chapter records, launcher files or repository files were written. No compiler or Lake tool was run.

## Attachments

No attachment for this item. The project-wide search for its exact blueprint tag returned no declaration. The concept searches found `AlgebraicGeometry.ProEtale.condensedPushforwardHom_comp`, in `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean:653`, and its uses in `UpperLowerStar`. Reading lines 599–663 shows the coefficient morphism and its general composition identity, but no diagonal/graph evaluation or the geometric clause. That composition declaration already belongs to `lem-sfb-eta-comp`; it is reused through that node, not claimed as a proof of this item. The other graph hits concern torsors or dual-number coefficients and do not state this item.

## WANTED

None. The current blueprint and every source needed for this elementary specialization are available locally.

## Corrections and scope

The supplied item had no proof. Its statement is well-typed and true with the comparisons it explicitly fixes, so it has not been changed and no statement dispute is needed. The main point needing care is the direction of restriction: if the scheme comparison is e from the iterated fibre product Q to the single fibre product R, its forward map on sections from sections on Q to sections on R is restriction along the inverse of e. The split makes this explicit and computes the base-changed diagonal as a scheme morphism, using projection equalities rather than an argument about point sets.

The only additional proof dependency beyond those already in the statement is `def-sfb-finite-lower-star`, which specifies pushforward on both sections and arrows. Every existing statement dependency remains used by the unchanged statement. No old proof dependencies or imports are removed.

## Blueprint, DAG and Mathlib searches

Read the current `main-20261015` chapter and constructible unit, their DAG records, the source of `lem-sfb-eta-comp`, and its four-paragraph proof. The closest ancestor is `det-def-sfb-constructible-local-model`; this item's existing `blueprint.from` already specifies the nonconstant-section localization argument and is retained. The four steps supply precisely the local diagonal/graph calculation needed by that argument. No chapter or unit route changes.

The whole-blueprint searches included `python3 tools/blueprint_refs.py search coefficient diagonal`, `search mate graph`, `search 'coefficient mate diagonal graph'`, and `search 'lem-sfb-eta-comp'`; the last identifies the composition theorem already reused. Whole-DAG searches included the exact item id and title, base-changed diagonal, graph evaluation, and coefficient-mate terminology. I opened `lem-sfb-localized-ring-mate-graph-evaluation`: it gives graph evaluation for a single mate under an inverse-image/restriction identification, and does not state this composition calculation. The torsor graph-evaluation and normalized-evaluation nodes concern equivariant or locally constant functions on finite étale torsors and do not state this result. The localization parent is a consumer and is not cited, avoiding a dependency cycle. `blueprint.same_as` remains empty.

The prescribed msearch command ran LeanSearch, Loogle, grep and two distinct LeanFinder phrasings; all five results were read and are recorded with their exact queries. The item's five pre-existing search records are preserved as inherited records, without representing them as new searches by N7. Loogle's `CategoryTheory.NatTrans.naturality` is the definition of naturality, not the full coefficient result. LeanSearch's pushforward composition and `SheafOfModules` hits concern generic continuous-functor comparisons or a different module framework. The grep hits include `CategoryTheory.Sheaf.pushforwardOverMapIso` (`Mathlib/CategoryTheory/Sites/Over.lean:520`) and `CategoryTheory.Limits.pullback.diagonal_comp` (`Mathlib/CategoryTheory/Limits/Shapes/Diagonal.lean:297`); I read their statements at those locations. The former is a slice restriction comparison and the latter is an identity between categorical diagonals, neither a coefficient-mate identity. The second LeanFinder phrasing returns global-section restriction and Zariski structure-sheaf naturality, likewise not the item. Hence this is a split using the existing coefficient composition theorem, not a Mathlib leaf.

## Not duplicates

There are no new nodes, hence no new/existing pairs to justify. Naturality, the projection calculation and functorial restriction are steps of the item's proof, not separately created nodes. No clause of the item is relabelled as a new lemma.

## Review by N7

I checked delivery-errors B–E with the item, all cited statements and the current source open. I read `lem-sfb-eta-comp.proof.md` (paragraphs 1, 3, 4) for the comparison convention and then the current DAG statement of `lem-sfb-eta-comp`, whose explicit normalization fixes the inverse conjugate comparison. I also read the source files and DAG statements of `def-sfb-finite-lower-star-comp`, `def-sfb-finite-lower-star` and `def-sfb-eta`. The unchanged statement's coefficient and site notions were checked against `sk-def-sfb-condensed-ring`, `sk-def-sfb-pulled-back-coefficients`, `sk-def-sfb-coefficient-morphisms` and `def-weil-pbc-proetale-site`. There are no new statements requiring an independent source or Mathlib search.

Step 1 uses the stated base-change functor from `def-sfb-finite-lower-star`, the specified canonical iterated-fibre-product comparison from `def-sfb-finite-lower-star-comp`, and the description of site morphisms as base-scheme morphisms from `def-weil-pbc-proetale-site`. These statements actually provide the functor and comparison used; no inverse-image/restriction equivalence is taken from a definition. I verified the inverse comparison by its projections: inserting h(z) as the middle coordinate makes a valid triple because w = u composed with h, and the two composites have identity projections. Pulling back the diagonal gives the triple (h(z), h(z), z), whose image under the comparison is the graph. This universal-property calculation applies to scheme morphisms, including nonreduced schemes, rather than only their points. It is elementary and not a hidden geometrical lemma.

Step 2 uses the exact displayed statement of `lem-sfb-eta-comp` with f = h and g = u. Its hypotheses are arbitrary scheme morphisms and a condensed ring; the item's commutative ring is a special case, and it explicitly fixes the same normalization. `def-sfb-finite-lower-star` really states that pushforward is restriction along base change and evaluates on T by sections over the fibre product, so evaluating u_* eta_h at V gives eta_h at P. `def-sfb-finite-lower-star-comp` really specifies restriction along the canonical scheme isomorphism; typing the component from sections on Q to sections on R forces its inverse as the restriction arrow. The composition identity therefore has precisely the orientation used. I marked this step non-elementary because it invokes the existing coefficient composition theorem, rather than proving it again. The cross-unit coherence theorem is declared as a generic tool in `split_report.tool_uses` for maintainer review.

Step 3 uses `def-sfb-eta` only for what it states: eta_h is a morphism of abelian sheaves. Naturality with respect to the diagonal is part of being that morphism, not a separate theorem. The pushforward definition identifies the bottom restriction in that naturality square with restriction along the base change of the diagonal. Its target before identification is sections over V times_V W; the canonical isomorphism with W is the same one used in step 1. The diagonal is a morphism over V because the second projection composed with it is the identity. I wrote the naturality equation and both section spaces explicitly, so no ringed localization comparison or unstated coefficient compatibility is assumed. This step is elementary unpacking of those two definitions.

Step 4 uses the already established equations and the contravariant composition law of the sheaf: restricting first along the inverse comparison and then the graph is restriction along their composite, which step 1 identifies with the pulled-back diagonal. Substituting step 3 and the definition of a gives the asserted formula for every s. No new fact is cited or concealed in this substitution. Each cited node in steps 1–3 has a verbatim quote in `citations.json`, and `proof_deps` is exactly their union. No step exceeds 2000 characters.

For edge cases I checked h the identity (both diagonal restrictions coincide), u the identity (P identifies with V and the remaining restriction is ordinary naturality), and W empty (all equalities remain in the final-object section ring). For a nonmonomorphic example take B a point, V the disjoint union of two points, W the disjoint union of two copies of V, and h the fold map. Then Q consists of triples with second coordinate h(z), the comparison forgets exactly that middle coordinate, and the pulled-back diagonal and graph still match. With discrete coefficients a section on V can take two distinct values; the calculation is still valid without a constant-section hypothesis. The proof never replaces V times_B V by V, never assumes u or h monic, and imposes no finiteness or connectedness hypothesis. No false statement, missing hypothesis or source correction was found.

## Dry-run repair

The first dry run rejected the eight-word extract for the site-morphism definition as too short for its minimum-length gate. I replaced it with the full unchanged statement and also expanded the pushforward and eta extracts to their full statements, so their section formulas and sheaf categories are visible to the reviewer. The second dry run also rejected the phrase referring to the item in step 2 under its self-containedness check. I replaced that phrase by the explicit hypothesis that Lambda is a commutative condensed ring and the explicit normalization reference. The mathematics and dependencies did not change.

## Unfinished work

None at stage 1. The required dry run and push are performed after this report is written; their terminal outcomes are reported by the delivery command.
