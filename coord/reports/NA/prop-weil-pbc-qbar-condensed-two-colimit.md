# Stage-1 cycle repair: prop-weil-pbc-qbar-condensed-two-colimit

## Files written

- `dag/nodes/sec-proper-base-change/prop-weil-pbc-qbar-condensed-two-colimit.json`: existing statement unchanged; seven assembly steps, 2726 characters of proof text.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-coherent-cocone-normalization.json`: new statement-only lemma, status unsplit, no Mathlib match. It isolates the normalization and representative-compatibility argument.
- `citations.json`: 21 literal quotations, one for every step/cited-node pair.

The retained searches.jsonl is unchanged. The earlier report and removed uncommitted bounded-Hom helper are preserved outside dag/nodes as report-before-cycle-repair.md and bounded-hom-helper-before-duplicate-removal.json; they are historical working records, not delivery nodes.

## Attachments

None. The live source theorem AlgebraicGeometry.ProEtale.constructibleCocone_isFilteredTwoColimit (TwoColimit.lean:258) assembles the three descent inputs at lines 234, 241 and 248, all with sorry. The scalar-preservation inputs at lines 165 and 175 are also sorry. This is not a completed attachment. The explicit human re-split instruction applies despite the existing reviewed stage-1 split.

## Literature

WANTED: literature/upstream-master-20261014/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean, the historical source named by the inherited item. This archive is unavailable here. I read the corresponding entire live module under lean/WeilConjectures, including the (Obj)/(Hom) docstring and exact scalar, cocone and descent declarations; the proof origin and steps name this accessible source.

I read the current main-20261015 thm-weil-pbc-qbar statement and proof: the latter explicitly uses the common-stage colimit and independence of representatives. I read the actual current blueprint filtered-two-colimit model and characterization, and the current DAG cocone and three-conditions statements. The new normalization lemma is an agent formulation that supplies the model's strict normalization hypotheses, not a theorem alleged to have been proved in that document. No SGA source is used.

## Repair of the numbered return

The return L reports a 17-node dependency cycle and requires a rebase, rereading changed citations, adjustment and delivery. I first ran the retained complete sandbox through the mandated dry run: it passed on the current server at a7ada37b9f9. This does not by itself constitute the repair. I then rebased the parent JSON on the current read clone, preserving its statement, statement dependencies, source, review/import/Lean metadata (including its current empty lean_audit), and adjusted its split as follows.

The current DAG now contains lem-sfb-condensed-bounded-hom-continuity. Its statement is the retained new bounded-Hom lemma's result, for exactly the same finite condensed field, topologically Noetherian scheme, bounded constructible first argument and uniformly termwise bounded-below diagram. A complex-colimit cocone is identified with the termwise one by its universal isomorphism commuting with the legs. I therefore dropped the uncommitted duplicate lem-weil-pbc-condensed-bounded-hom-colimit instead of delivering a second copy.

Crucially, I did not replace it by a citation of that existing lemma. Reading its current dependencies exposed precisely the dangerous return path:
lem-sfb-condensed-bounded-hom-continuity -> det-lem-constructible-ext-continuity-devissage -> det-cor-coefficient-heart-ii-generation -> sk-lem-coefficient-heart -> sk-prop-sfb-cartesian-coefficients -> sk-def-sp-tate-twist -> det-def-sp-tate-twist-locally-free -> lem-poincare-compatible-primitive-roots -> def-pur-condensed-tate-twists -> this item.
Such a citation would recreate the returned cycle. I retained the current parent's direct Hom-property argument from sheaf continuity, the same-unit hom-colimit-extension lemma and bounded module devissage. Their current closures do not return to this item. I reread every statement used by the seven parent steps and rebuilt every quotation from the current statements, rather than importing facts from their proofs. No other worker's node was changed.

The remaining new normalization lemma extracts an independent argument from the old final step. Thus this is a genuine finer split, not an unchanged repush or a shorter paraphrase. Its future worker must establish the transported coherence equations, strict units, and preservation of the three descent properties and representative images. The parent continues to carry the old scalar preservation, final field tail, coefficient presentation, sheaf-to-bounded Hom devissage, adjunction comparison, object devissage and derived faithfulness arguments. Every old argument is either still explicit in the parent or assigned to this new statement-only helper. The total parent proof is 2726 characters; no step exceeds 2000.

## Mathlib and blueprint searches

I read and retained the actual search results in searches.jsonl. The normalization helper already has LeanSearch, Loogle, LeanFinder, grep and a second semantic phrasing. I did not invent or repeat queries. The results concern ordinary cocones, free bicategory/monoidal normalization and pseudofunctor constructors. I read Mathlib/CategoryTheory/Bicategory/Coherence.lean:213 (free bicategory normalization) and CategoryTheory/Bicategory/Functor/LocallyDiscrete.lean:165 (mkPseudofunctor). Neither normalizes a supplied arbitrary unital category cocone while preserving its vertex comparison formula. Hence the new helper remains unsplit, not a Mathlib leaf. I also read the retained Hom-search results and Condensed/AB.lean:25-70; AB5 is exactness of filtered colimits, not the removed helper's continuity result.

I repeated whole-DAG keyword inspection and blueprint_refs searches for normalized cocone and bounded constructible first, and the ancestor query. The ancestor remains thm-weil-pbc-qbar; there is no blueprint normalization theorem. Both the item's and helper's blueprint fields identify the current common-stage/representative-independence paragraphs, and same_as is empty.

## Not duplicates

lem-weil-pbc-coherent-cocone-normalization vs det-def-sfb-filtered-two-colimit-model: the existing model assumes strict identity transitions and normalized comparisons; the new lemma constructs them from non-strict unit isomorphisms and identifies representative images.

lem-weil-pbc-coherent-cocone-normalization vs det-def-sfb-filtered-two-colimit-characterization: the existing characterization assumes the normalized model; it does not normalize an arbitrary unital cocone.

lem-weil-pbc-coherent-cocone-normalization vs det-def-sfb-filtered-two-colimit-cocone: that definition explicitly imposes no coherence and provides no normalization theorem.

lem-weil-pbc-coherent-cocone-normalization vs lem-sfb-flat-scalar-tower-coherence: the latter supplies coherent tensor comparisons, including derived comparisons, but does not replace identity transitions by literal identity functors or prove preservation of descent conditions.

Removed draft lem-weil-pbc-condensed-bounded-hom-colimit vs lem-sfb-condensed-bounded-hom-continuity: these are duplicates after the canonical identification of complex colimit cocones with termwise cocones; the draft is not delivered. The existing lemma is not cited because of the return path displayed above.

## Review by NA

I read delivery-errors B through E in full, including both copies, GOAL.md, the three levels in SETUP.md, the worker/stage instructions, and the proper-base-change chapter and unit. The target statement and unit route are unchanged. Only sandbox JSON and reports were written; no Lean or build command was run.

For the item I checked the live TwoColimit source against the statement: prime ell, topologically Noetherian scheme, finite-subfield-valued continuous functions for condensed Omega, no completeness condition, and all three descent assertions agree. Its final assembly does not remove its sorried inputs. The parent statement remains byte-identical to current main.

For the new normalization statement I read its actual model source and the cocone, conditions and characterization statements. I checked theta has direction Phi_j T_ij -> Phi_i, tau has direction T_jk T_ij -> T_ik, and beta has direction T'_ij -> T_ij. Thus beta_ik inverse after tau after T_jk(beta_ij) after beta_jk(T'_ij) is well typed. The stage-arrow identification is beta_jk inverse composed with g composed with beta_ik. Substitution into theta' cancels the two beta factors, leaving exactly the old vertex image. Conjugation transports the pentagon and cocone identities; unit equations give strict identity comparisons. The partial-order hypothesis ensures a chain returning to an identical index has no distinct intermediate index. This is a separate coherence argument, neither an elementary new node nor a clause restating the parent.

Step 1 uses the flat coefficient calculus for exact scalar functors, termwise derived computation and coherent tensor comparisons; exactness preserves finite limits in the abelian category, meeting the scalar-preservation lemma's hypothesis. The finite-model API is used only for its explicitly stated finite-field triangulation.

Step 2 uses directed finite fields and the coefficient-complex presentation. The tail above EF is small in the stated universes, directed and final: GEF bounds every finite G, and composita bound pairs. Bounded L is bounded below, so the presentation supplies the common lower bound, cocone, named isomorphisms and compatibility equation, with exactly these coefficient rings.

Step 3 applies sheaf-ext-continuity to that common termwise bound and the topologically Noetherian scheme. The arbitrary cocone is identified with the termwise colimit by its universal isomorphism, preserving all legs. The hom-colimit-property definition gives precisely the comparison for all shifts. Isomorphisms, zero and shifts preserve it directly; hom-colimit-extension supplies extension closure, and rotation gives cone closure. The existing bounded-devissage statement applies: its ring-object constructibility is the same stratified local finite-presentation condition, not an identification with constant lisse models. The directed abelian-group-colimit statement explicitly supplies a stage representative at shift zero. No coefficient-heart generation or Tate-twist result enters this step.

Step 4 uses the presentation's actual compatibility equation and the fixed adjunction/tensor data. Transpose the Omega arrow, factor it at a finite stage, transpose back there, and use the equation to identify its Omega adjunct with the original one. Injectivity of the adjunction bijection gives the original arrow. The subcategories are full and scalar extension preserves their objects by step 1.

Step 5 uses directed-triangulated-image with the Hom-surjectivity just proved and the triangulated finite categories and functors from step 1. Its essential-image property is replete by definition. Finite-presentation descent gives a single finite model M_E; exact termwise tensor identifies its degree-zero image with M[0]. Bounded module devissage then supplies every bounded constructible object. All hypotheses match the current statements.

Step 6 uses the explicitly stated derived faithfulness on the whole unbounded category for the same finite-subfield-valued Omega. Equal Omega images imply equality already over H, so H itself is the required later stage. This is faithfulness, not an unjustified inference from conservativity.

Step 7 applies the new normalization helper to the canonical unit and tensor-pentagon comparisons from scalar calculus. It preserves the three established descent properties and the images of finite-stage arrows. Only then are the model and characterization used to give the stated pair-category equivalence. The helper supplies the theorem missing from the model's definition. Generic off-unit devissage/model/characterization tools remain declared in split_report.tool_uses.

Small cases: normalization for a singleton poset gives beta_ii = epsilon_i inverse and theta'_ii = identity; repeated-index triples reduce to the two unit equations, while strict chains leave transitions unchanged. The two inverse beta conjugations preserve identity arrows and equal arrows. Zero complexes, the empty scheme and singleton coefficient tails cause no extra condition in the parent assembly. Every new statement is self-contained, with its own universes, hypotheses, source, definitions and actual searches; it has empty proof and proof_deps. All 21 quotes were regenerated verbatim from the current cited statements.

## What could not be finished

Nothing remains in the assigned stage-1 repair apart from the required final server dry run and push. The one new helper is intentionally statement-only for subsequent workers. No statement dispute or target change is involved. The historical source archive remains unavailable, with the accessible live source read instead. The earlier complete report and search log are retained as noted above.

## Final dry-run formatting repair

The first dry run after the cycle repair rejected the literal shift index [n-m] as an apparent node id and warned about a plain-text arrow. I wrote the same shifted-Hom identity in TeX with spaced indices and the morphism in TeX. No mathematical claim or dependency changed. The parent now has 2726 proof-text characters.
