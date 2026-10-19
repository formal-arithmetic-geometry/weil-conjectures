# det-finite-window-unbounded — Q54 stage-1 report

## Files written

- dag/nodes/sec-six-functors-basics/det-finite-window-unbounded.json — statement, split; no exact Mathlib match. Six proof steps follow the blueprint's Postnikov-tower route.
- citations.json — verbatim statement quotes for every citation in every proof step.
- report.md — author review and handoff.

There are **0 new nodes and 0 new Mathlib leaves**. The auxiliary prepare.py only writes these sandbox artifacts; searches.jsonl is the search command's genuine log.

## Attachments

None. Searches of WeilConjectures in /home/ubuntu/weil-src-slopmaster2 for the exact blueprint id, finite-window spellings, lower-tail spellings, and uniform-Ext concepts found no declaration of the item. The upstream master reference also has no exact-id or finite-window hit. Its sorry declarations were not treated as proofs. The closed generic homotopy-limit lemma IsHomotopyLimit.hom_ext_zero is only a tool under additional vanishing hypotheses, not this statement, and is not proposed as an attachment.

## WANTED

None. The current blueprint and the relevant Stacks source are locally present. No SGA source is used.

## Corrections and source audit

STATEMENT-DISPUTED: the imported standalone statement mentions d_C without binding or defining it, so it cannot be translated as a closed proposition on its own. The unit sk-lem-finite-window and sk-cor-ind-heart-ii explicitly take d_C from sk-lem-uniform-constructible-ext. The repair expands exactly what being a uniform bound means: vanishing against every constructible sheaf in degrees above d_C. The node does not assert existence of such a bound; existence remains the separate uniform-Ext theorem. Any bound supplied by that theorem is therefore valid input here. It also introduces X, the coefficient extension, the ambient derived module category, and the meanings of IndCons and Dic. The conclusion and cohomological cutoff are unchanged. No lower boundedness is imposed. The chosen Ext bound, rather than a further geometric assumption, is what the proof uses.

The item's imported proof uses several unit references absent from its uses lists. Moreover the shared DAG contains the detailed nodes, but not standalone nodes for sk-prop-pe-left-complete, sk-prop-pe-products, sk-cor-ind-heart-ii, or sk-cor-ambient-ind-derived. I use the detailed left-completeness and product nodes. For truncation stability I instead use the displayed cohomology formulas; for the two Ext vanishings I use the single-cohomology special cases of the bounded-tail theorem. These are the same layer vanishings as in the blueprint. The original first dependency on the weakly contractible basis is replaced by the actual left-completeness and product statements: the basis is used inside their proofs, not independently in this argument.

I read the current chapter _section.md and unit sk-lem-finite-window/_section.md and their unbounded proof paragraphs. This imported node has no chapter/unit binding fields; corresponding dag/chapters/sec-six-functors-basics.json and dag/units/sk-lem-finite-window.json do not exist in this snapshot. I have not created or altered maintainer metadata or unit records. The actual current chapter and unit source files give the route followed here. This is not the unit key node.

The blueprint itself supplies the agent-written proof. proof_origin remains by agent, now pointing to its actual .proof.md. The Stacks support was read in derived.tex: Tag 0149, lemma-representable-homological (with Tag 0146, lemma-composition-zero), and Tag 08J5, remark-truncation-distinguished-triangle. The latter explicitly gives the successive lower-truncation triangle and confirms the shift n+1 and resulting Ext exponents n, n+1. This is the existing unit's route, not an alternate compactness or Brown-representability argument.

## Mathlib and duplicate searches

Every Mathlib search was run through /home/ubuntu/weil-launcher-nt/msearch.py and is recorded verbatim in the item's mathlib_searches and searches.jsonl. Both semantic phrasings returned ordinary t-structure orthogonality or projective/injective-dimension results, not a theorem for the constructible relative Ext bound. In particular projectivity in the entire ambient module category is not assumed here. The Loogle queries returned unknown-identifier messages, which are recorded as returned, not presented as successful theorem matches. The two Mathlib grep queries returned truncation machinery and homology-sequence declarations only. LeanSearch returned cohomological-bound and single-injective-object results, also not matches.

I searched the whole DAG's statements for representable Hom exactness, for truncation triangles, for Dic and ind-constructibility, and for products/left completeness. This found the existing Mathlib leaf lem-weil-pbc-hom-into-triangle-exact, the generic truncation leaf lem-sf-derived-truncation-triangle, and the truncation definition def-kun-truncations. I read all their statements. Blueprint searches for finite window, Lower tail vanishing, cohomological, and truncation triangle found no additional node stating the item. The other lower-tail result is bounded, and the reduction node assumes this unbounded vanishing. Neither is an attachment or an interchangeable duplicate. No new node is created, so there are no same-tag new/existing pairs.

## Not duplicates

No new nodes.

## Review by Q54

I checked the split against delivery-errors B–E with the current .md statement, its full .proof.md, and the cited JSON statements open. There is no new unsplit node with a hidden proof, no elementary recursion packaged as a lemma, no new clause-restatement of the item, and no invented Mathlib record. The definition of Dic is written inline so it is not confused with the smaller localizing closure. Products are taken in the full ambient derived category, and are never asserted ind-constructible.

Step 1 uses det-pe-left-complete-iso for precisely the quasi-isomorphism to the explicit cone fibre, det-pe-products-derived for termwise products being derived products, and def-weil-abstract-derived-category for the cone triangle and inversion of quasi-isomorphisms. I checked that these are sheaves of rings, not only constant finite coefficients: Lambda_X is the pulled-back condensed coefficient ring object viewed as a sheaf of rings, as in the current chapter. Thus both E and Qlb use the layer-B module category throughout. The left-completeness node has no boundedness hypothesis.

Step 2 uses lem-weil-pbc-hom-into-triangle-exact, whose statement supplies both middle exactness and the adjacent rotated segment. This is the required representable-Hom result; the more generic lem-sp-long-exact-of-triangle by itself would require additionally proving Hom is homological. The product identifications are proved by the universal property, and shifts preserve products because they are equivalences. The coordinate expression for the map is written, so compatibility with the transition maps is not hidden. Only the displayed exact segment is used, with no unrecorded Milnor theorem.

Step 3 uses the literal truncation formulas in def-kun-truncations and the complete bounded-tail statement det-finite-window-bounded. Truncation stability follows directly because each retained cohomology object is unchanged and all other cohomology objects are zero; the zero sheaf is a filtered colimit of the constructible zero sheaf. The lower bound is -n, the upper bound is -d_C-1, and the same d_C is used. A product of these zero Hom groups is zero by its coordinate definition. No boundedness of the original L was slipped into this step.

Step 4 uses lem-sf-derived-truncation-triangle on L_(n+1) at b=-n, which is allowed for an arbitrary abelian category and an unbounded complex. I wrote the actual truncated complex identifying its first term with H^(-n-1)(L)[n+1]; this is an application of the kernel/cokernel formulas in def-kun-truncations, not a claim taken from another lemma's proof. After shifting by -1, the outer Hom groups are the Hom groups into B_n[n] and B_n[n+1]. Both are bounded complexes in Dic, with single ind-constructible cohomology sheaf B_n and degrees -n and -n-1. For n>d_C both degrees satisfy the cutoff -d_C-1. Thus the same det-finite-window-bounded applies twice. This is precisely the Ext^n and Ext^(n+1) vanishing from the source; no stronger ambient projectivity hypothesis is used. Representable Hom exactness again gives both injectivity and surjectivity of the middle transition.

Step 5 is elementary and complete: choose N=d_C+1, use inverse transition homomorphisms to recurse forward on the tail, then recurse backward across the finite initial segment. I checked the signs by substitution into x_n-u_n(x_(n+1))=y_n. The maps before N may be arbitrary. Step 6 is the two-line exact-sequence diagram chase and uses only the established earlier steps. Neither elementary step hides a Mittag–Leffler theorem.

Small cases checked: L=0 and C=0; d_C=0, where N=1 and no invertibility is claimed for the transition at 0; L_n with an empty support interval; L with a single cohomology object at the boundary -d_C-1; infinitely many nonzero negative cohomology sheaves; arbitrary noninvertible maps in the initial finite segment of G. The degree computation H^q(L[-1])=H^(q-1)(L) explains why one cannot simply apply the bounded-tail theorem to all shifted truncations instead of addressing the obstruction. The complete statements used at each step are copied verbatim into citations.json.

The two generic theorem tools are existing Mathlib leaves; def-kun-truncations is used solely for its notion and explicit formulas. These are declared in split_report.tool_uses for transparency. All substantive geometric/Ext facts are existing detailed nodes from the blueprint route, with the layer Ext vanishings supplied by the bounded case already on that route. There is no new route, SGA citation, or change to another node.

## Dependency cycle repair

Before accepting the first draft I explicitly traversed the dependency closure of each proposed citation. This exposed return paths from sk-def-sfb-derived-categories, sk-def-sfb-constructible, sk-lem-uniform-constructible-ext, det-ambient-ind-derived-sums, and det-ind-heart-ii-vanishing through the imported sk-def-sf-categories / sk-def-sf-operations / Brown-hypotheses / compactness / finite-window chain back to this item. The relevant broad definitions contain theorem pointers as dependency edges; changing them is outside this worker's scope. I did not keep those cyclic edges or edit those nodes. Instead the final statement spells out the exact uniform-bound property and the notions with direct existing definition nodes, and Steps 3–4 perform the elementary truncation argument and apply the bounded-tail theorem to the two shifted cohomology layers. This retains the actual mathematical argument and all of its hypotheses. The removed aggregate citations are recorded here for maintenance; they are not being claimed proved, merged, or discarded.

## Unfinished work

None at stage 1 once the required dry run passes. The existing cited nodes remain separate work items; this delivery does not claim they have Lean proofs. No Lean was written and no compiler, Lake, build, push, or direct git command was run by the worker.

## Second reading by Q54

- Statement: checked the corrected self-contained statement against the blueprint node `det-finite-window-unbounded` and the definitions cited in its hypotheses; the previously unbound `d_C` is now explicitly a uniform Ext bound, with the same cutoff and no lower bound on `L`; verdict: faithful and well-typed.
- Step 1: checked `det-pe-left-complete-iso`, `det-pe-products-derived`, and `def-weil-abstract-derived-category`; their statements supply the left-complete cone model, derived products, and the rotated cone triangle used; verdict: all dependencies say the claimed facts and no boundedness of `L` is added.
- Step 2: checked `lem-weil-pbc-hom-into-triangle-exact` and the product universal property; the displayed exact segment and coordinate formula for `1-t` follow from those statements; verdict: complete, with no unrecorded Milnor or product theorem.
- Step 3: checked `def-kun-truncations` and `det-finite-window-bounded`; the canonical truncation cohomology formulas give the stated finite support interval and `\Dic` membership, including the empty interval and zero sheaf; verdict: valid for every `n`, without a lower boundedness assumption on `L`.
- Step 4: checked `lem-sf-derived-truncation-triangle`, `def-kun-truncations`, `lem-weil-pbc-hom-into-triangle-exact`, and `det-finite-window-bounded`, plus Stacks Tag 08J5 (remark `remark-truncation-distinguished-triangle`) and Tag 0149 (lemma `lemma-representable-homological`); the layer is `H^{-n-1}(L)[n+1]`, the shifts give degrees `-n` and `-n-1`, and the outer groups vanish for `n>d_C`; verdict: exactness proves the transition isomorphisms with the correct shift signs.
- Step 5: checked the explicit inverse-transition recursion; `N=d_C+1` covers precisely the invertible tail and the backward recursion covers the finite initial segment; verdict: elementary calculation proves surjectivity of `1-t`.
- Step 6: checked the exact segment from Step 2 together with Steps 3 and 5; the lift and zero-image chase is complete; verdict: `\Hom(C,L)=0` follows.
- New nodes: there are no new nodes in this split; consequently there are no new-node statements or Mathlib leaves to audit.

Changes made in this second reading: appended this source-and-step audit only. The first reader's corrected statement, proof steps, citations, searches, and cycle repair were retained because the cited node statements support each use and the small cases (zero object, field coefficients, empty support interval, `d_C=0`, boundary degree, and arbitrary finite initial maps) all behave as claimed.
