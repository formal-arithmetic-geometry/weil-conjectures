# Stage-1 report: lem-sfb-filtered-colimit-naive-cotangent-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-filtered-colimit-naive-cotangent-comparison.json`: item, split; statement unchanged. Six proof steps establish the canonical comparison, in fact a chain isomorphism, and conclude the required derived isomorphism.
- `dag/nodes/sec-six-functors-basics/lem-sfb-filtered-colimit-conormal-modules.json`: new statement, unsplit; no exact or one-line Mathlib match. This is a general ideal-square quotient lemma for filtered diagrams of algebras with compatible ideals; its proof is deliberately left out of its node.
- `citations.json`: one verbatim statement quotation for each node used by each proof step.

## Attachments

None. Searched `lean/WeilConjectures/` by the item's full blueprint tag and by cotangent/colimit and conormal/colimit words. The existing `Algebra.subsingleton_h1Cotangent_of_finite_subfields` in `WeilConjectures/RingTheory/H1CotangentFiniteSubfields.lean:48` only proves vanishing over a field extension from vanishing over finitely generated intermediate fields. It does not state this item's arbitrary filtered-algebra comparison. No declaration was attached.

## WANTED

None. All sources used are present.

## Audit of the imported item and route

The imported item was statement-only. Its statement is correct; there is no statement dispute and no change of hypotheses. Stacks Algebra Tag 07BQ, label `lemma-colimits-NL`, proves the directed-set varying-base result, using canonical polynomial presentations and the colimit of their kernels. I read the full statement and proof at `algebra.tex:35557` and the surrounding flat-base-change lemma. The present item needs the constant-base case for a small filtered category. Rather than apply a directed-set theorem to a general category, the split uses the existing category-indexed elementwise results and explicitly equalizes parallel arrows. Flat base change is not used.

I read the chapter and unit records and the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and direct-images proof, paragraph (3). This is the supporting local algebra along the inherited alteration/cotangent chain already recorded in the item's blueprint provenance. The unit and chapter route are unchanged. `blueprint_refs.py ancestor` returns None for this inherited new-target chain; I preserved that null ancestor and the existing exact place, prepending the item to the new node's via list. Whole-blueprint searches for cotangent, conormal, polynomial and filtered colimit did not supply a statement of the new lemma. DAG searches by Tag 07BQ and by conormal, ideal-square and polynomial-colimit words were also inspected.

## New-node argument reserved for its future worker

The new node cites Tag 07BQ as its source; the general elementwise criteria in Tags 00D6, 00D7 and Section 04AX are supporting tools discussed here, not statements of this conormal assertion. For the conormal lemma, surjectivity follows from the assumed elementwise lifting of I. If x_j in I_j maps into I squared, write its image as a finite sum of products a_r b_r with a_r,b_r in I. Lift all these factors to compatible ideals at finitely many stages, then choose a common target with j. The equality between the image of x_j and the sum of products holds in the ring colimit. Elementwise eventual equality, followed by equalization of parallel arrows, makes it hold after one further arrow from that common target. Thus x_j is in the square of the ideal there, so its conormal class is zero. Apply the existing filtered-module colimit criterion. This is a general lemma about ring/ideal diagrams, independent of canonical polynomial presentations, differentials or derived categories; it does not restate either conclusion of the item.

## Mathlib searches

The item's pre-existing searches were retained and their recorded queries rerun for Q09. All new-node searches were run through msearch.py and their exact query strings and actual returned names are in the node and searches.jsonl. The two semantic phrasings for conormal colimits returned individual ideal conormal constructions, local cohomology diagrams, and general colimit results. Loogle returned no result for cotangent plus colimit; the RingTheory grep also returned no match. I read `Mathlib/RingTheory/Ideal/Cotangent.lean:42` through the quotient and zero-class lemmas at lines 57-100: these construct I/I squared and test its classes, but do not assert the filtered-colimit comparison. The general `colimitLimitIso` hit does not handle ideal multiplication and quotient without additional arguments. Thus the new node is unsplit, not a Mathlib leaf. The item's searches returned extension cotangent functoriality and flat base change, which likewise do not assert this comparison; I read the maps in `Mathlib/RingTheory/Extension/Cotangent/Basic.lean:380` onward. No search result was invented, and no direct Mathlib grep bypassed msearch.py.

## Not duplicates

- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-locally-dense-cotangent-h1: that node concerns sheafification of first cotangent homology for a locally dense subpresheaf; the new node concerns ideal-square quotients in an arbitrary ring diagram.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-strict-henselization-naive-cotangent: that node compares cotangent complexes across compatible strict henselizations; the new node has no local rings or henselizations.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-ind-etale-naive-cotangent-acyclic: that node proves acyclicity for ind-etale maps; the new node makes no etaleness or vanishing assertion.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-directed-union-cotangent-h1: that node concerns first homology for directed unions of subalgebras; the new node concerns conormal modules for compatible ideals and allows noninjective maps.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-filtered-colimit-naive-cotangent-comparison: the item concerns the canonical naive cotangent complex and its derived comparison; the new node concerns arbitrary compatible ideals in arbitrary algebra diagrams and no differential.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-ind-etale-jacobi-zariski-left-injective: that node asserts injectivity in a cotangent homology sequence with an ind-etale algebra; the new node is a general conormal colimit assertion.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-separable-field-square-zero-lifting: that node lifts maps from separable field extensions across square-zero quotients; the new node concerns filtered ideal diagrams without fields or lifting.
- lem-sfb-filtered-colimit-conormal-modules vs lem-sfb-sheaf-polynomial-cotangent-comparison: that node compares different sheaf polynomial presentations in a derived category; the new node concerns ordinary compatible ideals and module colimits.
- lem-sfb-filtered-colimit-conormal-modules vs lem-weil-pbc-transitivity-gamma: that node asserts exactness of the field-extension Jacobi-Zariski sequence; the new node asserts a conormal colimit for arbitrary compatible ideals.
- lem-sfb-filtered-colimit-conormal-modules vs lem-weil-pbc-h1-cotangent-finite-subfields: that node deduces first-homology vanishing over a field from finitely generated subfields; the new node concerns conormal modules of ideal diagrams.
- lem-sfb-filtered-colimit-conormal-modules vs lem-weil-pbc-field-char-p-h1-cotangent-vanishing: that node asserts first cotangent homology vanishes over the prime field; the new node has no characteristic or homology-vanishing hypothesis.

## Review by Q09

I checked this split against delivery-errors B through E with the source and the actual cited statements open. For the item and the new node I read Tag 07BQ's proof. For the elementwise extension to a small filtered category I read Categories Section 04AX (`section-directed-colimits`), including its eventual-equality description, and Algebra Tags 00D6 and 00D7. I did not invoke the source's unexplained word "clear" as a proof. The general ideal-square assertion hidden there is isolated as the new statement-only node and its intended finite-product proof is recorded above.

Step 1 takes the underlying-ring colimit and representatives from `lem-weil-pbc-filtered-colimit-algebras-elementwise`, and common-target equality from `lem-pc-filtered-colimit-commrings-elementwise`. I read both statements: the algebra node alone only supplies representatives, so equality is separately cited from the ring node. I checked the filtered-category definition supplies common targets and equalization of parallel arrows; iterating these operations makes only finitely many choices simultaneous.

Step 2 uses those same representative/equality clauses and the actual polynomial universal property in `def-weil-pbc-mv-polynomial-ring`. The construction is explicit evaluation on representatives of labels, not an uncited preservation theorem. It proves the polynomial cocone is a colimit before that fact is used in step 3.

Step 3 uses algebra-colimit representatives for the polynomial diagram, and eventual zero in the S_j diagram. Evaluation commutes with renaming on each generator, so a polynomial representative becomes a member of a later kernel. I checked every hypothesis of the new conormal lemma: fixed R, small filtered J, polynomial algebra colimit, compatible kernel ideals, images in the limiting kernel, and every limiting kernel element lifted to an actual kernel at a stage. Its conclusion is exactly a module colimit with the maps used by c in degree -1. No flatness or injectivity is smuggled in.

Step 4 uses representatives and eventual equality from the same two existing leaves and the exact statement of `lem-weil-pbc-filtered-colimit-modules-criterion`. It verifies both that criterion's surjectivity condition and its same-stage eventual-zero condition. The finite-support argument groups labels that become equal; treating the original support labels as permanently distinct would be incorrect for this item. Coefficients and labels both live in S_j, so their finitely many equality witnesses can all be realized using step 1. This is the routine finite-sum calculation itself, not a black-box free-module preservation claim.

Step 5 uses the displayed differential in `def-weil-pbc-smooth-ring-map` and the polynomial finite-monomial construction. I verified the Leibniz computation after applying the coefficient homomorphism, rather than claiming individual partial derivatives commute with a noninjective rename (they need not). Equal generator values and the product rule prove equality for each monomial and hence each polynomial. Products of kernel elements map to zero under the differential because both evaluations are zero. The formulas also prove identity and composition, so the component comparisons are for the stated canonical chain map.

Step 6 uses the definition of quasi-isomorphism and localization in `def-weil-abstract-derived-category`. It constructs the inverse chain map from the component inverses, and then takes cohomology and localization. It does not cite a definition node for an unproved exactness theorem. The degree convention is cohomological -1,0, the reindexing of the definition's homological 1,0, with the same displayed differential.

I tested the new statement at zero ideals and at unit ideals (the conormal module is zero in each respective case), constant and singleton diagrams, and diagrams in which an ideal element dies under a transition. In the last case its class dies too, which is precisely why eventual equality rather than inclusions is needed. The hypotheses exclude an empty index category. For the item's free term I tested a quotient R[x] to R sending x to zero: the two labels x and 0 merge, and d[x]-d[0] becomes zero by the partition calculation. A zero limiting algebra is allowed: its coefficient module is zero even though the label set is a singleton. None of the proof requires a finite set of generators of the algebra. Every step is shorter than 2000 characters; the actual general ideal-square lemma has been extracted instead of hidden in a long step. All citations have literal quotations in citations.json, and proof_deps is their union.

The new node introduces its own rings, ideals, maps and square/quotient meaning. Its proof and proof_deps are empty. Same-tag nodes are distinguished above; the more specialized directed-union homology node does not subsume it. All off-unit citations are existing Mathlib leaves or definitions; the new lemma inherits this unit. No tool-use exemption or change of route is needed.

## Unfinished work

No required stage-1 work remains in the item. The new conormal node intentionally remains unsplit for a subsequent worker. No Lean source, compiler, Lake, repository file or launcher file was changed.
