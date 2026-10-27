# Worker report: lem-sfb-algebraic-stack-open-dm-locus

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-algebraic-stack-open-dm-locus.json`: item, statement unchanged, split into seven proof steps following the DM part of Stacks 0DSM.
- `dag/nodes/sec-six-functors-basics/lem-sfb-open-substack-unions.json`: new statement-only lemma, not in Mathlib. Set-sized representatives, arbitrary open-substack unions, their least-upper-bound property, algebraicity, and their scheme-pullback description.
- `citations.json`: one verbatim statement excerpt for every cited node in every proof step. The union lemma is quoted in full because different steps use its different clauses.

One new node, zero new Mathlib leaves. The three existing scheme facts used below are Mathlib leaves already in the DAG.

## Attachments

None. Searched the project under `lean/WeilConjectures/` for the item id, its blueprint tag, Deligne/Mumford, DM locus, algebraic stacks, open substacks and unramified diagonals. There is no project declaration stating this item or the new union lemma. The unramified-diagonal matches found are morphisms of schemes; neither these nor a Mathlib declaration can attach the algebraic-stack theorem. No Lean was written and no compiler, Lake or build was run.

## WANTED

None. All proof sources used are present in `literature/stacks-project/`.

## Audit of the imported node and proof route

The item was unsplit and had no proof, Lean audit or blueprint update. Its statement is correct as imported; in particular its diagonal is relative to the given arbitrary scheme S. Stacks 0DSM is the largest-DM-open assertion, and the existing node `lem-sfb-unramified-diagonal-etale-atlas` already translates 06N3 to precisely this relative-base convention using 050N. No additional relative/absolute comparison is smuggled into this split.

I read the chapter record `sec-six-functors-basics` and unit record `sk-thm-sf-ctf-stability`. The item's inherited provenance is the curve-moduli prerequisite below the constructible-direct-image alteration route; it is not the unit's key theorem. Its inherited nearest imported-blueprint ancestor is null, as confirmed by `tools/blueprint_refs.py ancestor`. The new node preserves that ancestry and inserts this item at the front of the inherited via list. No chapter or unit was edited. Whole-blueprint searches for unramified diagonal, open substack(s), and union of open(s), together with searches of the current and historical blueprint text, yielded no node stating either the item or the new lemma.

The proof follows the source's atlas argument. The original 0DSM proof explains the binary union and leaves the passage to the largest open implicit. I made the set-indexed union explicit using 06FJ and 05UQ. The source's words that the disjoint union is etale and surjective are expanded on arbitrary scheme tests, rather than introducing a node restating preservation of the DM property under unions.

## Searches and reuse

Every new-node Mathlib query was run through the mandated `msearch.py` command and remains in `searches.jsonl`; its exact tool/query and actual logged results are recorded in the node. I tried two semantic phrasings, LeanSearch, Loogle `"AlgebraicStack"`, and a grep for `OpenSubstack|openSubstack|AlgebraicStack|open.*substack|substack.*union` in AlgebraicGeometry. The semantic hits are scheme opens, scheme gluing, open covers, and preservation of unions of opens under scheme pullback. They do not give an algebraic open substack, stack descent, or a set of stack-open representatives. Loogle and grep returned no hits. For the item I also ran LeanFinder and LeanSearch on largest-DM-open/unramified-diagonal phrasings, Loogle `"DeligneMumford"`, and the recorded DM-locus grep; these produce scheme/ring unramifiedness, not the stack theorem. Earlier genuine searches already present on the item were retained unchanged.

The general scheme facts were found and reused, not recreated: `lem-weil-pbc-scheme-coproduct-family` allows an arbitrary set-indexed family; `lem-weil-pbc-etale-composition-cancellation` supplies both the open-immersion and composition clauses; and `lem-weil-pbc-etale-local-on-source` allows an arbitrary open cover. In particular I did not use `lem-sc-etale-coproduct-etale`, whose statement assumes a finite family, or the field-only `lem-exc-etale-coproduct-etale` for this arbitrary scheme atlas.

## Not duplicates

No existing node has source Tag 06FJ or 05UQ or the labels lemma-open-substacks / lemma-union-open-substacks. DAG searches by these tags and by open-substack/union terminology, and full blueprint searches, found no statement containing the new lemma. The source tag 0DSM is shared by the item and the point-stabilizer node, but it is not a source tag of the new union lemma.

lem-sfb-open-substack-unions vs lem-sfb-algebraic-stack-open-dm-locus: the new lemma constructs unions of arbitrary algebraic open substacks and controls size and scheme pullbacks; it says nothing about the diagonal being unramified, DM stacks, or an etale atlas, and does not assert the item's existence or maximality clause for DM opens.

lem-sfb-open-substack-unions vs lem-sfb-unramified-diagonal-etale-atlas: the existing node is the equivalence between unramified relative diagonal and an etale scheme atlas. It contains no open-union construction or size assertion. The proof uses the existing equivalence in both directions, rather than creating a duplicate.

lem-sfb-open-substack-unions vs lem-sfb-algebraic-stack-dm-point-stabilizer: that node characterizes a point of the DM locus by its geometric stabilizer, and depends on the present item. It cannot supply unions or an atlas here without a cycle.

## Review by Q13

For the item I read the actual proof of Stacks Tag 0DSM, lemma-open-DM-locus in stacks-morphisms.tex, its reference 06N3, theorem-DM, and the relative convention in definition-absolute-separated and 050N, lemma-separated-implies-morphism-separated. For the sole new node I read both 06FJ, lemma-open-substacks, with its proof via a presentation, and 05UQ, lemma-union-open-substacks, including its full-subcategory construction and its two cartesian squares. The set of representatives follows from 06FJ's bijection with open subsets of the underlying topological space, not from a claim that all scheme-indexed data form a small set. The union's scheme-pullback assertion is precisely the cartesian formula in 05UQ's proof. The new statement contains no proof and no unproved additional DM assertion.

Step 1 uses the set-sizedness, algebraicity, and scheme-pullback clauses of the new union lemma, all stated there: this justifies selecting the candidate family and obtaining its union as an algebraic stack. Step 2 uses the entire equivalence in `lem-sfb-unramified-diagonal-etale-atlas`, whose statement I read; each chosen candidate is algebraic and has exactly its unramified relative diagonal hypothesis. I do not take the etale atlas merely from the definition of an algebraic stack, which only gives a smooth atlas.

Step 3 uses the arbitrary-index coproduct and disjoint open covering clauses in `lem-weil-pbc-scheme-coproduct-family`. I checked its statement, including the quantifier over any set I. Its universal property is only for scheme targets; I therefore do not apply that property to a stack target. The map to the stack is explicitly glued by the descent axiom in `def-sfb-stable-pointed-moduli-groupoids`, whose last paragraph I read. Representability then follows directly from the representable diagonal: the test fibre product is its base change by the scheme product. These are direct applications of definitions and the cited statements; there is no separate atlas-assembly lemma to create.

Step 4 uses the generic stack/chart convention in `def-sfb-stable-pointed-moduli-groupoids`, the union's scheme pullbacks, the coproduct's open summands, clauses (1) and (2) of `lem-weil-pbc-etale-composition-cancellation`, and the arbitrary-cover equivalence in `lem-weil-pbc-etale-local-on-source`. I opened and read every cited statement, as well as the source statements 02GP, 02GN and 02GJ in morphisms.tex. The source and target to which the composition and locality nodes are applied are schemes P_i, T_i, P and T; they are never applied directly to an algebraic stack or algebraic space. For a chart P of the representable test fibre product E, its inverse images P_i of the W_i summands cover P, and each P_i is a chart of the base change of the selected atlas a_i. Thus the etale premise is available from that selected representable atlas and the chart-test definition. The identification with W_i times over U_i T_i is the identity on triples in the 2-fibre product, using the fact that an open substack is full. This avoids the erroneous claim that U_i times U_i cover U times U. These checks expose the whole atlas argument in the item instead of hiding it in a new node.

Step 5 uses the union lemma's covering conclusion and the scheme-test definition of representable surjectivity. The chosen atlas surjects after every base change to T_i, so its image covers each T_i and hence T. It does not assume a scheme section of the atlas or a rational point in every fibre. Step 6 applies the opposite direction of the existing atlas equivalence only after the new union lemma has given algebraicity and steps 3--5 have given representability, etaleness and surjectivity. Step 7 uses the union lemma's containment conclusion; membership in the candidate index set is precisely the hypothesis imposed on the comparison open. All cited pieces are copied verbatim in citations.json, including the generic final paragraph of the moduli-groupoid definition rather than its unrelated curve-specific clauses.

I tested the small cases. The union lemma works for an empty family (empty open), a singleton, repetitions, and an infinite family; no finite-cover inference occurs. If X is already DM the index family contains X, so the result is X. If X is empty the atlas may be the empty scheme, and all scheme tests are empty. If there is no nonempty DM open, for example the classifying stack of G_m, the only candidate open is empty and the constructed locus is empty. No finite type, noetherian, quasi-separated, separated-base, or quasi-compact hypothesis is used. The new statement allows ordinary open substacks, not arbitrary locally closed substacks. I checked that no new node restates either clause of the item and that the point-stabilizer node depending on this item is not cited. There are no steps longer than 2000 characters. No statement correction, source dispute, or route departure was needed.

## Unfinished work

The one new general lemma is deliberately statement-only for a later stage-1 item. The present item has its complete one-level split. Server checks and final push are performed by the prescribed delivery command.
