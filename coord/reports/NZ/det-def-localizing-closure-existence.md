# Worker report: det-def-localizing-closure-existence

## Files written

- dag/nodes/sec-proetale-coefficients/det-def-localizing-closure-existence.json: statement, split in six steps; searched the whole item in Mathlib, no matching declaration; 0 new nodes, 0 new Mathlib leaves.
- citations.json: verbatim statements for every step/node pair.

## Attachments

None. Searched the exact blueprint id in both specified source checkouts, and searched the project's WeilConjectures/ for localizing/localising closure and the relevant coproduct and triangle notions. No declaration states all three clauses. The upstream master is reference material only. The already existing derived-coproduct node has its own Lean record; it is reused, not claimed as an attachment for this item.

## WANTED

None needed for this split. The imported Neeman Lemma 3.2.10 citation is not used: existing Stacks 07D9 supplies precisely the required arbitrary coproducts. The proof is marked agent-written, following the current blueprint with these existing foundational inputs.

## Problems and corrections

STATEMENT-DISPUTED (typing of an optional example only): the imported item quantifies over an arbitrary condensed ring but names Dctf as an example without qualification. The cited det-def-sfb-constructible-tor-amplitude defines that notation only for a commutative condensed ring; for example the finite discrete condensed ring M_2(F_2) is within the item's hypotheses and outside that definition's domain. The corrected sentence says "for instance, when Lambda is commutative". All three mathematical assertions retain the original arbitrary-ring hypotheses and conclusions. Definitions of the coefficient object, derived category, size conventions, localizing and thick are now explicitly cited or stated. This adds no hypothesis to the existence theorem.

The imported proof cites sk-prop-sfb-module-category, which is absent from dag/nodes. Its current blueprint _section.md asserts the Grothendieck module result in parts 3-4 for a commutative ring object, so applying that assertion to the item's arbitrary ring would lose a hypothesis. Step 1 instead writes the elementary equivalence between an internal left action and a sectionwise left action, using the existing sheaf tensor universal property over Z. Step 2 uses lem-weil-pbc-ring-sheaves-grothendieck, whose statement explicitly does not require commutativity. The existing def-weil-pbc-internal-abelian-sheaf-module-equivalence was opened and rejected as the sole citation here because it assumes a commutative monoid. No duplicate is introduced for the noncommutative unpacking.

The source's informal swindle omitted the reindexing map and the precise inclusion. Step 5 gives both inverse reindexings and uses the standard distinguished split triangle T -> T plus A -> A, citing the existing Mathlib leaf. The equality between objects in the imported proof is rendered as isomorphism throughout.

The new snapshot's item has no chapter/unit metadata and its corresponding sec-proetale-coefficients chapter and sk-def-localizing-closure unit are not present among dag/chapters and dag/units. Their actual main-20261015 blueprint _section.md files were read directly; they remain unchanged. The item is an auxiliary lemma of the localizing-closure definition, not the unit's key definition. Its blueprint.is equals its own id and from remains null, as appropriate for an imported blueprint node. No metadata or unit-file repair is attempted.

## Existing-node and Mathlib searches

Whole-DAG searches covered localizing closure, direct sums, coproducts, Grothendieck categories, internal modules, split triangles, direct summands, and the Stacks labels/tags. Whole-blueprint searches via tools/blueprint_refs.py covered localizing closure, module category, Grothendieck, derived coproducts, intersection localizing and direct summands, as well as the ancestor lookup. None gives all three assertions in another blueprint node: same_as is []. Existing lem-kun-grothendieck-derived-coproducts gives arbitrary small termwise coproducts, so no new coproduct node is created. Existing lem-sbc-biproduct-triangle-distinguished gives exactly the swindle triangle, so no split-triangle node is created. pur9-def-thick is reused only as a definition.

Every recorded Mathlib query was actually run with msearch.py; searches.jsonl is the tool's log. Semantic searches used two different derived-category phrasings and a separate swindle phrasing; Loogle searched the expected localizing-subcategory name, ObjectProperty with coproduct, and thick; grep searched both category theory and the derived-category directory. The localizing-subcategory hit is Verdier-localizing rather than closure under all sums, the derived-category hits provide foundations rather than the three-clause result, and the thick search largely gives metric thickenings. No whole-item Mathlib match was inferred from them. No new node needs a search record.

## Tool uses

- lem-pc-sites-sheaf-tensor-bilinear-universal is used with O the constant sheaf Z, not with the possibly noncommutative coefficient ring. It gives the two-way translation between natural bilinear actions and tensor maps. This is a general tensor tool.
- lem-weil-pbc-ring-sheaves-grothendieck supplies the Grothendieck category of left modules over an arbitrary ring sheaf on a small site.
- lem-kun-grothendieck-derived-coproducts supplies coproducts of any small family, including the empty family. It is a generic Stacks input, not a detour through the Kunneth theorem.
- lem-sbc-biproduct-triangle-distinguished is a Mathlib tool giving the standard split distinguished triangle.

## Not duplicates

No new nodes. All found generalizations are cited directly; the elementary cone calculation, intersection argument, swindle reindexing and comparison of generating classes remain proof steps.

## Review by NZ

I read the current main-20261015 existence statement and its complete three-paragraph proof, the localizing-closure unit _section.md and the pro-etale-coefficients chapter _section.md. I also opened the current module-category unit, which is where I found the commutativity mismatch described above. The source places used for the actual split were read in the local Stacks files: injectives.tex Tag 079Q (remark-existence-D, whose last sentence explicitly includes module sheaves on a ringed site), Tag 07D9 (lemma-derived-products, all three statements and the proof), sites-modules.tex's module definition (03CV), and derived.tex Tag 05QT (lemma-split, specifically (3)). The cone construction is read from the existing abstract-derived-category node, whose statement includes its matrix differential and the negative projection. No SGA source is used.

Step 1 uses exactly four statements: sk-def-sfb-module-objects defines the action map and its associativity/unit equations; sk-def-sfb-sheaf-tensor specifies sheafified pointwise tensor; lem-pc-sites-sheaf-tensor-bilinear-universal gives natural bilinear maps if and only if tensor morphisms; def-weil-sheaf-of-modules-category defines sectionwise modules and linear morphisms. I checked the commutativity hypothesis on the bilinear lemma: the base is Z, so it is satisfied even when Lambda is not commutative. Products and actions are defined on sections and restrictions are natural. Checking the ring and module axioms on pure tensors is elementary because the given universal property determines each tensor morphism uniquely. Linearity over the constant ring sheaf Z is checked locally where its scalar section is an integer; this also identifies the tensor with the sheafified objectwise abelian-group tensor. The inverse action constructions and the equations on morphisms are explicitly written; no theorem about a different module notion is silently assumed.

Step 2 uses the exact small-site convention of def-weil-pbc-proetale-site and def-weil-size-convention. The chosen skeleton is small in the working coefficient universe, so lem-weil-pbc-ring-sheaves-grothendieck applies, without a qcqs assumption and without requiring constant coefficients. Its statement expressly covers noncommutative ring sheaves. lem-kun-grothendieck-derived-coproducts then applies to this Grothendieck abelian category, with every set in the chosen indexing universe, not merely countable sums. def-weil-abstract-derived-category defines D as localization of complexes, so every derived object is represented. I checked that there is no dependence back from the cited coproduct or ring-sheaf theorem on this item.

Step 3 uses the exact cone-triangle characterization and differential from def-weil-abstract-derived-category, not merely the word "triangulated" from a definition. Together with the previously cited termwise coproduct theorem it reduces the compatibility to the displayed block differential and the inclusion/negative-projection maps. Rebracketing a coproduct of binary sums is given by inverse maps on the individual coprojections. Summing chosen triangle isomorphisms preserves invertibility by summing their inverses. Thus this step contains its argument rather than moving the clause "sums of triangles are distinguished" into a new node.

Step 4 is elementary predicate reasoning: zero, all integer shifts, isomorphisms, two-of-three for triangles and all small sums pass to the intersection. The collection is nonempty since it contains the ambient category. Minimality is immediate from the universal quantifier. This does not invoke a small-index colimit of subcategories or assume S is essentially small. Step 5 uses lem-sbc-biproduct-triangle-distinguished with X=T and Z=A, whose statement is exactly the split triangle written in the step. The explicit reindexing verifies the absorption isomorphism; no finite-cancellation claim is made. Closure under cones from step 4 therefore gives A. pur9-def-thick is used only for the definition of thick after summand closure is proved. Step 6 uses minimality twice with the correct inclusion directions and no additional cited theorem. citations.json copies the statements verbatim for each citation.

The small cases checked were the empty scheme/zero coefficient category, the empty coproduct and zero triangle, S empty, S all objects, S=S', a zero summand, and a noncommutative finite coefficient ring. The swindle uses countably infinitely many copies, which are small under the fixed convention; its inverse works also when either summand is zero. The conclusion Loc(S')=Loc(S) when S'=S or S'=Loc(S) follows in both directions. No new unsplit statements, definitions or leaves were created, so B1-B8 and the new-node edge-case/duplicate checks introduce no outstanding items. C1/C4 were checked against the opened statements as detailed above; D1/D2 are avoided by keeping every actual closure argument in the item. The only statement correction is the optional commutative example, explicitly reported above. All metadata and import flags are retained.

## Unfinished work

None at this level of splitting. No Lean was written or compiled, no agents were started, and no live repository or launcher file was changed. The second reader should review the explicit internal/sectionwise module translation, especially its use of the tensor universal property over Z. Delivery is intentionally left to that reader after the required dry run.

## Second reading by NZ

- Item statement: checked against `sk-def-localizing-closure-existence.md` in blueprint snapshot `main-20261015`, clause by clause; the arbitrary condensed-ring hypotheses and all three conclusions are retained, and the optional `Dctf` example is correctly restricted to commutative coefficients.
- Step 1: checked the internal module-object action, the sheafified objectwise tensor, the tensor universal property, and the sectionwise module definition; the scalar sheaf is the commutative constant $\mathbf Z$ so the argument does not impose commutativity on $\Lambda$.
- Step 2: checked the chosen small pro-etale skeleton and universe against the site and size definitions, and the Grothendieck and derived-coproduct node statements; arbitrary universe-small families, including the empty family, are covered.
- Step 3: checked the cone formula and block differential against `def-weil-abstract-derived-category` and termwise coproducts against `lem-kun-grothendieck-derived-coproducts`; the rebracketing and preservation of triangle maps are explicit.
- Step 4: checked each intersection closure condition (zero, generators, isomorphisms, shifts, cones, and sums) and the nonempty ambient family; no smallness of the class of generators is assumed.
- Step 5: checked the countable Eilenberg reindexing maps in both directions, the split triangle against `lem-sbc-biproduct-triangle-distinguished`, and the thick definition against `pur9-def-thick`; zero objects and zero summands are covered.
- Step 6: checked both minimality inclusions with the hypotheses $\mathcal S\subseteq\mathcal S'\subseteq\Loc(\mathcal S)$; the directions of containment are correct.
- Sources: reopened Stacks `injectives.tex`, Tag 079Q (`remark-existence-D`) and Tag 07D9 (`lemma-derived-products`, clauses 1--2); `sites-modules.tex`, Tag 03CV (`definition-sheaf-modules`); and `derived.tex`, Tag 05QT (`lemma-split`, clause 3). Each matches the use of its existing node. The current chapter, localizing-closure unit, and module-category unit were also read.
- Existing dependencies: reopened every cited node and compared the quoted statement in `citations.json` verbatim; no citation relies on a proof body or an absent assertion.
- Independent Mathlib searches: reran LeanFinder with "localizing closure triangulated coproducts direct summands" (eight generic localization/triangulated-property hits), Loogle with "localizing subcategory coproducts" (unknown identifier, hence no positive match), and grep with "LocalizingSubcategory|localizingClosure|IsLocalizing" (Verdier and probability localizing terminology; no closure theorem). Actual results remain in `searches.jsonl`.
- New nodes: none; therefore B1--B7, duplicate-node checks, and per-node edge cases are vacuous. Whole-DAG and whole-blueprint searches were reviewed, and the recorded Mathlib searches are actual `msearch.py` results.
- Small cases checked: empty scheme/zero category, empty coproduct, zero triangle and summand, empty and total generator classes, equal generator classes, and a finite noncommutative coefficient ring.

Changes made in this second reading: added this audit section only. No node or proof text required repair after checking the source, dependencies, citations, and edge cases.
