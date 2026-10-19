# Stage-1 report: lem-kun-proper-stability

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-proper-stability.json`: item marked split; imported statement retained; one proof step and blueprint/search metadata completed.
- `citations.json`: verbatim citations for the two existing dependency leaves used by step 1.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, proper-stability keywords, and the blueprint tag; no sorry-free project declaration states this item. The upstream master checkout is reference material and has no finished attachment considered here.

## WANTED

None. The item and its dependencies are documented by the local blueprint and Stacks Morphisms tags 01W4 (base-change proper) and 01W3 (composition proper), while the existing DAG dependencies already record the corresponding Mathlib declarations.

## Problems in the original node or blueprint

No statement error was found. The imported proof was already a complete one-paragraph argument, but its `uses_not_cited` field omitted `def-weil-pbc-scheme-conventions`; that convention is referenced in the two existing dependency statements and is not needed as a separate proof citation. I did not create a duplicate node or move a clause of the item into a new node. The product projection is explicitly the pullback of `X → Spec(k)` along `Y → Spec(k)`, followed by the canonical pullback identification.

## Review by NL

I read the item blueprint, chapter `sec-smooth-purity`, and unit `sk-prop-sf-kunneth-ordinary`. I opened the complete statements of `lem-weil-pbc-proper-base-change` and `lem-weil-pbc-proper-composition`. The first says exactly that a proper `f : X → Y` remains proper after arbitrary base change `Y' → Y`; the second says exactly that a composite of proper morphisms is proper. These are the only non-elementary facts used by the item.

Step 1 first invokes the base-change statement for `X → Spec(k)` and `Y → Spec(k)`, yielding the pullback projection `X ×_k Y → Y`. It then invokes composition stability for the general closure claim (the order of the two clauses follows the item's statement). The identification of the pullback with the ordinary fibre product and its second projection is an elementary universal-property identification, so no extra node is warranted. The hypotheses are unchanged: `X → Spec(k)` is proper, while `Y` is an arbitrary `k`-scheme; no finite-type, separatedness, or field hypothesis is added.

I checked small cases including `Y = Spec(k)`, `X = Spec(k)`, an identity morphism, and an empty scheme where applicable. The pullback description and properness conclusions remain valid. I searched the whole DAG and blueprint for proper stability and the Stacks tags before deciding against new nodes; the existing dependency leaves are exact matches, so this split introduces none and no duplicate pair is required. `citations.json` quotes each cited statement verbatim. The mandated Mathlib searches were run through `msearch.py`; LeanSearch was unavailable and recorded as such, LeanFinder and Loogle returned the `IsProper` stability/composition/pullback declarations, and the grep search returned no hits.

No Lean files, compiler, Lake, or live project files were changed.

## Unfinished work

None at stage 1. A second reader should verify the statement/dependency equivalence and deliver the accepted dry-run tree.

## Second reading by NL

- Item statement: checked the original blueprint node (order 1709) and Stacks morphisms.tex, Tag 01W3 / lemma-composition-proper and Tag 01W4 / lemma-base-change-proper, lines 9898–9933; all hypotheses and conclusions agree. No statement dispute. The base is Spec(k), X is proper over it, and Y is arbitrary over it; no properness of Y is used.
- Step 1: opened the complete statements of lem-weil-pbc-proper-base-change and lem-weil-pbc-proper-composition and the scheme-conventions definition. Both citations give exactly the asserted stability, with no extra hypotheses. Substituting f:X→Spec(k) and g:Y→Spec(k) gives the second projection directly; the identification X×_kY=X×_{Spec(k)}Y is definitional and elementary. Verdict: valid after replacing the erroneous word “composite” by the explicit substitution and projection identification. No uncited theorem or dependency-proof construction is used.
- New nodes: none; B1–B7 impose no new-node repairs. Existing Mathlib leaves already provide both general stability facts. Searched the DAG for 01W3/01W4 and read the exact existing leaves; creating clause nodes would duplicate them. My independent Loogle search for AlgebraicGeometry.IsProper.instSndScheme returned the exact projection instance, and my grep with the corrected Mathlib-relative path found base-change stability and the projection. I also read Proper.lean lines 40–90, including composition at line 67. These remain existing leaves, not new attachments.
- Edge cases: Y=Spec(k) makes the projection f; X=Spec(k) makes it the identity of Y. Empty X gives the empty closed immersion to Y; empty Y gives the identity of the empty scheme. Composition with identities and empty-domain proper maps is consistent with the two universal statements. There is no degree n or module-zero case in this item.
- Citations: checked both quotations in citations.json byte-for-byte against the dependency statements; both remain verbatim and support step 1.

Changes: expanded only the projection application to remove the misleading “composite” wording; corrected the original grep query metadata to the actual logged query, noted its incorrectly repeated Mathlib path, and added my actual corrected-path grep and Loogle searches. All prior report sections, including Review by NL, are retained. No new nodes, statement changes, Lean writes, compiles, or live-project/launcher edits.
