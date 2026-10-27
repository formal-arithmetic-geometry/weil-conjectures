# Q103 stage-1 report: lem-sfb-limit-preserving-isom-space-lft

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-limit-preserving-isom-space-lft.json: statement, split into four steps; no Mathlib match.
- citations.json: nine entries quoting the actual statements used in the four steps.
- report.md: this report. searches.jsonl is the search command's own log.

No new nodes; no new Mathlib leaves. The item's statement and statement dependencies are unchanged. No Lean was written or compiled and no repository or launcher file was changed.

## Attachments

None. Searches in lean/WeilConjectures/ for the blueprint tag, 0CXI, limit-preserving terminology and Isom-space names found no declaration stating the item. Hits about categorical limit preservation or isomorphisms of complexes do not concern moduli groupoids and are not attachments.

## WANTED

None.

## Findings and proof route

The item had no proof. I read artin.tex Tag 0CXI (lemma-diagonal), Tag 07XL (definition-limit-preserving), and the first paragraph of Tag 0CXM (lemma-base-change-versal). The diagonal proof in 0CXI uses testing on finitely presented bases and a limit criterion. Instead of introducing duplicate prerequisite nodes, the delivered proof applies the already existing relative object-descent criterion of criteria.tex Tag 06CX directly to the diagonal. This is a formal refinement below the unit route: the full isomorphism-descent hypothesis makes the relative descent verification explicit and even gives local finite presentation. The statement still asks only for local finite type. The proof does not assume that the fibred groupoid is a stack or that the base is Noetherian.

I read dag/chapters/sec-six-functors-basics.json, dag/units/sk-thm-sf-ctf-stability.json, the current blueprint unit in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md, and the item's inherited blueprint provenance. This remains a supporting moduli argument in the existing alteration prerequisite chain; it replaces no unit step. The ancestry command reports a null blueprint ancestor in the existing provenance; that maintainer-owned field and its via list are preserved. The existing from.place is already precise and is retained.

## Not duplicates

There are no new nodes. Whole-DAG and blueprint searches for 0CXI, 04AK, Isom/limit, and limit preservation led to reuse of lem-sfb-representable-lfp-object-limit-test and the existing chart and finite-type calculus nodes. In particular no new diagonal theorem, Isom theorem, finite-generation lemma, or fibre-product consequence was introduced. The more indirect lem-sfb-limit-test-representable-property, lem-sfb-space-relative-affine-limit-criterion and lem-sfb-space-lft-cancellation were read but are not needed by this direct proof.

## Mathlib searches

The item's previous search record is preserved. I ran the four required search kinds through msearch.py, plus a second semantic phrasing, and read the returned hits. LeanFinder found scheme local finite presentation and its composition/base-change instances. The second phrasing also found scheme affine-transition limit lemmas. LeanSearch found categorical relative representability of diagonals and functors preserving limits, which do not state local finite type for algebraic-space Isom functors. Loogle for AlgebraicSpace and FiniteType, and grep for AlgebraicSpace or the Isom/limit-preserving combinations, returned zero hits. These runs are recorded exactly in the appended mathlib_searches entries and searches.jsonl. There is no Mathlib match for the item.

## Review by Q103

I checked delivery-errors B through E against the actual node statements and source texts. There are no new statement-only nodes needing separate source or search audits. The original item states its groupoid and limit-preservation hypotheses inline, and the six existing statement dependencies cover the geometric notions used by its statement. No statement correction or dispute is needed.

Step 1 uses the representability hypothesis as spelled out in lem-sfb-representable-lfp-object-limit-test. I checked its statement, not its proof. The displayed two inverse constructions show precisely that the diagonal fibre is the discrete Isom functor: a morphism of triples is forced by the first comparison isomorphism, and the second compatibility is exactly equality of the two Isom elements. This is an elementary identification, not an unproved invocation of 2-Yoneda. Pullback coherence is part of the item's groupoid data.

Step 2 uses the same node's full relative-descent condition and its conclusion of local finite presentation, verified against criteria.tex Tag 06CX (including its converse proof). In the notation of that statement, I explicitly supplied c_j, alpha, and beta and checked beta restricted to the limit equals gamma composed with Delta(alpha). The only descent used is the item's descent of isomorphisms between the two objects already at stage i. It does not presume that an arbitrary object over a nonaffine scheme descends. The directed tail is small and nonempty and the index j is at least i. Representability was established in step 1, so all hypotheses of the criterion are supplied.

Step 3 cites def-sbc-locally-finite-presentation and def-weil-finite-type-morphism for their actual algebra meanings, and lem-sfb-space-local-properties-chart-test for testing these two properties on the same charts. I read spaces-morphisms.tex Tag 0464 (lemma-finite-presentation-finite-type); its local assertion is exactly the forget-relations argument written out here. This step is elementary relative to the cited chart criterion and definitions. Finite generation does not require that the base ring be Noetherian. The initially typed tag 03YR was corrected to the actual source tag 0464 before delivery.

Step 4 uses the universal property in def-pc-fibre-product to identify pairs of maps with maps to P, then applies the representing hypothesis to the two pulled-back objects on P. I read the statement of lem-sfb-stack-finite-type-calculus and checked that it explicitly includes agreement with the ordinary algebraic-space notions, arbitrary base change, and composition. Algebraic spaces (in particular U, V and P) are the special case used here; no assertion about the possibly nonalgebraic groupoid F is inferred from that node. I checked the source composition and base-change statements in stacks-morphisms.tex Tags 06FT/06FU and spaces-morphisms.tex Tags 03XG/03XH. Finally I read lem-sfb-space-etale-presentation-property-criterion and lem-sfb-scheme-etale-source-target-properties, against spaces-morphisms.tex Tag 03MJ and the stated source/target-locality condition. The former says EVERY presentation diagram, not merely a surjective atlas. Thus it applies to an arbitrary etale W -> Z, with the target chart the identity of U or V. The latter supplies exactly its required locality hypothesis for local finite type. The proof never strengthens 'chart' to 'surjective chart'.

Small cases checked: empty bases and empty Isom spaces give the empty local chart tests; identical objects include their identity isomorphism; the terminal groupoid reduces to the identity base map; a one-stage inverse system gives the same explicit beta and alpha without a descent issue. The algebra calculation remains valid with zero generators or zero relations. U and V need not be quasi-compact or separated; only local finite type is used. Every non-elementary input is a cited node; the only elementary arguments are the explicit groupoid identification and forgetting finite relations. All four proof steps are shorter than 2000 characters, and none hides a separate lemma. citations.json has one entry per uses entry, copied verbatim from each cited statement, with no claims borrowed from their proofs.

## Unfinished work

None in the authorized one-level split. The existing cited unsplit nodes remain their own items. Required server validation and direct delivery follow this report.
