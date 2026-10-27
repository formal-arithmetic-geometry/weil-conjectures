# Q113: lem-per-field-extension-generic-reducedness

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-field-extension-generic-reducedness.json: statement; split into seven steps, using existing nodes only. Mathlib verdict: no exact match or one-line specialization.
- citations.json: all 15 step/node occurrences, each quoting the cited statement verbatim.
- report.md and searches.jsonl: review and actual recorded searches.

New nodes: 0. New Mathlib leaves: 0. The item's statement and statement dependencies are unchanged. Existing metadata and earlier searches are retained. The sandbox initially contained only dispatcher brief markers, with no earlier split, report, or searches to resume.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and the generic-reducedness notion. Existing generic-fibre reducedness declarations concern geometrically irreducible models, radicial preparation, or other specialized schemes; none states this arbitrary-algebra equivalence. Also searched lean/Sheaf for context; it supplies no attachment.

## WANTED

None. All proof ingredients are in literature/stacks-project/algebra.tex.

## Corrections and scope

The item is true as stated. Its source explicitly describes a combined generic-local consequence, not a verbatim Stacks lemma. I supplied the argument and marked proof_origin.by as agent. No finite-generation, Noetherianity, algebraicity, or nonzero-algebra assumption was introduced. The perfect-field tensor theorem was already present as lem-weil-pbc-perfect-reduced-tensor, so no duplicate node was made. The finite-type scheme theorem lem-kun-geometric-reduced-perfect would not apply to A_p in this generality and was not used. Nor was the reduced-localization-field node used with the insufficient assumption that A is only generically reduced.

The latest blueprint was read at literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/lem-per-artin-gabber-affine-curve.proof.md and the current unit's _section.md, alongside the DAG chapter and unit records. This is a ring-theoretic support lemma on the inherited Step 3 duality / regular-resolution / rational approximation branch, not a change to the unit's Fourier route. The blueprint searches for generic reduced, generically reduced, perfect field, going down, faithfully flat, reduced, and localization found no blueprint node stating this item. The exact ancestor was checked with blueprint_refs.py ancestor. The off-unit non-Mathlib tool lem-weil-pbc-perfect-reduced-tensor is declared in split_report.tool_uses; it gives the necessary arbitrary reduced-algebra tensor theorem, not an alternative perverse-theoretic route.

## Not duplicates

No new nodes were created. The perfect-field tensor theorem, going down, faithful-flat scalar extension, spectra surjectivity, minimal-prime existence below a prime, flatness of local maps, local faithful flatness, and universal injectivity all reuse existing nodes. In particular 00I4 was searched across the whole DAG before deciding to cite its existing node.

## Review by Q113

I read the source statements and proofs of algebra.tex Tags 00I4 (lemma-perfect-reduced), 00HS (lemma-flat-going-down), 00HQ (lemma-ff-rings), 00HR (lemma-local-flat-ff), 00HT (lemma-flat-localization), 05CK (lemma-faithfully-flat-universally-injective), and the 00E0 prime-existence statement. I checked the labels against tags/tags. The 00I4 theorem has no finite-type restriction: any two reduced algebras over a perfect field have reduced tensor product. This is exactly why it applies to the possibly non-Noetherian A_p. The flat-local results likewise have no Noetherian restriction; the extra Noetherian conclusion in the cited node is not used.

For step 1 I opened def-weil-pbc-module-tensor-product and used its assertion that pure tensors generate and satisfy bilinearity; hence tensoring the zero algebra gives zero. For step 2, lem-weil-pbc-field-extension-base-change-faithfully-flat states precisely that arbitrary scalar extension of a commutative algebra along a field extension is faithfully flat. The tensor-definition node gives the factor-switch maps directly, and def-weil-pbc-faithfully-flat-ring-map explicitly includes flatness. No assertion about scalar extension was inferred from a definition alone.

For step 3 I opened lem-sc-flat-going-down: it lifts a smaller base prime inside the specified upper prime for a flat ring map. Here flatness was established in step 2. Minimality upstairs then forces the lifted prime to equal the original prime, proving that the contraction is minimal. This is a consequence of the cited statement, without using its proof.

Step 4 is a routine fraction calculation from the opened definitions def-weil-pbc-localization-at-prime, def-weil-pbc-module-localization, and def-weil-pbc-module-tensor-product. The inverse maps, denominator inverses, fraction relation, and generators checking that they are inverse are all displayed. The zero criterion it uses is expressly in the localization statements. I kept this as an elementary calculation rather than creating a tensor-localization node for a two-map universal-property argument.

For step 5 I opened lem-weil-pbc-perfect-reduced-tensor and checked both reduced inputs: E is a field, and A_p is reduced by the assumed generic reducedness and the minimality proved in step 3. F is perfect by characteristic zero, precisely one of the alternatives in that node. The rest is a written nilpotent fraction calculation using def-weil-pbc-localization-at-prime: from ub^n=0 one gets (ub)^n=0, then a denominator s outside p kills ub, and i(s)u lies outside q. This proves reducedness of B_q directly and avoids citing any global reducedness of A.

For step 6 I opened lem-weil-pbc-faithfully-flat-surjective-spectrum and lem-weil-pbc-prime-contains-minimal-prime. The former supplies q_0 over the specified p because i is faithfully flat. The latter applies to I=0 and q_0 and supplies a minimal q below it. The contraction of q is prime contained in the minimal p, hence equals p. Generic reducedness upstairs therefore applies to this q.

For step 7 I opened lem-weil-pbc-flat-local-ring-maps, lem-weil-pbc-flat-local-hom-faithfully-flat, and lem-weil-pbc-faithfully-flat-universally-injective. The first gives a flat local map at exactly the contracted primes. The second makes that map faithfully flat without further hypotheses. The last is specialized to N=A_p; the explicit tensor-unit identification turns its injective module unit into the local ring map. Nilpotents vanish downstairs because they vanish upstairs and that map is injective. These cited statements give every non-elementary assertion in the step.

I checked B1-B10, C1-C8, D1-D5, and E1-E7 against the written nodes and sources. There are no new statement-only nodes, omitted object hypotheses, invented source tags, unsupported attachments, cycles introduced through new lemmas, or clauses moved out of the item. Every non-elementary fact is a cited existing statement, and every citation is quoted in citations.json. No step exceeds 2000 characters (maximum 809), and the elementary tensor-localization calculation does not conceal an uncited comparison theorem: its maps and verification are given.

Small cases checked: A=0 is vacuous on both sides; E=F recovers the same generic local rings; A=F[epsilon]/(epsilon^2) is not generically reduced before or after extension, so the proof does not accidentally claim nilpotents disappear. The nonreduced algebra F[x,epsilon]/(epsilon^2,x epsilon) is generically reduced at (epsilon), since x becomes invertible and kills epsilon; the ascent argument only uses that generic localization, not reducedness of A. Arbitrary transcendental E/F and infinitely generated A introduce no missing hypothesis in any cited theorem. In descent, a prime over p is not assumed minimal: step 6 explicitly passes to a minimal prime below it and rechecks contraction.

## Unfinished work

None for this one-level split. The existing unsplit perfect-field tensor node remains another item's responsibility; no proof was added to it. No Lean file was written and no compiler, Lake, or build tool was run.
