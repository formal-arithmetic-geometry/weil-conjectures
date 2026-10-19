# Stage-1 delivery: lem-trf-generic-fibre-not-geometrically-reduced-open

## Files written

- dag/nodes/sec-trace-formula/lem-trf-generic-fibre-not-geometrically-reduced-open.json: statement, split; Mathlib searches found no spreading theorem. Statement retained verbatim.
- dag/nodes/sec-trace-formula/lem-trf-nonreduced-fibre-open.json: new statement-only lemma, unsplit; Stacks 0575, ordinary nonreducedness spreads from a nonreduced generic fibre. Mathlib searches found no match.
- citations.json: verbatim statement quotes for all 17 step citations.
- searches.jsonl: eight actual msearch.py results, read before recording the verdicts.
- report.md: this report.

## Attachments

None. Searched WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the item tag, geometric reducedness and nonreduced generic-fibre phrasings. The project's geometric-reducedness files cover smooth morphisms, perfect fields and slicing with already geometrically reduced fibres. None states 0577 or 0575. The exact master checkout was also searched for 0575 and nonreduced-generic-fibre phrasings; no attachment found. No compiler or build was run.

## WANTED

None. All sources used are in literature/stacks-project/.

## Errors and changes

The item statement agrees with Stacks 0577, lemma-not-geometrically-reduced-in-neighbourhood, including finite type rather than finite presentation, an irreducible possibly nonreduced base, and no flatness or Noetherian assumption. No statement dispute or correction is needed. Its original proof was empty. The split supplies the actual reduction argument, rather than moving geometric nonreduced spreading into another node.

The existing locus-base-change node is formulated using reduced geometric fibres, whereas the item is formulated using geometric reducedness over residue fields. Step 2 therefore cites the existing algebraic-closure test explicitly; it does not silently identify these formulations. The reduction comparison is supplied by the separate existing 054Z node, not inferred from the definition of reduction under an arbitrary base change. Only a generic fibre has that comparison here.

The existing preparation node has all needed 0550 clauses; in particular it constructs the actual reduction of the base change and an integral affine base with a finite universal homeomorphism onto a nonempty open. We use its geometric generic-fibre clause, not its flatness clause. The unreduced base-changed family is not assumed flat. Its finite-type property is checked using the existing locally-finite-type and quasi-compact base-change leaves.

## Not duplicates

The new node lem-trf-nonreduced-fibre-open is 0575 (ordinary nonreducedness); the item is 0577 (geometric nonreducedness). The ordinary statement cannot be applied to the original family when its generic fibre is reduced but not geometrically reduced. The split uses preparation, geometric base-change invariance and the reduction identity to produce a different family whose generic fibre is actually nonreduced, before applying 0575. Thus the new node is a strictly smaller input, not a clause or relabeling of the item.

Whole-DAG searches for the exact Stacks label, 0575 and ordinary-nonreduced generic-fibre statements found no existing statement of 0575. Blueprint searches for nonreduced, 0575, nonreduced generic, and not geometrically reduced found no equivalent node. The hit def-wf-lie-algebra-derivation uses nonreduced infinitesimal points to define tangent vectors; it has no generic-fibre spreading statement. Searches for geometric reducedness found the reusable 0550, 054Z, 0576 and 035X nodes, which are cited rather than recreated. No new node shares its source tag with an existing node.

## Review by Q89

I read more-morphisms.tex, Tag 0577 (lemma-not-geometrically-reduced-in-neighbourhood), its entire proof, and the inputs 0550 (lemma-make-generic-fibre-geometrically-reduced), 054Z (lemma-reduction-generic-fibre), 0575 (lemma-nonreduced-in-neighbourhood), and 0576 (lemma-base-change-fibres-geometrically-reduced). I checked the tag-to-label mapping in tags/tags. For the only new node, 0575 gives exactly its statement without flatness or a reduced base. Its proof reduces the base, finds an affine nonzero nilpotent at the generic fibre, shrinks to realize it as a nilpotent section, and uses generic freeness of its nonzero cyclic image and flatness of the quotient to keep it nonzero in every remaining fibre. This is real non-elementary content and is left as a statement-only next item, not hidden inside the current proof.

I read the statement of every node cited by the item and copied the statements into citations.json. Step 1 uses the 0550 preparation statement for the finite universal homeomorphism and the geometrically reduced generic fibre of the reduced pullback. The lft-base-change and quasi-compact-base-change statements apply to arbitrary base changes, so their conjunction gives finite type by its definition. The integral-scheme statement includes irreducibility. The universal-homeomorphism definition includes being a homeomorphism by taking the identity base change. The generic-point definition and the elementary closure argument then identify the image generic point with eta. No flatness of the unreduced pullback is asserted.

Step 2 uses exactly the equality of reduced-geometric-fibre loci in the 0576 node, applied directly to T -> Y. I checked its arbitrary-morphism quantifiers; there is no surjectivity or finite-presentation hypothesis to supply. I also read varieties.tex 035X and 020I for the algebraic-closure test's interpretation. That separate test is applied to both residue-field schemes, converting the two geometric-fibre reducedness conditions to the two geometric-reducedness conditions. This explicit citation repairs the potential mismatch between the item and the locus node.

Step 3 uses the exact canonical reduction/generic-fibre identity of the 054Z node. The point xi is generic in integral T, so its required generic-component hypothesis holds. On a reduced affine the nilradical is zero, hence its reduction map is the identity quotient; gluing gives the isomorphism used in the contradiction. Reduction, reducedness and geometric reducedness are invariant under these isomorphisms simply because the affine section rings, and their scalar extensions, are isomorphic. This step uses no claim that reduction commutes with all fibres.

Step 4 uses only the newly stated 0575. Finite type, irreducibility and a genuinely nonreduced generic fibre have all been established before the application. In step 5 the image of a nonempty open under the homeomorphism is a nonempty open; openness is transitive through U -> Y. The fibre identification is written using the universal properties in the cited fibre-product and fibre definitions. Taking the particular residue-field extension kappa(y) -> kappa(t) in the definition of geometric reducedness then contradicts ordinary nonreducedness of P_t. This final step is elementary from the cited definitions, so it needs no extra base-change-descent lemma.

I tested the ordinary statement on Spec(k[epsilon]/epsilon^2) -> Spec(k), on k[t,epsilon]/(epsilon^2) over k[t], and on the family k[t,x]/(x^2,t*x) whose nilpotence is confined to a special fibre. The last has reduced generic fibre, so 0575 correctly gives no conclusion. I tested the distinction between the two statements on Spec(k(a^(1/p))) over the imperfect field k of characteristic p: its source is reduced but its geometric fibre is not; after the inseparable preparation the tensor product has nilpotents, exactly as the proof requires. For a possibly nonreduced irreducible base, e.g. k[t,delta]/delta^2, no argument identifies base reduction with the unreduced family. Empty generic fibres are geometrically reduced, so the item's negative hypothesis excludes them; empty fibres elsewhere cannot belong to the open obtained from 0575. Non-Noetherian bases remain covered by the actual hypotheses of 0550 and 0575.

I checked delivery-errors B through E: statements introduce all their objects and cite the notions they use; source labels are exact Stacks tags; no proof is left in the new node; every non-elementary step cites an applicable statement; the proof-dependency list is the union of the step citations; the new node is neither elementary nor a duplicate nor the item in disguise; and no citation uses only a definition for a non-elementary theorem. All five steps are under 2000 characters. No SGA source, target, coefficient convention, chapter route or unit realization is changed. The item is a downstream constructibility tool in the supplied sk-i-curve-zero ancestry, not the unit's key node. Generic preparation and reduction of generic fibres are declared as tool uses from the purity unit; the unit itself does not supply these generic scheme lemmas. I checked that none of the reused theorem nodes depends on the item, so this split introduces no cycle.

## Unfinished work

None for this one-level split. The ordinary-nonreduced spreading input is intentionally an unsplit statement-only node, to be handled as its own item. The required dry run completed successfully; its result is recorded below.

## Validation

The required deliver.py Q89 lem-trf-generic-fibre-not-geometrically-reduced-open --no-push exited 0 and printed OK (not pushed) at 22458a3edd: preflight passed. No failures required repair. This was the sole active delivery invocation and it exited before the push.
