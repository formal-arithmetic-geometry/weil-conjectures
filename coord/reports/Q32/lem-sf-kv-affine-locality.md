# Worker report — Q32 — lem-sf-kv-affine-locality

## Files written

- dag/nodes/sec-six-functors/lem-sf-kv-affine-locality.json: statement, split into ten proof steps; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each node used by each step.
- report.md: this report and direct-delivery review.

New nodes: 0. New Mathlib leaves: 0. The pre-existing search entries, blueprint provenance and original creation record were retained. searches.jsonl contains the additional searches actually run by Q32. rewrite.py is a sandbox-only preparation script, not a delivery node.

## Attachments

None. Searching WeilConjectures/ in /home/ubuntu/weil-src-slopmaster2 for the exact item/blueprint tag produced no declaration; the relevant scheme restriction and generic adjunction names do not establish all clauses of this item. No Lean was written, opened in a compiler or compiled.

## WANTED

None. This is an agent-written elaboration of the available blueprint, using existing DAG statements for the non-elementary tools.

## Statement clarified and source scope checked

STATEMENT-DISPUTED: the imported item leaves K and Q untyped, and its reference to the specified Ku_! map inherits a domain mismatch in sk-def-sf-kv-maps(i). That definition allows nonseparated finite-type schemes, but identifies the map with sk-thm-sf-kunneth-relative on B=Y_1×Y_2, whereas that theorem assumes B separated. For example, take Y_1 to be the affine line with doubled origin, f_1=id, and Y_2=Spec(k), f_2=id. These satisfy the item's hypotheses, while B is not separated, so that particular theorem cannot be instantiated. This is a type/domain check, not a counterexample to the locality conclusion.

The corrected item explicitly types K in Dctf(Y,A) and Q in Dctf(Z,A), and writes the compactification formula for the identity-second-factor Ku_!: inverse PF followed by inverse compact-support exchange. These are precisely the component maps in the imported formula. The concrete finite projection theorem and arbitrary-base-change compact-support theorem allow this formula on the original nonseparated domain. No separatedness hypothesis was added, no case discarded, and no conclusion weakened. The phrase about not assuming invertibility now explicitly refers to the two alpha maps, so it cannot be confused with the restriction isomorphism already asserted.

## Proof and searches

The source read for the item is literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/sk-thm-sf-kunneth-verdier.proof.md, its alpha paragraph: affine factorization gives the local comparison, and exceptional pullback commutes with etale restriction compatibly with alpha. I also read the current imported relative-product formula and the statements of every cited node. For the constructibility input I checked Stacks Tag 095F, etale-cohomology.tex, lemma-constructible-local, and its proof at lines 11789–11804: it is Zariski local constructibility; the Tor assertion comes from the separate existing finite-cover node, not from that tag.

The new Q32 searches included LeanFinder for exceptional open restriction and for compact-support projection/open compatibility, LeanSearch for finite-cover uniform Tor amplitude, Loogle for conjugateIsoEquiv, and msearch grep in Mathlib/CategoryTheory. Their actual results are recorded. The first Loogle query mixed names with the words “exceptional inverse image” and was rejected with unknown identifier exceptional; it is explicitly recorded as an invalid query and is not evidence of absence. The valid replacement returned generic adjoint conjugacy. LeanFinder returned structure-sheaf restriction/section identities; LeanSearch returned topological constructibility and scheme finite-subcover results. None is a one-line instance proving this geometric derived exceptional statement. The generic adjoint-composition tool is already a Mathlib leaf in the DAG, so it was cited rather than duplicated.

## Not duplicates

No new node was created. The two initially tempting nodes, open restriction and finite-cover constructibility/Tor gluing, already have useful generic ingredients. In particular lem-sf-finite-cover-ctf-locality states the entire finite-cover gluing tool. cor-exc-base-change-open-immersion-general was read but was not used as a theorem about arbitrary commuting squares: it requires a Cartesian square. lem-sf-kv-shriek-composition and lem-sf-kv-alpha-transpose-coherence were also inspected but their separated-scheme domain was not silently enlarged. The blueprint search “open restriction exceptional” found no duplicate blueprint node. Generic off-unit tools are declared, with their specific purpose, in split_report.tool_uses.

## Review by Q32

I read the item against the alpha paragraph of the current blueprint, not the older snapshot, and checked delivery-errors B–E with the node files open. There are no new statements, so the new-node requirements on complete statement-only leaves, sources, independent searches, duplicate/tag pairs, and small-case testing introduce no additional files. The item's proof is marked agent-written because the expanded calculation is not quoted from a published proof. Each step below has its cited statements copied into citations.json; I checked the uses against those statements, rather than taking facts from their proofs.

1. The finite-type-over-Noetherian theorem applies with Spec(k); the open-Noetherian theorem supplies quasi-compactness, and the definition of finite type then types the open restrictions. Nagata supplies the compactifications needed by the ordinary-etale-adjoint theorem. These results do not require the schemes themselves to be separated over k. The operations node is used for the bounded-below finite construction, not for an ambient pro-etale right adjoint.

2. lem-amb-etale-adjoint-locality explicitly gives the ordinary-etale open derived adjunction. lem-amb-etale-compact-comparisons explicitly gives the associative compact-support composition isomorphism. The six displayed Hom bijections consequently apply to the square fu=vf' without any Cartesian assumption. The existing Mathlib adjoint-composition leaf states that the counits paste. I wrote the resulting counit equation explicitly: it is the normalization needed later, rather than a bare claim that some isomorphism exists.

3. I expanded the definition with the second factor the identity. thm-cbc-finite-torsion allows any base-change morphism, including a nonseparated product projection, and fix-prop-projection-formula is about the actual operation datum, not the axiom package def-sf-datum. The flat-model theorem and the derived-pullback theorem preserve the model's length and flat terms. The two constructible-pullback statements give the pulled-back strata and constant modules. These check the finite-Tor and constructibility domains of the projection factor. This repairs the imported separated-base reference instead of adding separatedness to the item.

4. The proper ringed exchange/tensor statement contains exactly the proper equation used here, and lem-asd-open-projection-exchange contains exactly the open equation, on ordinary-etale unbounded categories without separation assumptions. Substituting the latter into the former after naturality is a direct paste of two equalities; this is why this step alone is marked elementary. Compact-support exchange's horizontal pasting identifies the remaining exchange factor for the product projection. I did not cite a definition as a theorem asserting this coherence.

5. The open-tensor-normalization statement identifies its actual maps by the open units; the etale/pro-etale comparison statement supplies the equality between the corresponding tensor maps. The projection theorem states composition coherence, and the compact-support theorem states vertical exchange pasting. Substitution in the formula of step 3 cancels the open factors and gives the displayed source-extension identity. This is a left-functor calculation, not an assumption of the alpha restriction claim. Compact-support composition is used on its bounded-below ordinary-etale domain. I also checked that open extension retains the input domain: the strata extend by the zero stratum on the complement, and the open tensor formula with exact extension/restriction preserves the same Tor interval.

6. I read sk-def-sf-kv-maps(ii): it really says alpha is the exceptional transpose of Ku_! followed by the exceptional counits. Naturality moves the open counit through t_f, step 5 identifies the resulting left comparison, and the equation already proved in step 2 identifies its remaining counit. The mate-pasting statement supplies composition of the transposes. Injectivity here is the adjunction bijection, not faithfulness of restriction on arbitrary derived morphisms.

7. This is the Cartesian target-open case, where compact-support exchange is applicable. I wrote the counit/exchange equation, checked its open-adjunction transpose against step 2, and then calculated the transpose of the restricted alpha. Step 4 handles the Ku_! factor and the same counit equation handles the epsilon factor. All product opens are actual pullbacks. The statement of the exchange theorem supplies naturality and identity normalization; the mate-pasting theorem applies to the two composite adjunctions. Thus the proof identifies the specified map, without assuming alpha invertible.

8. An arbitrary commuting square factors through X_V because the image of W lies there; W is still an open subscheme of that open. The already proved target and source cases therefore cover the original square. Associativity and the pasted-counit property show that the comparison used is the same one as step 2. The finite operation node defines the transport, and the comparison-open-tensor equality identifies the maps transported. This avoids extending an etale-origin adjunction to the whole pro-etale derived category.

9. The finite-cover node assumes a Noetherian topology; I supplied the ascending-chain argument from quasi-compactness of every open. Its statement gives global constructible strata and exactly the supplied Tor interval. It does not on its own give an arbitrary independent cohomological interval, so I separately checked that exact open restriction identifies cohomology sheaves, and the sheaf axiom detects their vanishing. Hence the two global bounds need not coincide. Empty X and an empty covering give the zero category, without undefined extrema; singleton covers and different overlapping intervals give exactly the asserted containing intervals.

10. The integral assertion is about the normalized construction's uniform reduction bounds. The operations statement specifies that construction; derived-complete-integral-detailed explicitly requires one cohomological interval independent of n, and the finite-Tor definition requires one Tor interval for all finite reductions. Taking extrema over finitely many charts preserves independence of n, so step 9 applies with those exact intervals at every level. No equality of integral maps was inferred merely from separately equal reductions, and no unspecified tower was reconstructed.

The draft's incorrect use of Cartesian base change for a merely commuting square was removed. Its vague “naturality of alpha” was replaced by the two explicit transpose calculations. The extra definition of a bounded-constructible complete category was removed in favor of the exact integral category used by the statement. All ten steps are shorter than 2000 characters; I also inspected the two comparison calculations for hidden facts and cited their explicit factor identities, composition and exchange-pasting statements. The proof contains no SGA route, no new axiom, no new node restating a clause, and no unproved claim of alpha invertibility. Custom read-only dependency traversal found no path from the generic tools back to this item; the required server checks remain the authoritative validation.

## Unfinished work

None in the stage-1 split. There is no Lean implementation in this delivery. The stage-1 split and the Q32 review are complete.
