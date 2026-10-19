## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-quasi-excellent-nagata.json`: statement, split into eight steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-regular-map-reduced-target.json`: new statement-only node, unsplit; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-universally-japanese-n1-criterion.json`: new statement-only node, unsplit; no Mathlib match.
- `citations.json`: 25 entries, one for each node used by each numbered step, quoting the statement read.

The sandbox also contains the search command log, raw search results, and item-specific preparation scripts. These are supporting files, not proposed project files. Two new nodes, zero new Mathlib leaves. The required delivery dry run is the validation; nothing is pushed by this worker.

## Attachments

None. Searched `WeilConjectures/` in slopmaster2 and the read-only upstream master for the blueprint tag, quasi-excellence, Japanese/Nagata rings, the regular-map reducedness assertion, and the N-1 criterion. The quasi-excellence occurrence is explanatory text in `SixFunctors/Etale/Derived/Stability.lean:174`. The regular/reduced hits concern smooth schemes over fields, not arbitrary regular maps of Noetherian rings. None states this item or either new node under the required hypotheses. The upstream sorry declarations were not treated as proofs.

## Literature wanted

WANTED: `literature/stacks-project/more-algebra.tex`, Tag 07QV, `lemma-quasi-excellent-nagata`, for lem-exc-quasi-excellent-nagata.

WANTED: `literature/stacks-project/more-algebra.tex`, Tag 07QK, `lemma-reduced-goes-up`, for lem-exc-regular-map-reduced-target.

WANTED: `literature/stacks-project/algebra.tex`, Tag 0351, `lemma-check-universally-japanese`, for lem-exc-universally-japanese-n1-criterion.

The local Stacks and blueprint source directories are absent in this shared checkout. I read the Stacks assertions and proofs online at https://stacks.math.columbia.edu/tag/07QV, https://stacks.math.columbia.edu/tag/07QK, and https://stacks.math.columbia.edu/tag/0351, and checked the TeX labels in the Stacks source. I also read the statements/proofs of 0333 and 032Y, which explain the local-to-global reduction. No literature file was written. In accordance with the missing-local-document rule, the item's `proof_origin.by` is `agent`.

## Faults and corrections

No statement dispute: the imported conclusion agrees with 07QV and includes precisely quasi-excellence, without a dimension, domain, locality, or catenarity hypothesis. The node was unsplit; its statement and statement dependencies remain unchanged.

The argument avoids claiming that the existing excellent finite-type-localization lemma also states quasi-excellent stability: it states excellence only. Instead step 1 uses the existing finite-type G-ring theorem and step 2 uses the J-2 quantifier directly on the finite type algebra. This proves exactly the portion of 07QU required here, without introducing a duplicate quasi-excellence stability node.

Two localization nodes that were inspected concern only a base already of the form R_p, not an arbitrary principal localization S_f. They are not cited. The proof instead uses the arbitrary-localization spectrum embedding for contraction and writes both fraction maps identifying (S_f)_Q with S_p. This corrects a potential C4 mismatch before delivery.

Preliminary source grep invocations used an extra `Mathlib/` directory component; their empty results are not used to infer absence. Fresh searches used the valid `RingTheory` subdirectory. The node records contain those actual successful results. LeanSearch returned HTTP 500 and is recorded as unavailable, not as absence.

## Unfinished work

None within this one-level stage-1 split. The two new supporting statements deliberately have no proof and no proof dependencies. They are the smaller next items, not assertions that quasi-excellent rings are Nagata in different words. No Lean was written or compiled, and no direct git command or project write was made in either read-only project.

## Not duplicates

There is no existing node whose source carries 07QK or 0351. I searched the whole DAG for those tags and for reduced/regular maps, universal Japanese/N-1 criteria, finite normalization, and quasi-excellence, and searched the whole blueprint with `tools/blueprint_refs.py search` (including 07QK, 0351, regular reduced, universally Japanese N-1, and quasi-excellence phrasings). Neither new assertion has a blueprint equivalent; `same_as` is empty.

lem-exc-universally-japanese-n1-criterion vs lem-weil-pbc-nagata-universally-japanese: the existing statement assumes R Nagata; the new statement assumes every finite type domain algebra is N-1 and has no Noetherian hypothesis on R. Applying the existing statement here would assume the desired conclusion. The new criterion is 0351, while the existing Nagata-to-universally-Japanese direction is 0334.

lem-exc-regular-map-reduced-target vs lem-weil-pbc-serre-criterion-reduced: the existing statement characterizes a single Noetherian ring by (R_0) and (S_1); it does not assert ascent along a regular map. The latter is the genuinely additional content of 07QK. It is not obtained by merely unpacking that characterization.

The existing local N-1 characterization, analytically unramified N-1 theorem, finite-type G-ring theorem, completion Noetherian theorem, field regularity, localization Noetherianity, and regular-implies-normal theorem are reused. No duplicate nodes were created for any of them.

## Review by ND

I read 07QV (`lemma-quasi-excellent-nagata`) against the unchanged item: its base is a commutative quasi-excellent ring, not necessarily a domain or local, and its conclusion is Nagata. The proof reduces to finite type domains via 0351, uses the J-2 regular open and 0333, and makes the local completion reduced using 07QK before applying 032Y(5). These are the route and hypotheses implemented here. The blueprint ancestor is `lem-exc-punctured-curve-branches`, whose first proof sentence says “Excellence implies the Nagata property”; the new nodes' `via` lists contain the current item. This is a generic algebra input to branch normalization in the Kummer unit, not a replacement of a cohomology step. The off-unit algebra tools are declared individually in `split_report.tool_uses`.

For step 1 I opened the statements of the excellent-ring definition, finite-type definition, finite-type-over-G-ring theorem, and G-ring definition. They supply respectively R Noetherian and G, the exact finite-type hypothesis of the theorem, S G, and S Noetherian. The step quantifies over all finite type domain algebras, not just quotients or integral algebras. For step 2 the J-2 clause explicitly quantifies over precisely this S. The field-regularity node explicitly includes regular locality in dimension zero. Identifying S_(0) as its fraction field is the displayed fraction construction, and choosing f in the ideal defining the closed complement is an elementary Zariski-topology argument; neither generic smoothness nor an openness-of-normal-locus theorem is assumed.

For step 3 I checked the localization Noetherian statement against the actual powers-of-f multiplicative set; its units, fractions and kernel conditions hold by the localization definition cited. The spectrum-embedding statement is for an arbitrary multiplicative set and does give f outside the contracted prime. It is not cited for an isomorphism of local rings: the two inverse maps are written explicitly, with b and f outside that prime. The regular-ring definition then applies to every prime of S_f, and the regular-implies-normal node says exactly that such a Noetherian regular ring is normal. Thus the principal-normal hypothesis later used is established, rather than inferred merely from an open regular locus by an unquoted theorem.

For step 4 the localization-at-prime definition supplies the local ring and its actual maximal ideal mS_m. I checked domainhood directly using the fraction zero criterion; in particular there are no zero denominators and 1 remains nonzero. The G-ring definition is applied to S and its prime m, giving exactly S_m to its mS_m-adic completion, not completion of S at m or a residue field map. The completion-Noetherian node applies to this Noetherian local source with that ideal. Only after checking both source and target Noetherianity does the new reduced-ascent node apply. For step 5 the analytically-unramified N-1 node explicitly assumes a Noetherian local domain and reduced maximal-adic completion and concludes N-1; all those hypotheses were supplied in step 4.

For step 6 I read the full statement of the existing N-1-local-characterization node: it needs both a normal localization at one nonzero f and N-1 at every maximal localization. Steps 1–5 supply all of these, including Noetherianity of the domain. Its conclusion is finiteness of normalization in the same fraction field, precisely N-1. For step 7 the new 0351 node has exactly the universal hypothesis established in step 6. For step 8 the universally Japanese definition gives N-2 for R/p because its quotient map has zero algebra generators; R was already Noetherian. Those are the Nagata definition's two clauses. This last step is marked elementary because it only specializes the universal quantifier and unfolds the cited definitions.

For the new reduced-ascent node I read 07QK's full statement and its proof using ascent of (S_1) and (R_0). Both rings are Noetherian, the source is reduced, and the map is regular; none of these hypotheses was dropped. Reduced means every nilpotent is zero and is defined inline, while regular is the ring-map notion of the cited G-ring definition, not regularity of an element or of one ring. For the new N-1 criterion I read 0351's full statement and finite-extension argument: for a finite field extension L/Frac(S), choose a finite integral S-subalgebra S' of L with fraction field L, apply N-1 to S', and use transitivity of finite extensions and of integral dependence. This is why the universal finite-type-domain hypothesis is sufficient without assuming S normal or the field extension separable. Neither new node has proof steps, proof dependencies, or a sketch hidden in its statement; each introduces its own rings, hypotheses and notions and gives its precise Stacks tag and TeX label.

I tested the small cases and the hypotheses that are easy to confuse. For a field-domain S the regular locus is all of Spec(S), so f=1 works, its maximal localization is the field itself and its zero-adic completion is itself. If R is the zero ring there are no unital maps to nonzero domains and no prime ideals: the universal property and the Nagata quotient condition are both vacuous, with Noetherianity still supplied. The regular-map assertion allows the zero ring: a unital map from zero forces its target to be zero. Removing regularity would be false: the flat map k to k[epsilon]/(epsilon^2) has reduced source and nonreduced target; its fibre is not geometrically regular, so the stated hypotheses correctly reject it. The identity on this nonreduced ring similarly shows why source reducedness matters. The N-1 criterion handles degree-one extensions without assuming normality; for arbitrary finite extensions its S' construction includes inseparable extensions, so a separability restriction would be a defect.

I ran and read two semantic phrasings for each new assertion, Loogle and source grep, with queries and raw results retained in each node and the command log. The tempting `IsIntegralClosure.finite` was checked in `DedekindDomain/IntegralClosure.lean:150–180`: it assumes an integrally closed Noetherian base and a separable field extension, so it does not imply 0351 in one line. The reduced tensor-product candidate was read in `Flat/Basic.lean:638–661`: its hypothesis is reducedness for tensor products with every finitely generated subalgebra, not regular fibres, so it is not 07QK. No new Mathlib leaf is claimed. Dependency traversal found no path back to the item from any reused substantive theorem; the dry run also checks the full overlaid DAG. Every cited node's statement was opened, and the 25 citation quotes are verbatim copies of those statements. This review checks B1–B10, C1–C8, D1–D5 and E1–E7 against these particular files and sources; the substantive corrections above remove the excellent/quasi-excellent and prime/principal-localization mismatches.

## Second reading by ND

- Item statement: checked against Stacks Tag 07QV (`lemma-quasi-excellent-nagata`); PASS, with exactly the quasi-excellent hypothesis and Nagata conclusion.
- Step 1: checked against the excellent-ring, finite-type algebra, finite-type-over-G-ring, and G-ring node statements; PASS, including the domain and finite-type hypotheses.
- Step 2: checked against Tag 07QV and the J-2 clause, field regularity, affine-spectrum topology, and the closed-subset description in `lem-weil-pbc-spec-irreducible-closed-subsets-primes`; PASS.
- Step 3: checked against the localization, spectrum-embedding, regular-ring, and normality statements; PASS, with the fraction maps written explicitly.
- Step 4: checked against localization, G-ring completion, completion-Noetherian, and reducedness-ascent statements; PASS, including the exact maximal-adic completion.
- Step 5: checked against Tag 032Y and the analytically-unramified N-1 statement; PASS.
- Step 6: checked against Tag 0333 and the N-1 local characterization; PASS, including the nonzero principal localization and all maximal localizations.
- Step 7: checked against Stacks Tag 0351 and the new universal-Japanese criterion node; PASS, with the universal finite-type-domain quantifier unchanged.
- Step 8: checked against the finite-type, Nagata, and quasi-excellent definitions; PASS, with the quotient maps having zero generators and Noetherianity supplied.
- New node `lem-exc-regular-map-reduced-target`: checked hypothesis by hypothesis against Tag 07QK; PASS, self-contained and statement-only.
- New node `lem-exc-universally-japanese-n1-criterion`: checked hypothesis by hypothesis against Tag 0351; PASS, self-contained and statement-only.
- Mathlib searches: independently checked the recorded LeanFinder/Loogle/grep searches and the unavailable LeanSearch entries; PASS, no Mathlib leaf.
- Small cases: field, zero ring, degree-one extension, and the nonregular dual-number map were checked; PASS.
- Changes: added the existing closed-subset-of-`Spec` node to step 2 and `proof_deps`, added its verbatim citation quote, and appended this independent second-reading audit. The original worker sections, including `## Review by ND`, remain intact. No statement or new-node content changed; two new nodes and zero Mathlib leaves remain.

Second-reader source check: the local literature files are indeed absent. I downloaded and read the exact TeX lemma/proof blocks from the Stacks source into sandbox-only `second-reader-more-algebra.tex` and `second-reader-algebra.tex`, including labels lemma-quasi-excellent-nagata (07QV), lemma-reduced-goes-up (07QK), lemma-check-universally-japanese (0351), lemma-characterize-N-1 (0333), and lemma-analytically-unramified-easy (032Y). These supporting extracts are not project changes. The source statements agree with all ring, Noetherian, regular-map, reducedness, and universal finite-type hypotheses in the JSON. No statement dispute was found.

I independently ran `msearch.py` with “Flat algebra over a reduced ring with reduced residue field fibres is reduced” and “Finiteness of integral closure in all finite field extensions from finite normalization of every finitely generated domain algebra”. Actual query records and results are appended to the two new nodes and searches.jsonl. I read the candidate declarations in Flat/Basic.lean:638–661 and DedekindDomain/IntegralClosure.lean:147–180: the former assumes reduced tensor products for all finitely generated subalgebras, the latter assumes normal Noetherian base and a separable field extension. Neither states the new assertion. The reducedness ascent needs the non-elementary ascent of Serre conditions; 0351 needs the finite intermediate algebra with the prescribed fraction field and integral-closure transitivity. Neither new node is an elementary unfolding, a duplicate, or a restatement of quasi-excellent implies Nagata. Fresh whole-blueprint searches for “universally Japanese” and “reduced regular” returned zero matches; the ancestor command confirms lem-exc-punctured-curve-branches. Searches of the two read-only source repositories found no relevant declaration to attach.

The revised citations.json has 26 entries, one per step/node pair; I checked each quotation against the current cited statement and checked proof_deps equals the union of uses. The original eight proof steps and both new statements are preserved except that step 2 now explicitly attributes the closed-set formula to its added existing node. split_report.tool_uses retains the worker's generic-tool requests as expressly permitted by SETUP.md's fourth human decision; these are requests for the maintainer's judgment, not top-level approvals.

Delivery syntax note: this installation of deliver.py accepts the group and item only, with optional --no-push. The literal trailing dot in the brief prints usage, so the required checks use the tool's documented syntax without that dot. The first completed dry run printed OK at 41aee2ad51. A final dry run follows after the search and source audit additions.

Concurrent-base repair after the final dry run: the push citation check found three stale quotes for def-exc-excellent-ring. I reopened its newly merged statement and Q44 report. The changes add its localization-at-prime reference and explicitly scope universal catenarity to Noetherian rings; the Noetherian/G-ring/J-2 hypotheses used in steps 1, 2 and 8 are unchanged. Updated those three verbatim quotes from the current node. No proof or mathematical statement change is forced. Repeating the required dry run and delivery on this repaired citation set.
