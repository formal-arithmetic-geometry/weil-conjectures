# Stage-1 report: lem-sfb-weakly-etale-normal-ring-ascent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-weakly-etale-normal-ring-ascent.json: statement, split into four proof steps; no Mathlib match after logged LeanSearch, Loogle, two LeanFinder formulations, and two source grep searches.
- citations.json: five verbatim statement quotations, one for each step/node citation.
- report.md and searches.jsonl: review and actual search records.

No new nodes; zero new Mathlib leaves. No Lean files written, no compilation, and no repository writes or git commands.

## Attachments

None. The blueprint-tag search in lean/WeilConjectures found no item declaration. The concept search found Algebra.WeaklyEtale.isDomain_localization_of_isIntegrallyClosed, WeilConjectures/RingTheory/ProEtale/RegularLocalization.lean:149. I read its statement and body: its conclusion is only IsDomain of each target localization, not integral closedness, so it is not an attachment. The pointwise etale theorem in RingTheory/Etale/IntegrallyClosedLocalization.lean supplies the etale special case only. The existential refinement theorem is already represented by lem-weil-pbc-existing-weakly-etale-indetale-refinement, and was reused without a new attachment claim.

## WANTED

None. The combined result is derived by the recorded four-input argument, so proof_origin.by is agent. All four individual input sources are present in literature/stacks-project.

## Problems found and changes

The imported item had an empty proof; its statement is correct and retained byte for byte, including the unrestricted ring and universe clauses. Its source correctly warns that Tag 097Z alone does not assert the result. The proof now states the entire combination instead of attributing ascent to 097Z.

The inherited blueprint chain has null from.node: blueprint_refs.py ancestor confirms None. I retained this inherited metadata, including its precise Paragraph (3) open-direct-image place and via chain. The item is a supporting algebra lemma for weakly etale root-limit normal charts, not the key node of sk-thm-sf-ctf-stability, so no unit realization fields were touched. Whole-blueprint queries for weakly etale, normal, normal ring, colimit normal and weakly etale normal found no imported node giving this exact assertion. The exact general filtered-colimit theorem, the etale ascent theorem and the faithfully flat descent theorem already exist and are reused.

Off-unit generic tools are declared in split_report.tool_uses: the existential refinement, etale normality ascent and filtered-colimit normality. They implement the inherited ring-theoretic route without replacing a unit-level step. The normality descent node is in the item's own unit.

## Unfinished

Nothing in the requested stage-1 split remains unfinished. The referenced existing nodes retain their own independent proof obligations; this delivery does not claim a Lean proof of the item.

## Not duplicates

No new nodes. Searching tags 097Z, 033C, 037D and 033G and titles/concepts across the whole DAG found the precise reusable inputs. In particular, I reused the same-unit lem-sfb-faithfully-flat-normal-ring-descent rather than creating another copy of it or of lem-per-faithfully-flat-normal-ring-descent. The existing etale-colimit-normal-local-domain node assumes a domain base and a local colimit, so it is not the arbitrary-ring theorem needed here; the full filtered-colimit-normal-ring node is used instead.

## Review by Q157

I read Stacks proetale.tex Tag 097Z, label proposition-weakly-etale, including its proof: it produces B to C faithfully flat and ind-etale with A to C ind-etale, and does not assume A normal or f faithfully flat. I read algebra.tex Tag 033C, label lemma-normal-goes-up, including the arbitrary-base reduction after the Noetherian case; Tag 037D, label lemma-colimit-normal-ring, including localization at a prime and the normal-domain colimit argument; and Tag 033G, label lemma-descent-normal, including the faithfully flat local reduction and principal-ideal membership descent. There are no new-node sources to audit. I also read the chapter, unit route and the current root-limit-normal-charts source/proof context.

For step 1 I opened the full statement of lem-weil-pbc-existing-weakly-etale-indetale-refinement. It provides exactly a refinement ring, a faithfully flat map and the ind-etale composite. Its common-universe qualification is met by placing both rings in a containing universe; a lift is a ring isomorphism, carrying primes and localizations and their monic equations, and preserving the tensor-module flatness conditions. No size assumption is imposed on the mathematical rings. This is elementary bookkeeping within the step, not a new algebraic lemma.

For step 2 I read the statement of def-weil-pbc-ind-etale-algebra, which explicitly gives a filtered-colimit presentation by finitely presented etale algebras, and lem-weil-pbc-etale-over-normal-ring-normal, which applies to arbitrary commutative normal base rings and proves full normality of the target. The diagram is small in the chosen containing universe. Thus the etale input's only normality hypothesis is satisfied by A. I did not use the weaker domain-only project declaration or assume that a normal ring is a domain.

For step 3 I read the full statement of lem-weil-pbc-filtered-colimit-normal-ring. It accepts an arbitrary small filtered category and normal ring terms, with no transition-map condition. These are exactly the diagram and termwise conclusions of step 2. Normality passes across the displayed colimit isomorphism by the same prime-local description. The source Tag 037D is directed-system form; the existing node explicitly includes filtered categories, with its directed-category comparison source, so no unrecorded comparison theorem is needed in this item.

For step 4 I read the full statement of lem-sfb-faithfully-flat-normal-ring-descent. It assumes only faithful flatness and normality of the target. Both hold for B to C by steps 1 and 3; it concludes the precise prime-local domain and integral-closedness clauses for B. No Noetherian, locality, finite-presentation or domain hypothesis has slipped into the assembly. The citations file copies these five statements verbatim, and a local string-membership check passed for every quote.

I checked B=0 (no primes), A=0 (unitality forces B=0), identity maps, projections from a product k times k to a factor, and localization maps such as Z to Q. The latter tests show why f itself need not be faithfully flat; the refinement map is the one to which descent is applied. Disconnected normal products are handled by the actual arbitrary-normal-ring statements of the inputs. Non-Noetherian normal rings and noninjective colimit transition maps remain permitted. Every step is under 2000 characters, and the full assembly is under 3000; no long inline lemma is hidden. I checked C1/C4 by reading cited statements, C6 by using downstream algebra tools with no dependency on this item, D1/D2 by creating no restatement nodes, B1-B10 by retaining the schema and authentic logged searches, and E1-E7 against the source hypotheses and small cases above. The statement needs no dispute or correction.
