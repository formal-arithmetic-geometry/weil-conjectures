# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-log-structure-fixed-scheme-enhancement.json`: existing statement, now split into four steps; no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node citation.
- `searches.jsonl`: the required search command's actual search records.
- `report.md`: this report.

New nodes: 0. Mathlib leaves: 0. No Lean files, compilers, Lake commands, repository writes, or direct git commands were used.

## Attachments

None. Searched the project source under `lean/WeilConjectures/` for the blueprint id, LogStructure, FineLogScheme, fine log, and logarithmic structure: no declaration stating the item was found. Existing sorry declarations would not qualify as attachments.

## WANTED

None. The ILO PDF and Stacks source needed here are present.

## Findings and changes

The statement is sound and unchanged, including the locally Noetherian conclusion, the prescribed underlying scheme and morphism, the compatibility with every given identification, and the conditional fs conclusion. Its six statement dependencies are unchanged. The initially empty proof is replaced by an assembly proof using two existing reviewed nodes. No new node is needed: creating another log-gluing or Noetherian-descent lemma would duplicate existing statements.

The essential source-type check is that the raw inverse image `f^{-1}M_S` need not be a log structure for the pulled-back ring. The existing `lem-trf-fine-log-structure-etale-descent` expressly allows arbitrary monoid sheaves, including inverse-image monoid sheaves, in its morphism clause. Step 3 uses that clause, with the composite map to the structure sheaf, and does not apply its log-structure existence clause to this source. The overlap identity is written out, including the direction of the transition isomorphism.

Read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md` and its unit/chapter. This item's log descent is an inherited supporting construction, rather than a statement repeated in that latest blueprint proof. The split preserves its existing ancestor and via chain, and leaves the chapter and unit unchanged. Whole-blueprint searches for `log structure`, `fine log`, `logarithmic`, and `glue sheaves` found no matching statement: the logarithmic hits concern zeta derivatives. Whole-DAG title and statement searches found both reusable lemmas and their definitions. Both lemmas have the item's unit `sk-i-curve-zero`, so no off-unit tool exception is needed.

The item was searched with the mandated msearch command using LeanFinder, Loogle, LeanSearch, and Mathlib grep, and then a second semantic phrasing and second grep. Read every returned hit. The hits concern ordinary etale categories/properties, Zariski gluing of schemes/ringed spaces, section gluing for an already existing sheaf, or module presentations. None constructs a logarithmic enhancement or states the whole item. Exact query text and the command's output summaries are recorded without inventing queries or treating unavailable services as negative searches. The item retains its earlier recorded searches as well.

## Not duplicates

No new nodes. `lem-trf-etale-local-noetherian-descent` is reused for descent of the underlying property. `lem-trf-fine-log-structure-etale-descent` is reused for both descent of the log structure and gluing of homomorphisms between arbitrary monoid sheaves. The present item additionally assembles the specified relative log morphism over the fixed scheme map; that assembly is proved here.

## Review by Q20

I read ILO Expose VI 1.1, printed p.69 (PDF page 75), which defines fine versus fine saturated by etale-local charts and states the locally Noetherian convention; VIII 3.3.4(ii) and 3.3.8, printed p.107, where strict etale charts and their descent are used; and p.108, which distinguishes saturation. I also read Stacks `descent.tex`, Tag 034C, label `lemma-Noetherian-local-fppf`, and `sites.tex`, Tag 04TQ, label `lemma-glue-maps`, and Tag 04TR, label `lemma-glue-sheaves`. The PDF invokes descent rather than spelling out this relative assembly; accordingly `proof_origin.by` is agent. No SGA source is used.

For Step 1 I opened `lem-trf-etale-local-noetherian-descent` and read its statement: it requires a jointly surjective etale family with locally Noetherian sources and concludes the exact needed property of the target. All hypotheses are explicitly present in this item. This is a theorem citation, not an inference from the definition of Noetherianity. It also puts the locally Noetherian hypothesis in place before the log-structure convention is applied to X.

For Step 2 I opened the entire statement and proof of `lem-trf-fine-log-structure-etale-descent`. Its existence clause takes the same structure-map-compatible transitions on the actual double overlaps, with the same cocycle and diagonal normalization, and returns identifications satisfying `e_b = phi_ab e_a`. Its final sentence in that clause gives precisely the conditional fine saturated charts. The source schemes need only be fine, and no saturation is silently imposed. The new proof cites this existing result rather than reproducing a clause of the item as a new node.

For Step 3 I read the relative-test description in `def-trf-fine-log-scheme-morphisms`, and the full moreover clause of the descent lemma. The fixed underlying map of each f_a is f p_a, so its source is the restriction of the same inverse-image sheaf A. Each e_a preserves structure maps. Thus u_a = e_a^{-1} f_a^flat has the required common source and structure map, and on overlaps the given equation f_b^flat = phi_ab f_a^flat and the established equation e_b = phi_ab e_a give equal u_a. The cited moreover clause really states gluing for arbitrary monoid sheaves over O_X, not merely for fine log structures or over a different ring. That is why it applies to A. This step uses no unstated effective descent of schemes, charts, or line bundles.

For Step 4 I read the morphism definition in `def-trf-fs-log-blowup`: a scheme map together with exactly such a structure-preserving homomorphism is a log morphism. Pairing f with u is therefore elementary. Its restriction equation is checked explicitly by cancellation of e_a^{-1}; it does not follow from an unproved assertion that maps transport. The conditional fs assertion was already supplied in Step 2. All citation quotations were checked as literal substrings of the cited statements.

I checked the empty-scheme/empty-cover case (joint surjectivity forces X empty when the cover is empty), an identity cover, repeated cover members, nontrivial transitions, and trivial log structures. None requires a nonempty cover, a global chart, a Zariski chart, separatedness, or a finite cover. The fine but nonsaturated case is retained, and the fs conclusion is conditional on fs charts on every cover member. There are no new statements needing separate small-case tests. All non-elementary facts in the assembly have node citations; the last step is only the stated definition and the written restriction equation. Every step is below 2000 characters. No statement dispute, source correction, or unresolved mathematical issue remains.

## Unfinished work

None in the stage-1 split. Independent maintainer review and subsequent formalization remain the project's later work.
