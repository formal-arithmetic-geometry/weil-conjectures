# Stage-1 report: lem-a1-etale-atlas-presentation

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-etale-atlas-presentation.json: existing statement node, now split into five steps; not a Mathlib leaf. Its statement is unchanged. Added the scheme fibre-product notion to stmt_deps. Preserved the original search results and all maintainer metadata.
- citations.json: one entry for each of the eleven step/node citations, quoting the cited statement verbatim.
- searches.jsonl: fresh msearch results for the item, retained as generated. The earlier item's recorded searches were also read and retained.
- report.md: this report.

No new nodes, no new Mathlib leaves, no unit edits, no Lean edits or compiler runs.

## Attachments

None. Searched WeilConjectures/ in the designated slopmaster2 source for the exact blueprint tag and for etale-atlas/algebraic-space/kernel-pair/quotient terminology. No project declaration states all the clauses. The upstream master checkout is not being treated as a completed proof.

## WANTED

None. All sources needed are available in literature/stacks-project/.

## Problems found and changes

The statement is correct. The unsplit item already had meaningful Mathlib searches; the matching hits concerned scheme etale categories, scheme gluing, locally ringed-space coequalizers, or general sheaf effectiveness. None provides the algebraic-space atlas presentation in one specialization. Fresh LeanFinder searches with two phrasings, LeanSearch, Loogle and grep agreed. The general sheaf theorems already have DAG Mathlib leaves, so I reused those instead of creating new nodes.

The proof makes the distinction between a surjective scheme-test atlas and an epimorphism of sheaves explicit: the former supplies the fppf local lifts; only then is the epi/local-surjectivity theorem applied. It also expands the equivalence between the source's coequalizer formulation and the item's specified sheafification of the sectionwise quotient. No hypothesis, conclusion, definition, unit route or statement was changed.

The generic fibre-product node lem-trf-space-fibre-products-etale-covers belongs to another unit. It is declared in split_report.tool_uses: it supplies the representability interface already named by the item; it does not replace any step of the rank-bound unit. All other theorem citations are existing Mathlib leaves or definition nodes.

## Unfinished work

None in the one-level split. Existing cited nodes retain their own statuses and ownership.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for Tag 0262, atlas, equivalence relation, sheaf quotient, coequalizer, surjection and sheafification found the existing generic sheaf inputs. The item is not a duplicate of a blueprint node. No new theorem packages a clause of this item.

## Review by NZ

I read spaces.tex, Tag 0262 (lemma-space-presentation), including its complete proof and the following explanation of the quotient formulation. I checked the definition of algebraic spaces and representable surjective etale maps against the actual statement of def-trf-algebraic-space (source Tag 025Y). For the local covering assertion I read topologies.tex, definition-fppf-covering (Tag 021L); for the sheaf step I read sites.tex, definition-sheaves-injective-surjective (00WM), lemma-mono-epi-sheaves (00WN), lemma-coequalizer-surjection (086K), and proposition-sheafification-adjoint (00WH). There are no new nodes requiring separate source reviews. I read the chapter and rank-bound unit records, the current main-20261015 ancestor text and the item's ancestry: this auxiliary presentation argument supplies the recorded 03BZ/03XW branch of the support argument, without changing the chapter or unit route.

Step 1 uses the actual statement of lem-trf-space-fibre-products-etale-covers for the sheaf fibre product and its scheme case: both factors are U and the map U to X is representable etale. It uses lem-weil-pbc-site-sheaf-sets-limits-sectionwise only for a finite pullback, so its small-index hypothesis holds. That statement explicitly identifies the sheaf limit with sectionwise limits. def-pc-fibre-product gives the ordinary universal property identifying (U times_S U)(T) with U(T)^2. The reflexivity, symmetry and transitivity are the three properties of equality of p-images; no geometric separation assertion is being smuggled in.

Step 2 cites def-trf-algebraic-space, whose statement explicitly defines both etale and surjective representable maps by all scheme pullbacks. Applying that test with T=U gives one projection R to U, and interchanging the pair gives the other. Thus no uncited base-change theorem is needed: this is an instance of the definition in force, not an invocation of a theorem about arbitrary nonrepresentable maps. Surjectivity does not require p to be injective; the diagonal pair (a,a) also supplies a section of either projection.

Step 3 uses that same definition with the arbitrary scheme test xi:T to X. It produces an actual scheme V and a surjective etale scheme map V to T. The statement of def-weil-etale-morphism includes flatness and local finite presentation, exactly the two requirements in def-pc-fppf-site together with surjectivity. The projection V to U is the local lift, by the defining equation of the pullback. I then read the whole statement of lem-weil-pbc-site-sheaf-sets-epi-locally-surjective: it concerns sheaves of sets and its local-surjectivity hypothesis is precisely what the displayed cover proves. The morphism p in the hypothesis is already a morphism of sheaves under the representable-map convention, and X is a sheaf by definition. This step does not assert that p is surjective on sections over T.

Step 4 uses lem-weil-pbc-site-sheaf-sets-epi-kernel-pair-coequalizer. Its statement requires a sheaf epimorphism and the pullback of that epimorphism with itself; these are respectively steps 3 and 1. Its conclusion gives exactly the unique factorization to any sheaf H that this step records. It is not a definition node cited as an effectiveness theorem. It is the existing Mathlib leaf for the very Sites 086K invocation in the source.

Step 5 uses only the universal property actually stated in def-weil-pbc-sheafification. I checked the construction on quotient classes and the naturality under every restriction, rather than invoking local representatives or a plus construction that that definition does not state. The resulting universal property makes Q a coequalizer. The two displayed factorization identities alpha q=p and beta p=q prove both inverse identities by the respective uniqueness clauses. The concluding map is the canonical map induced by p, including the requested compatibility of quotient maps. This is a routine universal-property argument, not a new lemma or a restatement of the desired clause.

I checked small cases: identity atlas gives the diagonal relation and Q=X; a disjoint union of copies of X gives all pairs over the same X-section, not the diagonal relation; an atlas need not lift a T-section globally, which is why step 3 uses V; if X and U are empty the fibre-product, singleton-cover and quotient arguments still hold (a scheme T admitting a map to the empty sheaf must itself be empty, and its identity is a covering). Nothing uses quasi-compactness, quasi-separatedness, affineness, Noetherianity or a field base. The pullback is always over X, while the ambient relation is over S.

Against delivery-errors B--E: there are no new self-contained-statement, duplicate, fake-search or relabelled-clause issues. Each non-elementary input has its own existing cited theorem statement. Each use is backed by a verbatim quote in citations.json. All proof uses are included in proof_deps. I retained the statement and protected metadata, used exact Stacks tags and labels, kept only the permitted literature route, and created no circular or hidden induction argument. Every proof step is below 2000 characters (the longest is 1063), and the quotient calculation is written out. I corrected the initially absent proof and the missing scheme fibre-product notion dependency; there is no source error or statement dispute.
