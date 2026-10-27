# Stage-1 report: lem-trf-monoid-sheafification-trivial-covers

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-monoid-sheafification-trivial-covers.json`: statement; split into seven proof steps. Mathlib verdict: no declaration states the whole item. No new nodes, hence zero new Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every step/node pair, with both local-lifting and local-equality excerpts where used.
- `report.md`: this report. `searches.jsonl` is the actual msearch log; `ilo-excerpt.txt` and `write_split.py` are sandbox-only reading/writing aids.

## Attachments

None. Searched the project `lean/WeilConjectures/` for the exact blueprint tag and for monoid/sheafification and trivial-cover terminology. There is no declaration giving all clauses of this item. Read `CategoryTheory/Sites/MonObj.lean`: its monoid-object transport and tensor comparison concern a different setting and do not give this statement. A sorry declaration would not qualify as an attachment.

## WANTED

None. Both ILO and the needed Stacks source are available locally.

## Findings and changes

The live item was unsplit and had no earlier sandbox split or report. There is no released repair note for it. The statement, `stmt_deps`, source, created metadata and historical blueprint provenance were retained. The existing Mathlib searches from its creation were retained; six fresh searches were appended with their actual command-log queries and results. Both natural-language phrasings and the type/name searches were read. General forgetful-functor preservation and local bijectivity exist in Mathlib, but the full combination, component conclusion on selected opens and inverse restriction formulas require an argument. I reused existing DAG nodes instead of making these facts into new nodes.

Read `GOAL.md`, the stage-1 brief, stage document, worker role, SETUP's three levels and tool-lemma rule, and delivery-errors B--E in both occurrences. The current latest blueprint's chapter, unit and `lem-trf-local-term-locality.md` differ from their historical DAG records: the current route uses contracting local terms, and that ancestor contains no monoid or fan-sheafification assertion. This item explicitly retains its historical affine-fan branch provenance. I did not change the unit or chapter, make a current route claim, or use any SGA source.

The proof no longer risks citing the universal-property definition as if it supplied a plus construction. It uses the actual finite-limit theorem to extend operations and checks the monoid universal property, then cites the existing local-section theorem for precisely its stated local assertions. No statement dispute was found and no mathematical hypothesis was changed.

## Existing-node and blueprint searches

Searched the whole DAG for `00WH`, `00WK`, `00YR`, finite-limit/product sheafification, underlying-set sheafification and local lifting/equality. Read the statements and metadata of `lem-weil-pbc-sheafification-sets-exact`, `lem-weil-pbc-site-sheafification-sections-local`, `lem-weil-pbc-sheafification-plus-theorem`, `lem-weil-pbc-algebraic-sheaf-iff-underlying-sets`, `lem-weil-pbc-sheaf-algebraic-structures-objects`, and `def-weil-pbc-sheafification`. The algebraic-sheaf nodes restrict to abelian groups or rings: they cannot be cited as monoid theorems. They are not used. The plus theorem is unnecessary. `blueprint_refs.py ancestor` confirmed `lem-trf-local-term-locality`; its searches for `sheafification`, `monoid`, and `trivial covers` found no imported blueprint node stating this item. The existing item's `same_as: []` is confirmed. No new node was created, so no new/existing-node duplicate pair exists.

## Review by Q23

I read ILO VIII 3.1.3 and Remark 3.1.4(iii), printed pp.98--99, in the PDF text. It defines the sharp monoid sheaf on affine fan opens and explains that every cover of such an open contains the open itself, so sheafification does not change those values. The item states the general topological monoid version of exactly this mechanism, including the required naturality. I also read Stacks `sites.tex`, Tag 00WH (`proposition-sheafification-adjoint`), 00WJ (`lemma-sheafification-exact`), 00WK (`lemma-sections-sheafification`), and 00YR (`section-sheaves-algebraic-structures`), properties (alpha)--(zeta). The last source discusses forgetful compatibility for algebraic structures; the split writes out the monoid-specific operations and universal-property argument instead of assuming a missing monoid node. No new statement-only sources are needed.

Step 1 uses `def-weil-pbc-sheafification` only for the set sheafification and its natural unit. `lem-weil-pbc-sheafification-sets-exact` explicitly supplies the terminal-object and product comparisons via projections, which iteratively give the finite powers used here. It applies because the open site is small in the common coefficient universe. The step defines addition and zero, writes their unit equations, and explains sectionwise products by coordinatewise sheaf gluing. It does not assume that monoid and set sheafification already agree.

Step 2 uses those same two statements to detect equality of maps out of each finite power after the unit. Each monoid law is reduced to its original equation on Q, with the domains (one, two or three factors) specified. This is a direct universal-property calculation, marked elementary, and does not invoke a new transport theorem. It supplies natural monoid operations on S without choosing objectwise arbitrary operations.

Step 3 again uses exactly the set universal property and product comparison. The two addition-preservation maps are displayed and agree after the product unit; zero preservation follows from the displayed unit identity. Thus the unique extension really is a monoid map, which establishes the monoid universal property. Step 4 uses only `def-weil-pbc-sheafification`: maps in both directions factor the respective units, and their composites are identities by uniqueness. Consequently the identification carries the *given* eta, not merely an unspecified isomorphism of underlying sheaves, and yields its set universal property. These short formal assembly calculations are not new nodes restating the item's clauses.

Step 5 uses `lem-weil-pbc-site-sheafification-sections-local`, whose statement I opened. It explicitly gives both covering-local lifts of sections and covering-local equality for equal images. Its universe bound is satisfied here. Open-site covers are open covers; no finite or quasi-compact cover assertion is used. Step 6 uses those same two clauses and selects the member equal to U in each resulting cover. This proves both surjectivity and injectivity; it does not infer them merely from the monoid universal property. Step 7 cites no further result: applying the bijective eta to zero and sums proves the inverse homomorphism formulas, and composing the original restriction naturality equation with the two inverse components proves inverse naturality explicitly.

I checked edge cases: on the empty space the selected collection is empty and the component assertions are vacuous; local assertions over the empty open allow its empty cover. The nonempty condition in the collection is substantive: a presheaf may take a nontrivial monoid at the empty open whereas its sheafification there is the singleton. For a one-point space and any commutative monoid, the only nonempty open has the asserted component bijection; the argument imposes no cancellativity, integrality, fineness or sharpness. An empty collection is permitted, and inclusions between collection members need no closure under intersections. The proofs use the original homomorphism eta and its naturality, so both zero and addition are preserved for arbitrary, possibly noncancellative monoids.

I checked B1--B10: no new nodes, no hollow definitions, no proof hidden inside a statement, single TeX escaping, precise source tags and labels, genuine searches with unavailable handled honestly (all six fresh searches succeeded), and no unjustified attachment. For C1--C8 every substantive external input is in a cited statement and quoted verbatim in `citations.json`; the local-sections theorem is declared as a generic off-unit tool in `split_report.tool_uses`. Finite-product preservation and the sheafification definition are Mathlib leaves. No cited node depends on this item. For D1--D5, the proof carries the operations, law checks, factorization checks, trivial-cover argument and naturality calculation; it does not transfer a clause into a newly named node or leave an omitted source argument. For E1--E7, smallness, coefficient universe, sheaf targets of the universal property, cover hypotheses, and direction of each comparison were checked at their uses. Every proof step is below 2000 characters. No further hidden lemma was found.

## Unfinished work

None in the stage-1 split. The maintainer's independent review remains the normal delivery review; no Lean files were written and no compiler or Lake command was run.

## Dry-run repair

The first dry run rejected the finite-limit citation excerpt as shorter than the required 40 characters. I replaced it in all three affected step entries with the complete concluding sentence of the cited statement, including its terminal-object and product clauses. The mathematical argument did not change.
