# Worker report

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-qe-jacobson-g-ring-criterion.json`: statement item, now split by exact reuse of the existing reviewed `lem-per-g-ring-quasi-excellent-closed-fibre`; no Mathlib match.
- `citations.json`: Step 1 quotes the existing theorem's complete statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's original log.

New nodes: 0. New Mathlib leaves: 0. No unit record changed.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, both node ids, Jacobson/G-ring combinations and quasi-excellence. The returned mentions were unrelated docstrings or uses of Jacobson radicals. No finished project declaration states this theorem. Searched `dag/lean_names_upstream.json` too, without an attachment.

## WANTED

WANTED: Kurano–Shimomoto, *Ideal-adic completion of quasi-excellent rings (after Gabber)*, https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf, Theorem 4.1 and its proof on printed pp.4–7, for lem-per-qe-jacobson-g-ring-criterion. The PDF was read online; it is not in this clone's literature/. No download or repository write was made. Consequently proof_origin is agent, as required for an unarchived source.

## Existing duplicate

`lem-per-qe-jacobson-g-ring-criterion` and `lem-per-g-ring-quasi-excellent-closed-fibre` are exact duplicates. Both assert quasi-excellence of a Noetherian G-ring from quasi-excellence of its quotient by an ideal in every maximal ideal. The latter already has seven proof steps and a passing independent L review dated 2026-10-24, by NT-cc-Q90-fd53a4045; its review explicitly requests merging this duplicate into that node. This delivery cites the existing theorem, instead of recreating it or its subordinate lemmas. The maintainer can perform the merge and redirect citers; I have not changed any other node or a maintainer-owned field.

## Not duplicates

There are no new nodes to compare. The exact existing duplicate is identified above and reused. Whole-DAG statement/title searches for G-ring, J-2, regular locus, Brodmann and Rotthaus located the existing canonical theorem. Searches by `kurano40.pdf` located the same source family, including the genuinely smaller alteration-neighbourhood and J-2 regular-locus inputs. `tools/blueprint_refs.py search 'Jacobson'` and `search 'quasi-excellent'` returned zero blueprint nodes; the ancestor command returned `lem-per-artin-gabber-affine-curve`.

## Mathlib searches

Retained the item's imported Q23 search records. Added only searches actually run with msearch.py as Q146, recorded exactly from searches.jsonl: LeanFinder in two phrasings, Loogle for QuasiExcellent, grep for quasi-excellent/Brodmann/Rotthaus/IsGRing, and LeanSearch in words. Every service answered. LeanFinder returned Noetherian quotient, Jacobson, quasi-finite and smooth algebra declarations; LeanSearch returned Jacobson quotient identities, a quotient local-map theorem, smooth lifting, Nakayama and a quasi-finite quotient instance. These do not assert geometric regularity of formal fibres or J-2. The grep hits are the Brodmann–Sharp local-cohomology bibliography at Mathlib/Algebra/Homology/LocalCohomology.lean:32–33. Loogle returned zero hits. No exact or one-line Mathlib specialization was found.

## Problems corrected

The item was unsplit even though a theorem with exactly its statement was already split and reviewed in the live DAG. Its empty proof is replaced by a direct application with an explicit hypothesis check. The statement and statement dependencies are unchanged. There is no statement dispute. The imported ancestor chain is historical provenance; the latest blueprint ancestor proof was read and contains no distinct version of this ring criterion. The canonical node's review also flags stale completion-route provenance; this delivery preserves the item's provenance rather than modifying unrelated nodes or higher-level routes.

## Unfinished work

None for this stage-1 item. Consolidating the two existing ids and archiving the requested PDF are maintainer operations. No Lean was written or compiled.

## Review by Q146

I read the worker brief, stage-1 rules, SETUP's three blueprint levels, GOAL, and delivery-errors B–E. For the mathematical statement I read Kurano–Shimomoto Theorem 4.1 on printed p.4 and the proof on pp.6–7 online, and opened the whole existing canonical node including its statement, seven-step proof and independent passing review. The source states the J-2 conclusion, equivalently quasi-excellence in the presence of the assumed G-ring condition. Neither it nor either DAG statement assumes completeness, characteristic zero, universal catenarity, or a dimension bound. There are no new statements or sources to audit.

Step 1 uses exactly `lem-per-g-ring-quasi-excellent-closed-fibre`. Its statement explicitly quantifies the same commutative Noetherian G-ring A and ideal I, requires I to lie in every maximal ideal, requires A/I to be quasi-excellent, and concludes quasi-excellence of A. Thus it supplies the whole claim under precisely the available hypotheses. No construction or unstated assertion is borrowed from its proof. The citation quote is that actual statement, not a paraphrase. The step is marked non-elementary because it invokes the theorem, while the matching of parameters is immediate. There is no concealed intermediate lemma and the step is under 2000 characters.

For edge cases I checked I=0 (the quotient hypothesis is already the conclusion), a field A (only the proper ideal zero occurs), and the zero ring (there are no primes; the reused theorem has no nonzero-ring restriction). I=A cannot occur for a nonzero ring because a maximal ideal is proper; in the zero ring it is covered by the preceding vacuous case. The condition is membership in the Jacobson radical, not the different assertion that A is a Jacobson ring. No injectivity, nonzero ideal, localness, or finite-dimensionality was silently imposed.

Against B–E, this delivery makes no new elementary, duplicate, clause-restatement or unsearched nodes. It uses a pre-existing reviewed theorem, as the reuse rule requires; it does not move the item into a new node. The cited id is unmerged, in the same chapter and unit, and its proof dependencies do not include this item. Statement notions already cite their definition nodes. The only non-elementary fact in the one-step proof has an explicit node citation. I corrected the missing reuse edge and recorded the duplicate for maintainer consolidation. No other mathematical correction was necessary.
