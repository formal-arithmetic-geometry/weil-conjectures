## Worker report

Files written: `dag/nodes/sec-deligne-laumon-a1/lem-per-fs-chart-torsion-factorization.json` (statement, split; no exact or one-line Mathlib match), this report, and `citations.json`. The sandbox initially contained only dispatcher markers, with no earlier split, report or search log. The item was copied from the current shared repository. All pre-existing Q108 fields and search records were retained, including the source, statement and blueprint ancestry.

Attachments: none. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact blueprint id, fs-chart/torsion-factorization phrases, fine-saturated monoids and root saturation found no candidate declaring this result. Kummer-sequence and Kummer-polynomial results concern different objects. The exact upstream master is not treated as a finished proof. No compiler, Lake, Lean-writing tool or git command in the shared repository was used.

WANTED: none. The needed ILO volume is available locally. I read Exposé VIII 3.1.17 (printed p.101; PDF p.107), VI 2.1 (printed p.71; PDF p.77), and VIII 3.2.9 and its proof (printed p.104; PDF p.110). VIII 3.1.17 defines roots in the monoid's own group, and VI 2.1 defines Kummer by injection and positive multiples. Neither source asserts this entire ambient-group factorization; `proof_origin.by` is therefore `agent`. No SGA route is used.

The item statement is correct and unchanged. It had no proof. The important issue was that finite saturation applies in a monoid's own group completion, whereas saturating h(P) only there would miss the torsion classes in H/A. Steps 4–6 bridge this: positive shifts put representatives of every H/A class in R; adjoining finitely many such representatives to P gives a finite monoid M with group H; its root saturation is exactly R. This is an application of the existing theorem, not a new assertion silently substituted for it.

Nothing remains unfinished in this one-level split. The existing saturation theorem retains its own DAG proof and dependencies.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves.

## Searches and blueprint

The initial item already records Q108's searches; I read their results and retained them. Q124 ran the required `msearch.py` searches, recorded in `searches.jsonl` and appended verbatim as the command's JSON log records in `mathlib_searches`: LeanFinder on the complete Kummer factorization, a second phrasing on ambient-group root saturation and finite coset representatives, Loogle `"NSMulSaturated"`, grep `Kummer|kummer|NSMulSaturated|PowSaturated` with subdirectory `GroupTheory`, and LeanSearch on root closure yielding a Kummer factorization. Every returned signature was inspected. Loogle gives only the root-closure property and its defining equivalence. Grep gives `Mathlib/GroupTheory/Subgroup/Saturated.lean` lines 26, 29, 31, 35–36. The semantic hits concern Selmer groups, group-completion finite generation, ordinary monoid finite generation and localization; none supplies the full statement or its finite-generation step in one line. All services returned successfully. No unrun query was added.

I read the chapter `sec-deligne-laumon-a1`, unit `sk-p-dl-a1-perverse`, and current-main ancestor `lem-per-artin-gabber-affine-curve` proof, especially Step 3. `tools/blueprint_refs.py ancestor` confirms that ancestor. Whole-blueprint searches for `Kummer` and `saturation` found Kummer-sequence nodes and a scheme-image saturation node, with no monoid factorization duplicate. The inherited `from.place` and `via` name the established regular finite-torsion local-model branch and remain correct; `same_as` stays empty. This item is not the unit's key statement, so no unit record was changed.

## Not duplicates

No new-node pairs require comparison. For the item itself, `lem-trf-fine-monoid-finite-saturation` saturates a monoid in its own group; this item constructs a Kummer intermediate monoid inside a larger given fs monoid and identifies both group cokernels. `lem-trf-fs-chart-free-factorization` addresses a torsion-free cokernel, and the toric-refinement nodes require equal group completions. None states the present result. Searches over all `dag/nodes` for root saturation, finite saturation, Kummer and chart torsion located these existing tools and the parent, which I read rather than duplicating.

## Tool uses

`lem-trf-fine-monoid-finite-saturation` is declared in `split_report.tool_uses` as a generic algebraic tool. Its statement, including the allowance of torsion, is exactly the input used in Step 6. It lives in `sk-i-curve-zero` but uses no trace-formula or duality conclusion in this application. No node of this unit states the finite-generation fact. No maintainer-owned top-level `tool_uses` field was added.

## Review by Q124

I checked the node and each cited statement with ILO VIII 3.1.17, VI 2.1 and VIII 3.2.9 open. The notion of fs in `def-trf-fs-log-blowup` explicitly includes finite generation, injectivity into group completion and root closure, with no sharpness or torsion-free-group restriction. The finite-saturation node explicitly assumes a finitely generated integral monoid, takes roots in its own group, and explicitly permits torsion. Its statement—not its internal proof—is enough for Step 6. The four step citations are copied verbatim into `citations.json`.

Step 1 uses the fs definition only to embed the monoids; h^gp is injective by hypothesis, so identifying its image is legitimate. Common positive multiples explicitly prove H is a subgroup. Step 2 uses no external result: the quotient's equivalence relation identifies H/A with exactly the torsion subgroup, and the two successive positive multiples prove G/H torsion free. No structure theorem for finitely generated abelian groups is being assumed.

Step 3 uses the root-closure clause of the cited fs definition for Q, first to get g into Q and then the defining positive-multiple condition for R. The common-multiple addition formula also proves closure. Step 4 uses that same cited clause in the displayed shift calculation. I checked the coefficient n−1 is nonnegative even for n=1, and wrote out why the map from the group completion of a submonoid of a group is injective. This avoids assuming R=Q∩H, which is false for the localization map N→Z.

Step 5 takes finiteness only from the stated hypothesis and the identification in Step 2. Step 4 supplies a representative in R for each class, not merely a difference of representatives. Finite generation of M is by the finite generators of P and the finite list r_i; the equality M−M=H follows because the representatives exhaust the quotient and P−P=A. These are direct arguments, not an unsupported permanence claim for arbitrary submonoids.

Step 6 is the sole non-elementary step. Its citation states finite generation of root saturation in the input's own group. All its hypotheses have been established for M, and that group was proved to be H in Step 5. Each inclusion M^sat⊆R and R⊆M^sat is written using Step 3 and P⊆M. Thus this citation supplies exactly the finite-generation conclusion taken from it. This step is 573 characters, and no non-elementary step exceeds 2000 characters.

Step 7 defines both maps and checks their group maps under the established identification. It uses only the already proved statements and the Kummer condition explicitly defined in this item's statement, which agrees with ILO VI 2.1. Step 8 supplies an elementary proof of the finite-cardinality annihilator by summing the translation permutation; it does not silently invoke Lagrange's theorem or require a new finite-group lemma.

I tested the statement and construction on h=id (R=P, H=P^gp, N=1); N→N by multiplication by d>0 (R=N, H=Z, torsion quotient Z/d); N→Z by inclusion (R=N, H=Z, although Q∩H=Z); N→N² on the first coordinate (R=N×{0}, quotient Z); 0→finite abelian group T regarded as a monoid (R=H=T); N⊕Z/2 mapped identically (nonsharp, group torsion); and the zero monoids. In the finite-group case the finite-saturation input is applied to M containing representatives, not to 0 with its trivial group. All conclusions and positive-cardinality statements hold. No statement dispute or source correction is required.

Against delivery-errors B–E: there are no new statement-only nodes to misstate or duplicate (B1–B10); the preserved statement introduces all its objects and cites the actual fs definition. Every non-elementary fact is the Step 6 cited statement, and the elementary steps include their full formulas (C1–C4). The tool-use declaration identifies the off-unit generic input (C7–C8). The proof performs the construction and both quotient calculations itself; it does not move the item's clauses into children (D1–D5). The saturation and finite-index hypotheses are used only after established; torsion, units, zero cases and actual ambient groups were explicitly checked (E1–E6). No error was found against the quoted source notions (E7).

During work I mistakenly launched two overly broad read-only searches outside the named directories. I stopped both processes immediately; they produced no output and were not used. Subsequent searches were restricted to the paths in the brief. All writes are in this item's sandbox.
