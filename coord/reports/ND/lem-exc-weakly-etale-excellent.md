# lem-exc-weakly-etale-excellent — ND stage-1 report

## Files written

- `dag/nodes/sec-smooth-purity/lem-exc-weakly-etale-excellent.json`: existing statement, unchanged; six proof steps; no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-weakly-etale-g-ring.json`: new statement-only G-ring ascent theorem under only a G-ring source hypothesis; unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-weakly-etale-nagata-j2.json`: new statement-only simultaneous Nagata/J-2 ascent theorem; unsplit, no Mathlib match.
- `dag/nodes/sec-smooth-purity/lem-exc-weakly-etale-locally-nagata-catenary.json`: new statement-only ascent of local Nagata and universal catenarity; unsplit, no Mathlib match.
- `citations.json`: seven verbatim step/node quotations.
- `report.md`: this report. `prepare.py` and `search-*.txt` are sandbox-only working records.

Total: three new statement nodes, zero new definitions, zero Mathlib leaves. Every child has an empty proof, empty proof dependencies, and null proof origin. This item is not the unit's key node, so no unit record is edited. No shared repository or launcher file was written and no git command was run there. No Lean, Lake, compiler, or build command was used.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact item id, weakly-etale terminology, G-ring, J-2, Nagata and catenarity. The only excellence occurrence is a discussion of Gabber in an unrelated stability docstring; the ring-theory Nagata occurrence concerns unique factorization. No project declaration states the parent or any of the three new statements. The upstream master checkout was also searched as reference material; it supplied no finished proof claim.

## WANTED

WANTED: Silvio Greco, *Two theorems on excellent rings*, Nagoya Mathematical Journal 60 (1976), 139–149, DOI 10.1017/S0027763000017190, especially Foreword, §1.1, Remark 5.2 and Theorem 5.3, for this item and its three new prerequisite nodes. It is not present in the shared literature tree. I read the original paper's text through the online PDF mirror at `https://scispace.com/pdf/two-theorems-on-excellent-rings-2lc74dyy3w.pdf`, including printed pp. 139–140 and 146–148; the Cambridge article record independently confirms the AF/excellence theorem. No paper was downloaded or written to the shared tree. The parent's `proof_origin.by` is `agent` because the canonical literature copy remains unavailable, as the standing brief requires.

The Stacks source is readable in the existing literature mirror `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`. I read `more-algebra.tex` at `definition-G-ring` (07GH), `definition-excellent` (07QT), and `lemma-quasi-excellent-nagata` (07QV), and `algebra.tex` at `lemma-nagata-localize` (032U). The new nodes' sources name Greco's actual theorem clauses; the Stacks tags in those sources locate definitions, and are not misrepresented as sources for Greco's ascent assertions.

## What was wrong and what changed

No statement dispute: the original statement is correct, including the target Noetherian hypothesis. The initial node had no proof. My first sandbox draft merely translated weakly etale into AF and applied Greco 5.3(iv) without a prerequisite node; although packaging preflight accepted that draft, it failed C1/D3 mathematically. I discarded that proof before handoff. The final split follows Greco's actual opening proof of 5.3(iv): assemble the independent results 5.3(i), (ii), and (iii). It does not cite 5.3(iv) as an unrepresented black box.

The three new nodes are genuine weaker-input theorems, not copies of the item under a new name. The G-ring theorem assumes neither J-2 nor universal catenarity. The Nagata/J-2 theorem assumes neither G-ring nor universal catenarity. The local-Nagata/catenarity theorem assumes neither G-ring nor J-2, and retains the source's local Nagata hypothesis explicitly. None assumes or concludes excellence. The parent must unpack excellence, derive global and local Nagata from existing results, check three distinct sets of hypotheses, and then assemble the target properties. These are not the parent's clauses with the excellent-source hypothesis unchanged.

The item statement, all four statement dependencies, imported/created metadata, chapter and unit are retained. Its original blueprint place accurately points to the second-paragraph permanence sentence and is preserved. The actual blueprint does not name Greco; the report and new-child places distinguish that sentence from the particular proof route supplied later by this item. The child `via` lists are `[lem-exc-weakly-etale-excellent, lem-exc-field-algebra-strict-henselization-excellent]`, through the nearest blueprint ancestor `thm-exc-curve-open-dimension-general`.

## Searches and route

Before creating the nodes I searched the complete DAG statements for weakly-etale/absolutely-flat maps together with G-ring, J-2/J2, Nagata and catenarity; searched source places for Greco 5.3(i)–(iii); searched all blueprint nodes with `tools/blueprint_refs.py search` for `absolutely flat`, `weakly etale G-ring`, `Nagata J2`, `weakly etale Nagata`, `locally Nagata universally catenary`, and `geometrically regular formal fibres`; and checked all three proposed ids in the DAG and project Lean source. None already states a new theorem. The existing `lem-exc-quasi-excellent-nagata` and `lem-weil-pbc-nagata-localization` were reused rather than duplicated.

For each child, two distinct LeanFinder phrasings, Loogle, grep and LeanSearch were actually run with `msearch.py ND lem-exc-weakly-etale-excellent ...`; exact outputs are in its `mathlib_searches`, `search-*.txt`, and the launcher's `searches.jsonl`. I read the hits: the semantic results concern etale composition/presentation, flatness, going down and regular sequences, none of which concludes a G-ring, J-2, Nagata, or catenarity assertion. The G-ring and catenarity name/grep searches are empty. Nagata/Japanese grep hits concern analytic Japanese brackets and bibliographic references to Nagata, including Noether normalization, not the ring property. LeanSearch returned Internal Server Error and every such query is `unavailable`. The item itself also has a fresh five-query record, including a second semantic phrasing. No declaration qualified as an exact or one-line Mathlib specialization.

The chapter and `sk-prop-a1-kummer` unit were read, together with the actual ancestor blueprint file under `/home/ubuntu/weil-launcher-nt/literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/`. This is the existing strict-local curve route; no unit or chapter route is changed. `lem-weil-pbc-nagata-localization`, in another unit, is declared in `split_report.tool_uses`: it is the generic localization lemma checking a local hypothesis of Greco 5.3(iii), not a replacement for the affine-line/Kummer argument.

## Not duplicates

lem-exc-weakly-etale-g-ring vs def-weil-pbc-g-ring: the existing node defines geometric regularity, regular maps and G-rings; the new theorem proves G-ring ascent along a weakly-etale map.

lem-exc-weakly-etale-g-ring vs lem-weil-pbc-g-ring-check-pairs-of-primes: the existing statement characterizes formal fibres of one ring by pairs of primes; it has no weakly-etale algebra or ascent conclusion.

lem-exc-weakly-etale-g-ring vs lem-weil-pbc-g-ring-ring-equiv: the existing statement transports G-rings only along ring equivalences; weakly-etale maps need not be equivalences.

lem-exc-weakly-etale-g-ring vs lem-weil-pbc-adic-completion-ring-equiv: the existing statement constructs a completion equivalence from an ideal-preserving ring equivalence; it does not prove G-ring ascent.

lem-exc-weakly-etale-nagata-j2 vs def-weil-pbc-nagata-ring: the existing node defines Nagata and universally Japanese rings; it states no ascent theorem.

lem-exc-weakly-etale-nagata-j2 vs lem-weil-pbc-finite-type-z-domain-normalization-finite: the existing theorem gives finite normalization for domains finitely generated over the integers; it does not treat weakly-etale maps or J-2 ascent.

lem-exc-weakly-etale-nagata-j2 vs def-exc-excellent-ring: the existing node defines J-2 and excellence; it contains no permanence theorem.

lem-exc-weakly-etale-locally-nagata-catenary vs def-weil-pbc-nagata-ring: the existing node defines Nagata rings and has no local-Nagata/catenarity ascent assertion.

lem-exc-weakly-etale-locally-nagata-catenary vs lem-weil-pbc-finite-type-z-domain-normalization-finite: the existing finite-normalization assertion has neither a weakly-etale map nor a universal-catenarity conclusion.

lem-exc-weakly-etale-locally-nagata-catenary vs def-exc-excellent-ring: the existing node defines catenarity and excellence; it does not show that either ascends.

The three children are also mutually distinct: they have different source-property hypotheses and conclusions. Compared with `lem-exc-weakly-etale-excellent`, each has weaker, separate source requirements and none concludes excellence. Compared with `lem-exc-field-algebra-strict-henselization-excellent`, they concern arbitrary weakly-etale Noetherian ring maps and individual weaker properties, not the excellence of particular strict henselizations.

## Review by ND

I read Greco's Foreword (commutative Noetherian rings throughout), §1.1 (the P-ring framework), Definition 5.1, Remark 5.2, all six clauses of Theorem 5.3, and its proof through 5.4 and 5.5. I checked the new G-ring statement against (i) with P geometrically regular, the Nagata/J-2 statement against (ii), and the local-Nagata/universally-catenary statement against (iii). Remark 5.2 permits the project weakly-etale formulation because both source and target in every child are explicitly Noetherian. The paper distinguishes local Nagata from global Nagata; I preserved that distinction in the third child instead of silently replacing its hypothesis. The G-ring definition node supplies precisely the formal-fibre property used by the specialization. Every new statement introduces A, B and f and either references an existing defining statement or explicitly expands its terminology; no proof sketch is inside a new statement.

For step 1 I reopened `def-exc-excellent-ring`. It explicitly supplies all four conditions of excellence; the quoted segment includes the Noetherian, G-ring and J-2 list and the universal-catenarity conjunct. This is a definition expansion and is marked elementary. The parent itself already introduces the target Noetherian and map weakly-etale hypotheses, so there is no missing theorem at this step.

For step 2 I reopened both cited existing statements. `lem-exc-quasi-excellent-nagata` concludes Nagata for any quasi-excellent commutative ring, exactly applicable to R from step 1. The last sentence of `lem-weil-pbc-nagata-localization` explicitly concludes that each prime localization is Nagata; it is not a merely abstract definition or a finite-localization assertion. This supplies precisely the quantified hypothesis needed for the third child. The Stacks proofs 07QV and 032U were also read. Their dependency paths do not run through the item.

Steps 3, 4 and 5 each cite a new node whose statement was read in full. For step 3 the source G-ring property is step 1; for step 4 global Nagata is step 2 and J-2 is step 1; for step 5 every source prime localization is Nagata by step 2 and universal catenarity is step 1. In each application A=R, B=S and f is exactly the given ring map; R's Noetherianity comes from excellence, S's from the unchanged hypothesis. No finite type, finite presentation, faithful flatness, perfectness, or finite-residue-extension assumption is introduced. Each child's statement gives exactly the property extracted at its step. The target Nagata extras are unused and do not conceal an additional inference.

Step 6 merely reassembles Noetherianity, G-ring, J-2 and universal catenarity using the same excellence definition. It is elementary, and there is no theorem at this step that needs another node. `citations.json` contains one literal statement substring for each of the seven step/node pairs; new-node quotations are their whole statements, and the existing Nagata-localization quotation is exactly its last sentence. Proof dependencies are the union of the step uses.

I checked every new statement on identity maps under its own source assumptions, rather than assuming excellence for the tests. For a separable algebraic extension of fields the target remains a field and all the asserted properties hold, even if the extension is infinite, so no accidental finite-presentation assumption has appeared. A non-faithful map such as k×k to k by projection also meets the intended hypotheses and conclusions; this checks that the faithfully-flat converses (v) and (vi) have not been confused with the ascent parts. For the zero target, flatness holds for the zero module; all prime/localization conditions are empty and any unital algebra over the zero ring is zero, so J-2 and universal catenarity are vacuous. These cases are consistent with each new statement and the parent. Arbitrary quotients are not asserted weakly etale: quotienting an excellent ring by a non-flat ideal is not a counterexample to this ascent theorem.

Against B, all three children are statement-only, self-contained, searched honestly and tied to exact source clauses; the source-definition tag overlaps are distinguished above after opening every matched existing statement. Against C, the first draft's uncited ascent theorem was corrected; every final non-elementary step is a statement of a cited node, and all hypotheses were checked. Against D, no child is a renamed excellence theorem, and the six-step argument performs the source's property assembly and Nagata hypothesis derivation. Against E, the crucial checks were target Noetherianity, local versus global Nagata, direction of ascent versus faithful-flat descent, and the multiplication-map weakly-etale convention. No mathematical statement correction was needed.

## Unfinished work

None for the requested one-level split. The three new prerequisite statements remain unsplit for later workers. The canonical local Greco literature copy is still WANTED. The second reader must review and deliver; this worker runs only the dry run and does not push.

## Dry run

The first, superseded draft passed packaging preflight, which did not certify its missing mathematical dependency. The final six-step split with three new nodes is checked by the required command after this report is written. The installed deliver.py accepts `python3 /home/ubuntu/weil-launcher-nt/deliver.py ND lem-exc-weakly-etale-excellent --no-push`; the brief's extra trailing `.` is rejected by its usage parser, so the documented no-dot invocation is used.

The independent read-only overlay traversal found an inherited missing id, `def-weil-pbc-regular-scheme`, referenced by existing generic-formal-fibre model nodes below the old G-ring infrastructure. Every direct dependency of all four delivered nodes exists, all seven quotes are literal, and no cycle is introduced. This existing deeper issue is reported here and left untouched.

The first final-version packaging attempt stopped at a shared-repository config lock (`.git/config: File exists`) before preflight. No lock or shared file was edited; the required delivery tool is retried for this transient coordination failure.

## Second reading by ND

I independently read the official Greco PDF, printed pp. 139–140 and 146–148, and opened the Stacks TeX definitions and lemmas listed below. The item's statement agrees with Greco 5.3(iv), with the Foreword's two Noetherian ring hypotheses and Remark 5.2's flat-map/flat-multiplication interpretation of AF. No statement dispute or mathematical correction was needed.

- Step 1: checked the full statement of `def-exc-excellent-ring` against 07QT (`definition-excellent`) and 07P7 (`definition-J`); PASS, elementary unpacking supplies exactly Noetherianity, G-ring, J-2, and universal catenarity.
- Step 2: checked the full statements of `lem-exc-quasi-excellent-nagata` and `lem-weil-pbc-nagata-localization` against 07QV (`lemma-quasi-excellent-nagata`) and 032U (`lemma-nagata-localize`); PASS, quasi-excellence is established in step 1 and localization gives every required prime localization, with no finite-type restriction.
- Step 3: checked `lem-exc-weakly-etale-g-ring` against Greco 5.3(i), §1.1 and 07GH (`definition-G-ring`); PASS, both rings are Noetherian and the source G-ring hypothesis is established.
- Step 4: checked `lem-exc-weakly-etale-nagata-j2` against Greco 5.3(ii), with 032R (`definition-nagata`) and 07P7 (`definition-J`); PASS, source Nagata comes from step 2 and J-2 from step 1. Extracting the stated J-2 conjunct requires no additional theorem.
- Step 5: checked `lem-exc-weakly-etale-locally-nagata-catenary` against Greco 5.3(iii), 00NI (`definition-catenary`) and 00NL (`definition-universally-catenary`); PASS, local Nagata and universal catenarity are both present, without using a faithfully flat converse.
- Step 6: checked the full excellence definition and Greco's opening proof of 5.3(iv); PASS, elementary assembly of the four properties already obtained.
- New node `lem-exc-weakly-etale-g-ring`: checked Greco 5.3(i), §1.1, Remark 5.2, and the defining nodes for Noetherian, weakly etale, and G-ring; PASS B1–B7. It is a non-elementary ascent theorem with only a G-ring source assumption, rather than excellence.
- New node `lem-exc-weakly-etale-nagata-j2`: checked Greco 5.3(ii), Remark 5.2, and the Noetherian/weakly-etale/Nagata/J-2 defining statements; PASS B1–B7. Neither G-ring nor universal catenarity is assumed; both conclusions are present in the source.
- New node `lem-exc-weakly-etale-locally-nagata-catenary`: checked Greco 5.3(iii), Remark 5.2, and the Noetherian/weakly-etale/localization/Nagata/catenarity defining statements; PASS B1–B7. Local Nagata is quantified over all prime localizations, rather than silently replaced by global Nagata.

For all three new nodes I checked identity maps, separable algebraic field extensions (including infinite ones), the non-faithful projection $k\times k\to k$, and maps to the zero ring. In the projection the target is a direct summand as a source module and the multiplication map is an isomorphism. For the zero target all prime conditions are vacuous and all algebras over it are zero. These tests expose no omitted hypothesis, finite-presentation assumption, or accidental faithful-flatness requirement. Greco's Foreword, Remark 5.2, and Stacks 092B (`definition-weakly-etale`) identify exactly the map predicate used here.

I repeated whole-DAG statement/source searches for weakly-etale or absolutely-flat maps together with G-ring, J-2, Nagata, and catenarity, opened all the potentially overlapping statements named under `## Not duplicates`, and searched the whole imported blueprint for G-ring, Nagata J-2, and universally catenary. No duplicate was found. The three weaker-input theorems are independent ingredients, each strictly below excellence; none proves the entire item. The ancestor and its second proof paragraph, chapter, and unit were opened; the existing local-algebra route is preserved. The generic Nagata localization tool is appropriately declared in `split_report.tool_uses`, as authorized by SETUP's fourth claims/tool-uses decision.

I ran one new LeanFinder phrasing for each child, using flat multiplication, formal fibres, relative loci, and prime-chain vocabulary rather than the author's queries. I read every returned type. Flatness and going down do not supply G-ring ascent; openness of a relative smooth locus does not supply J-2; height formulas do not state universal catenarity. A fresh word-bounded RingTheory grep found only the historical credit to Nagata in `Mathlib/RingTheory/NoetherNormalization.lean:14`. These exact search records are appended to each relevant node and to searches.jsonl. The earlier broad grep also ran and remains in the raw log; its incidental “ring ring” matches were excluded by the tighter repeat. Read-only source searches in slopmaster2 found no declaration stating these ascent theorems. No Mathlib leaf or finished source attachment was found.

Changes made and why:

- Expanded the step 1/6 excellence quotes to the full defining statement, including universal catenarity, and the step 2 Nagata-localization quote to include its hypotheses. All seven step/node citations remain verbatim and cover what the steps use.
- Added the independent Mathlib search records and precise verdicts; retained all three genuine non-elementary prerequisite nodes and the correct proof steps.
- Retrieved the official Cambridge PDF to `greco-1976.pdf` in this sandbox and extracted `greco-1976.txt`, resolving the inherited source record's missing reproducible retrieval/hash documentation. URL: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/8F98780AD8CD9051866A2716C67833C3/S0027763000017190a.pdf/two-theorems-on-excellent-rings1.pdf . SHA256: `7e5b69f052d7966551e1fd292ed0916a7da9edeb70cd542b33d4052819ae074e`. Retrieval used `curl -L --fail --max-time 45 <URL> -o greco-1976.pdf`; extraction used `pdftotext -layout greco-1976.pdf greco-1976.txt`. The direct Scispace download returned HTTP 403; the official Cambridge download succeeded. The source PDF/text are sandbox working records, not delivery files. The WANTED entry concerns the shared literature tree, which remains read-only.
- Updated only the parent's proof-origin retrieval description to reflect that official source reading; its `by: agent` and all mathematical statements are preserved.

All new nodes remain self-contained, statement-only and unsplit, with one TeX escape per command, exact source clauses, defining-node references, and valid blueprint ancestry. No live project/launcher file was edited, no git command was run directly, no agent was started, and no Lean/compiler/Lake/build command was used.

Second-reader validation: `python3 /home/ubuntu/weil-launcher-nt/deliver.py ND lem-exc-weakly-etale-excellent --no-push` printed `OK (not pushed) deliver/ND/lem-exc-weakly-etale-excellent at fac88bf0b8: preflight passed`. No preflight repair was required. The installed parser requires the invocation without a trailing dot, as the author already documented above.
