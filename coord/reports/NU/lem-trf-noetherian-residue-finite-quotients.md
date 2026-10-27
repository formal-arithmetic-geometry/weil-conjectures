# Stage-1 report: lem-trf-noetherian-residue-finite-quotients

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-noetherian-residue-finite-quotients.json`: item split into four steps; statement and statement dependencies unchanged; no exact Mathlib match.
- `citations.json`: six verbatim statement quotations, one for every step/node citation.
- `report.md`: this report. The required search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No Lean was written, compiled, or built.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint tag and the residue/Noetherian/finite-quotient and maximal-power-intersection terminology. The hits about uniformizer quotients, local Krull intersection and adelic principal parts have different hypotheses or objects and do not state this item.

## WANTED

None. Read the relevant statements and proofs in the local Stacks algebra.tex: 00IY (`lemma-dimension-is-length`), 00J0 (`lemma-length-finite`), 00IP (`lemma-intersect-powers-ideal-module-zero`), 00IQ (`lemma-intersection-powers-ideal-module`) and 00HN (`lemma-characterize-zero-local`). Checked tag/label correspondence in the local tags index.

## Audit of the original item and route

No mathematical statement error was found. The initially empty proof is replaced by an explicit finite-filtration argument and separation argument. The source's local length statements are not applied to the nonlocal ring R. Instead, finite ideal generators and lifts of a K-spanning list of R/m give concrete K-spanning lists in every graded piece and hence in the truncated quotient.

Read GOAL.md, the three blueprint levels in SETUP.md, the chapter/unit records, and the current latest blueprint unit and lem-trf-local-term-locality proof (snapshot main-20261024). The long inherited blueprint.from chain is historical analytic support for automatic boundedness, not part of the current contracting-correspondence proof. This delivery keeps that provenance and supplies only the requested algebraic tool. It does not change the chapter or unit or claim to realize the unit's key statement.

The existing off-unit node lem-weil-pbc-krull-intersection-localization is used as a generic algebraic tool and declared under split_report.tool_uses. Its statement, rather than its internal proof or an unexposed local theorem, supplies the annihilation conclusion needed here.

## Searches and Mathlib verdict

Read the inherited item's recorded searches and their actual hits. Ran additional logged msearch queries using leanfinder, leansearch, loogle and grep, with two different natural-language phrasings. Read the returned types. Ideal.finite_quotient_pow and IsLocalRing.finite_quotient_iff require finite underlying sets, not finite K-dimension; Ideal.Factors.finiteDimensional_quotient_pow additionally requires a module-finite Dedekind extension and does not apply here. Read Mathlib/RingTheory/Finiteness/Finsupp.lean:153–169, RingTheory/Filtration.lean:425–437, and RingTheory/LocalProperties/Basic.lean:539–545. The exact-sequence finiteness lemma would still require the inputs that steps 1–2 construct; the local Krull theorem alone does not provide the global intersection conclusion. Thus the conjunction is not a one-line specialization of those declarations.

Searched the whole DAG for all four original source tags and the relevant terms, and used blueprint_refs.py search for `Krull intersection`, `finite dimensional quotient`, `residue finite`, and `intersection powers`. Reused the existing 00IQ node and maximal-localization membership leaf. The local graded-length bridge assumes a local ring and adds a Hilbert-polynomial assertion; the derived completed-localization detection node concerns objects of D(R). Neither is a replacement statement for the present item. The filtration calculation is elementary and remains in the item's proof: it does not become a new clause-node.

## Not duplicates

No new nodes were created; no new/existing duplicate pairs arise.

## Review by NU

I checked delivery-errors B through E with the JSON, the cited node statements, and the source open. There are no unsplit new nodes, new definitions, unverifiable source tags, or new clause-nodes. The statement is unchanged and all dependencies named in its text remain present.

For step 1 I read def-weil-pbc-noetherian-ring, which says precisely that every ideal is finitely generated, and def-weil-finite-dimensional-subspace, which specifies a finite spanning list. These give generators of m^i and a K-spanning list of R/m, respectively. I checked the coefficient calculation: reducing each coefficient r_j modulo m leaves u_j in m, so u_j g_ij lies in m^(i+1). No finite generation of R as a K-module is asserted. No unquoted theorem on module length or restriction of scalars is used. This step is elementary because the generators give the displayed expansion directly.

For step 2 the repeated remainder calculation explicitly constructs a finite spanning list of R/m^n. Its only cited definition gives exactly the resulting finite-dimensionality assertion. The induction starts at r in m^0=R, runs n reductions, and ends in m^n. I checked that this does not presuppose the desired finite dimension in the induction step or invoke an uncited extension theorem. The source is 00J0's finite filtration, with the extra K-coefficients written out; proof_origin is honestly marked agent.

For step 3 I read the entire statement of lem-weil-pbc-krull-intersection-localization. It applies to a Noetherian ring, any ideal I, a finite R-module M, and a prime p containing I. Here M=R is generated by 1, I=p=m, and a maximal proper ideal is prime (the quotient-field argument is included). Its conclusion says explicitly that each element of N is annihilated by some power of f outside p. Since the n=0 factor is R, x in all positive powers is in this exact N. I read def-weil-pbc-localization-at-prime and verified the inversion of f as a fraction; no interchange of infinite intersection and localization is assumed. I read lem-weil-pbc-ideal-membership-at-maximal-localizations: it gives exactly the desired conclusion with J=0 after x/1=0 at every maximal ideal. Every node cited here has a verbatim quotation in citations.json. The non-elementary Krull input and maximal detection input are both cited as nodes, rather than tags alone.

For step 4 I checked the stipulated empty-family convention directly. In the zero ring the whole ring is the zero ideal. Additional edge checks: for a field R=K, m=0 and every power quotient is K; for R=K[epsilon]/(epsilon^2), m^2=0 gives finite quotients while nilpotents survive in the ring; for a product K x K, the intersection of the two maximal ideals is zero although neither individual maximal-adic intersection need be zero; for R=K[[t]], the local example is not a finite-type K-algebra but has finite-dimensional truncated quotients. Thus no reducedness, locality, Jacobson or finite-type hypothesis slipped in.

All steps have explicit elementary flags, proof_deps is precisely the union of uses, and no proof step exceeds 2000 characters. No statement dispute, hidden comparison lemma, source error, or unfinished mathematical obligation remains.

## Unfinished work

None within this stage-1 item. Its dependencies retain their existing states; no changes to other nodes are proposed.
