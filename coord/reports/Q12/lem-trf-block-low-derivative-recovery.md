# Stage-1 report: lem-trf-block-low-derivative-recovery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-block-low-derivative-recovery.json`: item, statement unchanged, split into five proof steps; no Mathlib match.
- `citations.json`: every cited step/node pair, with a verbatim excerpt of the cited statement.
- `report.md`: this report.

No new nodes and no Mathlib leaves. All inherited searches are retained. I read the existing sandbox search log, reused its three queries, and ran two additional LeanFinder phrasings. The search hits give derivatives, filtrations, polynomial leading coefficient ideals, Weierstrass division, and substitution conditions, not this theorem. The Weierstrass source and the formal derivative source confirm that those hits do not give the block induction as a one-line specialization.

## Attachments

None. Searches of `lean/WeilConjectures/` by the item id, low-derivative and degree-block terminology, and transverse/Jacobian terminology found no declaration giving this statement. General invertible-Jacobian comments in standard-smooth presentation files do not state it.

## Literature wanted

WANTED: Bierstone--Milman, Canonical desingularization in characteristic zero, Invent. Math. 128 (1997), 207--302, Remark 7.16, Lemma 7.17 and Theorem 7.14 proof, printed pp.267--268, for lem-trf-block-low-derivative-recovery. The node's inherited citation describes the online journal text, but this document is not in literature/. The proof here is marked agent, and is a direct proof from the item's explicit hypotheses, rather than an assertion that ILO states this formal lemma.

## Problems and corrections

The item has no statement error identified. I kept the statement and its statement dependencies. The previously empty proof now gives the argument. In particular an index in the full diagram may have derivatives in W or in variables outside the earlier essential set: step 2 explicitly projects it, applies the earlier-block hypothesis only to that projection, and applies the remaining derivatives only in complementary variables. One must not claim that differentiation in an essential variable preserves its coordinate ideal.

I read ILO VIII 2.3.11--2.3.13 in the local PDF (PDF pp.99--100, printed pp.93--94). These paragraphs discuss the resolution route and cite BM; they do not prove the formal block lemma. I also read the latest blueprint ancestor proof and the unit/chapter records. The latest ancestor uses contracting correspondences; the inherited long ancestry identifies this item as a lower lemma on the historical resolution branch. No unit or chapter route was changed.

## Unfinished work

None in the mathematical split. The first dry run passed (durable receipt head ccdbc17b439); the report was then updated with the online source check, so the final dry run is repeated before push. No Lean was written and no compiler, Lake, or build tool was run.

## Not duplicates

No new nodes were created. Whole-DAG searches for Jacobian, derivatives and the related transverse/implicit-calculus nodes, together with `blueprint_refs.py search` for Jacobian and derivative and `ancestor` for the item, located the existing graph factorization. It is cited instead of recreated. The graph factorization has no block-recovery conclusion, so it does not duplicate the item.

## Review by Q12

I read the full statement of each cited node and the sources described above. The only non-elementary input is the existing reviewed `lem-trf-formal-transverse-shift-calculus`. Its statement, not its proof, explicitly supplies an invertible matrix U with h=U(Y-phi) and equality of the generated ideals. I apply it with phi=0 and regroup the complementary variables; its hypothesis h(W',0)=0 follows from the item's assumption that each g is in the coordinate ideal. Its constant Jacobian is the one in the item. Its field/characteristic-zero hypotheses agree, and its statement explicitly includes empty matrices. There is no need for its more general coefficient formula, for an implicit-function existence assertion, or for a new Jacobian lemma.

Step 1 sets up simultaneous induction with V_0=0, and uses only the increasing-ideal hypothesis. Step 2 cites the formal derivative definition: its coefficient rule makes coordinate derivatives commute and its derivation/Leibniz rule proves stability under complementary derivatives. The projected alpha dominates an earlier vertex because its total order is below the current degree. Thus its projected degree is at most k_l-1, hence at most Q, and the earlier-block derivative hypothesis applies to the current f_i since d_i is strictly greater than that earlier block. This verifies every inequality needed in that use, including full W derivatives. Step 3 uses exactly the item's reduction relation with t=k_l-1<d_i for the current block; all its supported terms were just handled. Lower derivatives of earlier generators use the induction hypothesis and monotonicity of I_t. Each selected g has order d_i-1, not merely a bound by Q. Step 4 cites graph factorization and the power-series coefficient-family definition for regrouping variables. From g in I_t and equality (g)=V it obtains V in I_t. Step 5 takes the last block and checks empty and positive-degree cases. All citation quotes were copied verbatim and checked as substrings of the corresponding statements.

I checked B--E of delivery-errors against the files: no new lemma that repeats a clause, no extra hidden non-elementary tool, no use of a cited proof in place of its statement, no unsupported source tag, and no dependency on a parent. Every proof step has fewer than 2000 characters. The derivative stability computation is a two-line iteration of the definition and remains a proof step rather than a new node. The block induction is spelled out with base and successor, not assumed in a separate lemma.

Small cases: with L=Q, f=Z^2, a=2, the supported correction sets below degree 2 are empty and the hypothesis directly puts f and f' in I_1; g=2Z gives V=(Z). For two blocks use f_1=Z_1^2 and f_2=Z_2^3 with incomparable vertices (2,0),(0,3): derivatives of f_2 supported on the first diagram vanish, and the proof recovers Z_1 first and Z_2 next. A supported multi-index with extra W derivatives still has the same projected diagram index, and the W derivatives preserve V. With s=0 there are no blocks; n=0 forces s=0 under positive vertex degrees. Empty essential tuples use the empty graph-factorization assertion. These tests reveal no missing hypothesis or false step.


## Online source check

I additionally read the journal-version PDF online at https://mahalex.net/teaching/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf, printed pp.267--268 (PDF indices 60--61), specifically Remark 7.16, Lemma 7.17 and the continuation of the proof of Theorem 7.14. Remark 7.16 identifies the coordinate ideal using the Jacobian property and implicit functions. Lemma 7.17 inducts on blocks, uses the reduction of Lemma 7.15, and puts the supported derivative ideal in the preceding coordinate ideal by property (5). The item's reduction hypothesis already supplies that reduction, so citing a separate minors theorem would add assumptions. Steps 1--3 implement this induction with the projection to the previous essential variables and the complementary-derivative calculation written out. Step 4 replaces the source's implicit-function appeal with the existing graph-factorization statement, whose hypotheses are exactly available. The item's generalized ideal-filtration statement and its full derivative conclusion are proved directly, so proof_origin remains agent. No online file was downloaded or written outside the sandbox; the WANTED entry records the missing local copy.
