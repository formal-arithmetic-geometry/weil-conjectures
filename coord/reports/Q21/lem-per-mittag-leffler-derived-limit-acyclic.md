# Stage-1 report: lem-per-mittag-leffler-derived-limit-acyclic

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-mittag-leffler-derived-limit-acyclic.json: statement, split in five steps; no Mathlib match for the full statement. No new nodes and no Mathlib leaves.
- citations.json: verbatim statements backing the three proof citations.
- searches.jsonl: actual searches run with msearch.py. The node retains its inherited search records and adds this session's new queries and results.

## Attachments

None. Searches of WeilConjectures/ in slopmaster2 for the exact item tag, Mittag/mittag, and derived-limit terminology found no declaration stating this item. The exact upstream master was also checked as reference material, without treating it as finished proof evidence.

## WANTED

None. All mathematical sources needed are present locally.

## Audit and corrections

The existing item was statement-only; there was no earlier sandbox split or report to resume. I preserved its statement, hypotheses, source, creator metadata, blueprint ancestor and via chain, and inherited searches. It correctly states Stacks 07KW (1),(3) for countable towers of ordinary abelian groups. No statement dispute or change is necessary. The imported finite-group node lem-weil-pbc-mittag-leffler is insufficient for arbitrary ML towers: the groups here can be infinite. The existing surjective-tower node lem-pc-tower-surjective-lim-acyclic also has a strictly stronger hypothesis than this item, so neither can replace the argument.

The proof constructs the finite-prefix short exact sequence from the proof of 07KW, uses the already stated ML-kernel exactness theorem, and calculates its induced limit map as the very Roos map in the item. It does not appeal to a noncanonical derived cone or identify abelian-group derived limits with sheaf-derived limits. The two cross-unit generic tools are declared in split_report.tool_uses. No unit record is edited: the item is a subordinate lemma, not the unit's key statement.

## Not duplicates

No new nodes. Whole-DAG searches for 07KW, Mittag-Leffler, ML-limit-nonempty, 0598, and derived-limit/Roos terminology found the existing exactness and Roos statements used here. Whole-blueprint searches with tools/blueprint_refs.py for Mittag and Roos found the finite-group variant and the broader surrounding Roos material, but no blueprint node stating the arbitrary ML-group assertion. The item's same_as remains empty: a strict special case is not the same statement. The recorded ancestor is lem-per-artin-gabber-affine-curve; the via chain already specifies the punctured-completion sub-input of its formal-sections/duality route.

## Review by Q21

I read the complete local source of Stacks 07KW (more-algebra.tex, lemma-compute-Rlim), including the displayed finite-prefix systems and difference map. I also read Homology 02N0 and 02N1 (definition-Mittag-Leffler and lemma-Mittag-Leffler), and Algebra 0595 through 0598, in particular lemma-ML-exact-sequence and its fibre correction proof. The tag-label matches were checked in tags/tags. The chapter, unit, ancestor statement/proof and the full blueprint ancestry of the item were read to keep this a tool lemma in the recorded formal-sections route. No SGA source is used.

For Step 1 I opened def-weil-inverse-system: its statement gives exactly the composites and commuting-map condition used. The formulas for j and d commute with prefix restrictions; at the last retained coordinate this uses t_(n+1,n)=g_n. This step is an elementary construction of group homomorphisms, not an invocation of a construction hidden inside another node. Step 2 verifies injectivity, the kernel, and surjectivity of d by a finite descending recursion; it needs no non-elementary claim. In particular I checked n=1, when Q_1=0 and j_1 is the identity.

For Step 3 I opened the statement of lem-weil-pbc-mittag-leffler-limit-exact. Its clause (3) applies to a short exact sequence of positive-integer towers with ML first term and explicitly states that the limit map is surjective. Our first term is B, which is ML by the item's hypothesis, and Steps 1 and 2 establish every required compatibility and exactness condition. Thus it supplies precisely the surjectivity used, without assuming the transition maps of B are surjective. The definition of ML in def-weil-pbc-mittag-leffler-system was also read and agrees with the hypothesis.

Step 4 is the elementary prefix-limit calculation: each product coordinate is read at level i in P and level i+1 in Q, and compatibility proves independence at higher levels. This explicit identification checks the sign and index of x_i-g_i(x_(i+1)); it does not merely say that the two maps transport to one another. For Step 5 I opened lem-pc-derived-limit-roos-abelian-groups and read its statement: it gives coker(1-s)=R^1 lim and R^q lim=0 for q>=2 for ordinary abelian towers, exactly the two conclusions taken. Surjectivity makes that cokernel zero by the quotient definition. The three citations have full verbatim statement quotes in citations.json.

I checked the B--E failure patterns against the saved JSON: all non-elementary inputs are existing cited statements, no proof is moved into a new node, there is no circular appeal to ML acyclicity, and every proof dependency is the union of the step uses. The three elementary steps contain the actual finite-coordinate arguments and claim no independent deep result. All steps have fewer than 700 characters, so none falls under the long-step warning. The JSON contains single TeX backslashes after decoding. Existing unrelated metadata was retained.

Small cases checked directly: the zero tower gives zero products and cokernel; a constant tower with identity transitions gives the usual recursively solvable difference map; zero transitions give 1-s=1 even for infinite groups; and B_n=Z direct-sum Z with g_n(a,b)=(a,0) is ML with nonsurjective transitions, while the difference map is solved in its first coordinate by x_(n+1)=x_n-y_n and in the second by x_n=y_n. These confirm that finiteness and surjectivity have not been added. In contrast Z with multiplication-by-2 transitions is not ML (the images 2^r Z never stabilize), so Step 3 correctly cannot be invoked in that case. No Lean was written or compiled and no build tools were run.

## Unfinished work

None in the one-level split. Downstream proof work and independent maintainer review remain the project's responsibility. Required server preflight and delivery results are recorded by the delivery command.
