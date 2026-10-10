# Worker report: lem-weil-pbc-p-basis-differentials-basis

1. Files written:
   - dag/nodes/sec-proper-base-change/lem-weil-pbc-p-basis-differentials-basis.json: statement unchanged; four proof steps; no new nodes.
   - This report.
2. Attachments: none; the item's Lean audit is none on both branches.
3. WANTED: none. I read /tmp/stacks-project/more-algebra.tex, Definition 07P1 (definition-p-basis, lines 11344-11355) and Lemma 07P2 (lemma-p-basis, lines 11363-11413), and the supporting Algebra 00RS (lemma-exact-sequence-differentials), 00RU (lemma-differential-seq) and 00RX (lemma-differentials-polynomial-ring). All five tag-label pairs were checked in /tmp/stacks-project/tags/tags.
4. The imported node had no proof. Its statement agrees with 07P2 (a) implies (b). The source compresses the argument into the quotient presentation and the word "hence"; the proof now checks the presentation for an arbitrary index set and computes the differentials of the relations. The source checkout is available at /tmp/stacks-project, not the unmaterialized literature/stacks-project path in this worktree. No error in the unit or statement was found.
5. No mathematical work remains on this split. The cited Mathlib leaves were already present and their public statements were read; the existing item has LeanSearch, LeanFinder/Loogle and source-grep searches with no direct p-basis match.

B-E checks:

- B1-B8: no new nodes. The item already introduces the field extension, the monomial basis and Kähler differentials; its existing definition dependencies are unchanged. Each TeX command has one backslash after JSON decoding, and the proof cites exact Stacks tags and TeX labels.
- C1-C8: Step 1 uses only the universal derivation in def-weil-pbc-kahler-differentials. Step 2 uses the polynomial ring and evaluation map stated by def-weil-pbc-mv-polynomial-ring; the normal-form and independence argument is in the step. Step 3 uses the arbitrary-variable polynomial differential basis and the quotient conormal exact sequence exactly as stated by their nodes. Step 4 uses the first exact sequence exactly as stated by its node. All are existing nodes in the item's unit, so there is no duplicate, cross-unit route change or new cycle. The DAG search included p-basis, 07P2, polynomial differentials and quotient differentials.
- D1-D5: the four steps keep the proof in this item. The source's omitted "hence" is expanded into quotient normal form, zero differential of each defining relation and the comparison from base \(kK^p\) back to \(k\). No child restates the conclusion and there is no circular citation.
- E1-E7: the sole algebraic hypothesis used to kill the relations is characteristic \(p\); the monomial basis hypothesis gives both surjectivity and injectivity of \(B[X_i]/(X_i^p-t_i^p)\to K\). The finite-support reduction works for infinite \(I\); for \(I=\varnothing\), it gives \(B=K\) and both differential modules are zero. The field \(B=kK^p\), not \(K^p\), is used throughout, so \(k\) need not be perfect. The first exact sequence is needed because \(\Omega_{B/k}\) itself need not vanish; only its image in \(\Omega_{K/k}\) does.

Verification: python3 tools/review_split.py lem-weil-pbc-p-basis-differentials-basis PASS, 0 new nodes. python3 tools/check_dag.py --cycles reports 0 cycles and 0 self-loops, with seven unrelated pre-existing reach warnings. JSON parsed successfully. No Lean build, git operation or server access was run.

## Review by F1

I read More on Algebra Definition 07P1 and Lemma 07P2, implication (a) to (b), together with the cited public statements for polynomial differentials (Algebra 00RX), the quotient differential sequence (00RU), and the first differential sequence (00RS). The item's field-extension, characteristic-p and monomial-basis hypotheses agree with 07P2. There are no new nodes; B1-B8 and duplicate-node check C5 are vacuous.

Step 1 calculates that the universal k-derivation kills both k and K^p, hence the intermediate field B=kK^p. Step 2 uses finite-support monomial reduction and the hypothesis that the t-monomials are a B-basis to prove the displayed quotient presentation. Step 3 invokes exactly the public polynomial-basis and quotient-sequence statements and calculates d(X_i^p-t_i^p)=0 and d(J)=0, making Omega(K/B) free on dt_i. Step 4 invokes the public first exact sequence: the map from K tensor Omega(B/k) is zero by Step 1, so Omega(K/k) maps isomorphically to Omega(K/B). No step relies on a cited node's internal proof or substitutes a restatement of the conclusion (C1-C4, D1-D5).

I checked I empty, infinitely many t_i, nonperfect k and the possible nonzero module Omega(B/k). The proof kills only its image in Omega(K/k), as required; it uses the characteristic-p assumption exactly when differentiating the pth-power relations (E1-E6). The worker needed no correction. review_split passes and the seven DAG reachability warnings are unrelated (A, F).
