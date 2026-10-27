# Stage-1 report: lem-trf-componentwise-finite-set-affine-neighbourhood

1. Files written:
   - dag/nodes/sec-trace-formula/lem-trf-componentwise-finite-set-affine-neighbourhood.json: item, split into six proof steps, no Mathlib match.
   - dag/nodes/sec-trace-formula/lem-trf-quotient-lift-finite-prime-avoidance.json: one new statement-only node, unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and source grep.
   - citations.json: one complete verbatim statement quotation for each use in each item step.
   - report.md and searches.jsonl: review and actual logged searches. write_split.py is the sandbox-only generation script.
2. Attachments: none. The tag and concept searches in lean/WeilConjectures found generic-point neighbourhoods (Mathlib/AlgebraicGeometry/Properties.lean), quasi-projective neighbourhoods (AlgebraicGeometry/ProjectiveSpace/AffineNeighbourhood.lean), and affine finite-closed-cover assembly (AlgebraicGeometry/IsAffineOfFiniteClosedCover.lean). None states this arbitrary-scheme simultaneous-neighbourhood theorem. No project declaration matching the independent 09NK algebra lemma was found either.
3. WANTED: none. All proofs follow the locally available Stacks sources.
4. The item statement is correct and unchanged. Its seeded dependency list is retained. The proof was empty. Tag 09NM's symmetric second shrinking has a typo, corrected below. The blueprint ancestor provenance points to an old contraction paragraph no longer present in the main-20261015 ancestor; the established created-item chain and the precise current Stacks source are retained rather than inventing a new blueprint quotation or changing the unit route.
5. Unfinished mathematics: only the new independent 09NK statement is left unsplit, as stage 1 requires. No Lean was written or compiler run.

## Source error

In varieties.tex, Tag 09NM (lemma-finite-set-codim-1-points-in-affine-per-component), the second shrinking prints

$\Delta'=(U\cap(Z_1\cup\cdots\cup Z_{r-1}))\setminus(U\cap V)$.

Because $U\subseteq Z_1\cup\cdots\cup Z_{r-1}$, this is $U\setminus V$. It need not be a subset of $V$, so it cannot be the closed subset of $V$ excluded by choosing $h\in\mathcal O(V)$. For example, even disjoint affine components give $U\setminus V=U$ outside $V$. The intended symmetric formula is $(V\cap(Z_1\cup\cdots\cup Z_{r-1}))\setminus U$, which is closed in $V$ and misses $T$. Step 4 explicitly uses this corrected formula. This repairs the proof without changing the true statement, so there is no statement dispute.

The same paragraph's application of 09NK must be restricted to points of $T\cap U$ outside the closed overlap $W$: at points on $W$, its hypothesis $I\not\subseteq\mathfrak p_t$ fails. There nonvanishing follows instead from the prescribed restriction $g|_W=h|_W$ and $T\cap B\subseteq D(h)$. Step 5 separates these two checks.

## Not duplicates

lem-trf-quotient-lift-finite-prime-avoidance vs lem-weil-pbc-prime-avoidance: the existing Tag 00DS statement chooses an element in an ideal avoiding finitely many primes; the new Tag 09NK statement prescribes an arbitrary class modulo a separate ideal and chooses a representative avoiding the primes. The product-ideal correction argument is needed and is not a one-line specialization.

lem-trf-quotient-lift-finite-prime-avoidance vs lem-trf-componentwise-finite-set-affine-neighbourhood: the new lemma concerns arbitrary commutative rings and cosets, with no schemes, components, or affine-neighbourhood assertion. It is the independent algebraic lifting tool in the induction, not a clause of the item.

Searches over all DAG statements for quotient lifts, cosets, residue classes and prime avoidance and over the imported blueprint for 09NK, 09NM, residue class, quotient, avoiding and finite set found no duplicate. Existing 09NL (lem-sc-closed-affine-union-affine) and 06AD (lem-weil-pbc-thickening-affine-scheme) are cited directly, not recreated.

## Review by O4

I read varieties.tex Tag 09NM in full, including its induction, and the adjacent 09NK statement and proof. For the reusable geometric facts I read limits.tex Proposition 05YU (proposition-affine) and Lemma 09NL (lemma-affines-glued-in-closed-affine), together with the existing 06AD thickening node statement. I read all statements cited by the six steps, not just their source labels. The new lemma is exactly 09NK with the empty-family and zero-ring cases made explicit, and carries no proof or proof dependencies.

Step 1 takes reducedness, the surjective closed immersion and the underlying homeomorphism exactly from lem-weil-pbc-reduction-universal-homeomorphism. The radical quotient and uniqueness clauses of lem-weil-pbc-reduced-induced-closed-subscheme justify the unchanged component structures. The affine closed-immersion clause of def-weil-closed-immersion applies after restriction to the corresponding open of X; lem-weil-pbc-thickening-affine-scheme expressly allows arbitrary thickenings, so no unmentioned nilpotence or Noetherian assumption is needed. In affine charts the restriction of the reduction is precisely the quotient by the nilradical, proving the required surjective closed immersion.

Step 2 states the induction claim on each finite union Y_r, the empty base, the first-component base and the full induction hypothesis. Reduced induced closed structures come from the same node. The empty-cover clause of lem-sc-closed-affine-union-affine covers the empty scheme. No new lemma repeating the induction claim is created.

Step 3 uses the radical-ideal description of a closed subset in an affine scheme from lem-weil-pbc-reduced-induced-closed-subscheme, genuine finite prime avoidance from lem-weil-pbc-prime-avoidance, and both clauses of lem-weil-pbc-affine-open-section-vanishing-prime (prime membership and affine principal opens). Delta is closed because it is U intersect the closed subset B minus its open V. T misses it because every T-point of B lies in V. These checks verify each hypothesis of prime avoidance. With no prescribed points, f=0 suffices, so the existing lemma's nonempty-family restriction is respected.

Step 4 uses precisely the same three cited statements on the affine V, with the corrected symmetric closed subset V intersect (A minus U). Every T-point in A lies in the induction open, so the subset misses T and prime avoidance applies; the empty set again permits h=0. The equality V_h intersect A = W intersect D(h) is a direct equality of subsets, not an unexplained transport theorem.

Step 5 takes the surjective quotient description of the closed W in U from def-weil-closed-immersion. The new 09NK node gives a lift only at the finite family of primes corresponding to points outside W, where I is indeed not contained in those primes. At points on W I checked nonvanishing separately from h and equality in the same residue field. The principal-open node gives affineness and the point criterion for D(g). Because both W restrictions are the same element of R/I, their nonvanishing loci agree, yielding the exact common intersection needed next.

Step 6 writes out why the union is open in Y: compatibility makes its complement the union of two subsets closed in the closed A and B. Its intersections with A and B are exactly the constructed principal opens, so these are affine closed subschemes of that union. Their scheme structures agree by the radical-ideal construction and uniqueness of the cited reduced-induced-structure node. Thus the statement of lem-sc-closed-affine-union-affine applies directly to a finite closed cover, not to an arbitrary affine open cover. This distinction is essential. The induction then reaches the whole reduction, and Step 1 returns to X.

For the new 09NK node I checked the source's argument: discard primes contained in others; lift the class arbitrarily to a, let S be the primes containing a, and form J = I times the product of the other primes. Primality and incomparability imply J is not contained in any prime indexed by S. Ordinary 00DS supplies b in J avoiding those primes. Then a+b remains the given class, is outside primes in S, and remains outside the other primes since b lies in them. This is a separate algebraic argument, recorded here for the future worker, not hidden as a proof in the new statement-only node.

Small cases checked: r=0 in 09NK uses any representative, including in the zero ring; repeated or nested primes are handled by retaining inclusion-maximal primes, and I=0 is possible only with no primes. For instance A=Z, I=(2), p=(3) allows every residue class; dropping the hypothesis with I=0, p=(3), class 0 would be false. In the item, X empty/s=0, T empty, one component, disjoint components, and points on several components all work in the written induction. Nonreduced schemes with unbounded nilpotence are covered by the arbitrary-thickening criterion. No assumption that intersections of affine opens are affine is used: the overlap becomes affine specifically because it is closed in U.

I checked delivery-errors B through E against the actual files: the sole new node has a self-contained statement and no proof; its ordinary algebra notions are defined inline; all searches are actual logged queries and candidate hypotheses were read; every non-elementary ingredient is a cited statement; all citations have verbatim quotations in citations.json; no clause of the item was repackaged as a helper. Each of the six steps has fewer than 1000 characters, and none hides a further independent comparison lemma. The off-unit affine assembly, thickening and principal-open tools are declared in split_report.tool_uses because they are generic tools absent from this trace unit; they preserve the branch's specified Stacks reduction route.

The first dry run required an explicit notion dependency for the new algebraic statement. I added the prime-spectrum interpretation of its prime ideals, citing def-weil-affine-spectrum, whose statement expressly identifies the points of Spec A with the prime ideals of A. Ideal, prime ideal and quotient-class meanings remain defined inline. Regenerated the verbatim item citation of the updated new node. This is a real statement dependency, not an unrelated theorem citation.
