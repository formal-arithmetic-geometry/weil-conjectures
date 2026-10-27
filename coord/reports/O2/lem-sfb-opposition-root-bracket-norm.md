## Worker report

Stage 1, O2, 2026-10-24. Item: lem-sfb-opposition-root-bracket-norm. There was no earlier node, report, citations file, or searches log in this item's sandbox. The live item was unsplit with no proof. I retained its statement, source, inherited blueprint ancestry, and earlier searches and added a five-step proof. All writes are inside this sandbox. No Lean was written and no compiler, Lake, or build was run.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-opposition-root-bracket-norm.json: item, now split; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-killing-root-duality.json: new statement, unsplit; no exact Mathlib match for the full explicit split-Cartan/positive-definite duality statement.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-string-adjacent-length-ratio.json: new statement, unsplit; no exact Mathlib match for the adjacent-root length ratio for an arbitrary invariant positive form.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-string-endpoint-difference.json: new statement, Mathlib leaf, RootPairing.chainBotCoeff_sub_chainTopCoeff, Mathlib/LinearAlgebra/RootSystem/Chain.lean:405--422.
- citations.json: one entry for every node used by every item step, with verbatim statement text.
- searches.jsonl: actual msearch.py records; the JSON nodes retain the exact query text, results and verdicts. Both semantic services, Loogle and grep were used for every new node. Alternate phrasings were tried for both absent assertions.
- report.md: this report and review. write_split.py and check_small_cases.py are sandbox-only preparation and mathematical spot-check scripts, not delivery files.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, opposition, root-string and Chevalley vocabulary found no project declaration that states the item. The available Chevalley mentions concern other notions. Mathlib's GeckConstruction operators describe specifically constructed matrices and do not prove the item about arbitrary normalized vectors in a given rational Lie algebra.

## WANTED

WANTED: Casselman 2015 and Raghunathan 2015, proofs cited by Milne immediately after Theorem 23.71, for comparison with lem-sfb-opposition-root-bracket-norm. Neither is listed as obtained in literature/LIST.md. The delivery does not invoke either as a proved input. Its proof_origin is agent: Milne motivates the conditional local identity but gives no proof of it.

## Corrections and limitations

The statement needed no correction. In particular I kept arbitrary opposition-normalized vectors, rather than assuming the Chevalley basis whose construction uses this node in its parent. Milne 23.71 is about structure constants after choosing a basis; it cannot be applied directly here without an extra comparison argument. The new proof instead derives FE on the actual adjoint root string and then uses Killing duality and a root-length ratio.

The source gives the rank-two diagrams and invariant inner product, not the adjacent-length formula verbatim. That node is explicitly agent-formulated. Likewise the rational Killing-duality node makes the background Lie-theoretic identification an explicit obligation rather than claiming a literal quotation from Milne. The two new unsplit nodes are the remaining stage-1 frontier, and carry statements only; their proofs are not falsely represented as finished. There are no new Lean sorry declarations.

The blueprint ancestor command returned None. I preserved the live item's blueprint.from.node = null and its full via chain; the new nodes prepend this item to that chain. The current latest blueprint is main-20261024. Its direct-images proof (3) and the unit/chapter were read; the existing alteration/moduli/root-datum-realization chain is left in place. No unit or chapter file is changed.

## Not duplicates

Searches used tools/blueprint_refs.py search for root string, root-string, root string length, invariant bilinear, Killing, and Killing dual, as well as whole-DAG searches for the notions and declaration names. No imported blueprint node states any new assertion. Source Lean was searched before creating them. There are no Stacks tags to compare: the source here is Lie theory in Milne, not a Stacks theorem, and no SGA route is used.

lem-sfb-root-string-endpoint-difference vs lem-sfb-root-string-integer-interval: the existing leaf gives exactly the roots in the interval [-p,q], not p-q = the Cartan integer; the new leaf gives the latter only and does not restate the interval.
lem-sfb-root-string-adjacent-length-ratio vs lem-sfb-root-string-integer-interval: the existing leaf has no invariant form or squared-length identity.
lem-sfb-root-string-adjacent-length-ratio vs lem-sfb-chevalley-string-central-parity: the existing statement assumes a Chevalley basis and asserts centrality and integral half-sums; the new statement is purely about a root pairing and invariant form and assumes no Lie algebra or basis.
lem-sfb-root-string-adjacent-length-ratio vs lem-sfb-chevalley-adjoint-weyl-signs: the existing statement concerns Weyl operators on Chevalley vectors, not an identity between lengths in a root pairing.
lem-sfb-rational-killing-root-duality vs lem-sfb-split-semisimple-root-decomposition: the existing statement provides the decomposition, coroot pairing, nilpotence and generation, but no Killing restriction, inverse form, or opposite-bracket formula.
lem-sfb-rational-killing-root-duality vs lem-sfb-faithful-semisimple-trace-form: the existing theorem asserts nondegeneracy of a faithful representation trace form, not positivity on a split Cartan or compatibility with coroots and opposite brackets.
lem-sfb-rational-killing-root-duality vs lem-ag-killing-nondegenerate: the existing theorem is over algebraic l-adic coefficients and asserts only nondegeneracy; the new theorem is over Q and includes the explicit root duality and rational positivity.
lem-sfb-rational-killing-root-duality vs sk-lem-walg-killing: the latter asserts only semisimplicity implying nondegeneracy, without any split Cartan or root-duality clauses.
Each of the three new nodes vs lem-sfb-opposition-root-bracket-norm: none mentions the opposition involution or normalized pair u,v; none asserts the bracket norm. The item itself supplies the scalar recurrence, the opposition signs, and the final coroot coefficient. These are supporting inputs, not the item renamed.

## Review by O2

I read Milne Section 23h, printed pp.503--509, especially the actual statement and post-theorem proof reference of 23.71, and Appendix C Section g, printed pp.621--622, including table (180) and all four rank-two diagrams. I compared the current latest blueprint unit and direct-images proof (3) with the inherited place record. This supports the parent route but does not provide a local Lie-theoretic proof; the argument supplied here is marked agent-written.

For the Killing-duality node I read the source background and Mathlib/Algebra/Lie/Weights/Killing.lean:76--78,232--265, including cartanEquivDual, traceForm_coroot and lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux. These establish related assertions once Cartan and IsKilling interfaces are supplied. I did not mark the full new statement as a leaf: establishing those interfaces and rational positivity is additional work. Positivity here is on H and its inverse-dual form, never on the whole rational Lie algebra. A check on sl2 gives B(h,h)=8, B(e,f)=4, t_alpha=h/4 and d_alpha=1/2, hence h=2t_alpha/d_alpha and [e,f]=B(e,f)t_alpha with exactly the delivered normalization. The zero Lie algebra has H=0 and no roots; positivity and the root clauses are then vacuous. The anticipated justification is the trace sum of squared rational root evaluations on H, bracket invariance of trace, and the Killing-dual coroot characterization; those are the obligation retained in this unsplit node.

For the adjacent-length node I checked its independent-pair and positive reflection-invariant-form hypotheses against the rank-two diagrams. A1 x A1 has no pair whose sum is a root; A2 has equal lengths, while B2 and G2 include unequal lengths and internal string positions. The statement allows reducible ambient pairings since a sum-root pair is handled in its two-dimensional root subsystem. I tested all independent ordered pairs in the diagrams with exact rational Gram matrices: 8 in A1 x A1, 24 in A2, 48 in B2 and 120 in G2. All endpoint differences and interval descriptions passed; the length identity passed for 12, 24 and 60 sum-root pairs, respectively. In particular the potentially troublesome p=1,q=1 B2 short-root pair yields a long sum root and the factor 2 is correct. The G2 internal p=2,q=1 position also passed. These are edge-case checks of the new statement, not a claim that this statement-only node has been split.

For the endpoint-difference leaf I read Chain.lean:35--46 and 133--164 for the ambient and independence assumptions and endpoint characterization, and :405--422 for the exact equality. The statement is in integers and uses pairingIn Z j i, with the order beta,alpha; taking scalars in Q is a one-line specialization. This is a genuine leaf, unlike the two other new statements. Its edge cases include p=0, q=0 and orthogonal roots with p=q. The item uses it only where q>=1.

Step 1 uses the actual statement of lem-sfb-split-semisimple-root-decomposition: it supplies finite root-coroot families with perfect evaluation and simultaneous reflections, rather than merely naming a decomposition. Its split rational maximal abelian hypotheses are exactly the item's. The coroot line and normalization identify its coroots with the supplied h_alpha. The new Killing-duality statement has those same hypotheses and explicitly gives B, b, t_rho, positive d_rho, and both displayed identities taken from it. Independence is proved in the step from reducedness and the sum-root hypothesis; it is not assumed without justification.

Step 2 cites the interval leaf only for the interval, the new endpoint-difference leaf only for m=p-q, and the new length-ratio node only for q*d_gamma=(p+1)*d_beta. I opened each statement rather than using a proof or a search result as a citation. The positive invariant b comes from step 1; the required finite reduced crystallographic P and independence are also already established. The choice of q agrees with chainTopCoeff because the cited interval leaf characterizes its nonnegative endpoints.

Step 3 is marked non-elementary because it depends on the two root-string inputs, which it cites again, and the Lie algebra definition gives the adjoint/Jacobi identity. Its remaining content is written out as a finite scalar calculation. The one-dimensional spaces exist at every index by the interval; the absent adjacent endpoint weights are nonzero because alpha and beta are independent. There is consequently no hidden irreducibility, semisimplicity of an sl2 module, or assertion that a raising map is nonzero. Choosing bases gives scalar products c_k, with c_q=0; the commutator gives the difference equation and its finite sum proves FE(v)=q(p+1)v. This also checks the orientation of m and the sign of EF-FE. I corrected the draft classification of this contextual step from elementary to non-elementary and explicitly repeated the two root-string citations. No non-elementary step exceeds 2000 characters.

Step 4 cites the Killing-duality statement for symmetry, invariance, the opposite bracket and h_beta=2t_beta/d_beta. The rest is an elementary substitution written as an equation: -theta([u,v])=[-theta(u),theta(v)], so the skew-adjoint move contributes the second minus sign and gives a positive q(p+1). Applying beta, whose value on h_beta is 2, justifies scalar cancellation without assuming a particular coordinate choice. This step does not assume theta preserves a positive form, nor any positivity on all of g.

Step 5 cites that same node for the opposite-root formula and Killing-dual coroot identity. Jacobi gives the required weight of w, and theta's stated action gives its opposite. The final replacement uses the exact length equality already cited in step 2 and divides only by d_beta>0. The final nonzero claim follows from gamma(h_gamma)=2 and p+1 nonzero in Q; it does not presuppose that the bracket is nonzero. Both steps classified elementary after the cited inputs are explicit substitutions or finite bilinear calculations, with no uncited structural theorem.

I checked delivery-errors B--E against the files: all new nodes are self-contained statement-only records with empty proofs; no new definition has hollow data; the exact Mathlib declaration and source lines were read; no search was invented or an unavailable service described as no match; no Stacks tag is used for meaning; dependencies are the union of step uses; no child uses Chevalley normalization or the present item. The node statement is unchanged, and the two smaller structural obligations are not clauses of the item. The source hypotheses Q, characteristic zero, splitting, independence, reducedness, positive lengths, and q>=1 are accounted for at their applications. No correction to another worker's node is included. The maintainer's independent review remains responsible for acceptance.

## Validation

The first required server dry run exited successfully with OK at 54d55de6cdc. Before the final dry run I clarified that the scalar coefficients a_k,b_{k+1} are chosen only for k<q, set c_q=0 separately, and apply the difference equation for 1<=k<=q; this makes the endpoint indexing explicit.
