# Stage-1 delivery: lem-sfb-reductive-semisimple-rank-formula

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-reductive-semisimple-rank-formula.json`: existing statement, now split into five complete steps; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every step/node citation, including both kernel/flatness and smoothness/connectedness from the quotient theorem.
- `report.md` and the search log: report and actual Mathlib queries. No new nodes, no Mathlib leaves, no Lean files.

## Attachments

None. I searched `lean/WeilConjectures/` for the item id, maximal-torus names, semisimpleRank, central-torus and quotient-torus terminology. There is no declaration stating the item. The semisimple rank-counted determinant-weight results in Purity/RealSheaves/DetWeights concern representations, not this algebraic-group rank.

## WANTED

None for this split. All source pages used are available in `literature/milne-algebraic-groups_iAG2017.pdf`. The reused orbit theorem's source record mentions the corrected 2022 edition, but the assertions used here are also explicitly in the available 2017 edition: 5.23 (p.104), 7.4 (pp.139--140), and 7.11 (p.141). I read these pages in the local PDF.

## Findings and corrections

The item was unsplit with an empty proof, and the sandbox had no prior node, proof, report, citations or search log to recover. Its statement is correct and unchanged. I added the two explicitly named field/algebraic-closure definition nodes missing from stmt_deps, and the existing Krull-dimension definition that the statement uses. All original fields, source, creation record and inherited blueprint ancestry are retained.

An initially plausible citation to `lem-sfb-reductive-radical-quotient` would create a cycle: radical-quotient -> reductive-centre-multiplicative-type -> reductive-borel-pair-structure -> regular-cocharacter-borel-description -> borel-opposite-root-dichotomy -> reductive-rank-one-reflections -> this item. I do not cite it. The hypothesis already characterizes R as the largest smooth connected solvable normal subgroup once smoothness and connectedness of a torus have been cited, so Step 5 identifies the radical directly.

The imported unit record still refers to an older blueprint path. I read the latest unit at `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image proof. This item is a supporting algebraic-group input far below paragraph (3), through the already recorded alteration and invariant-theory chain. It is not the unit's key node and does not change the unit's statement or proof route. `blueprint_refs.py ancestor` returns None, matching the inherited null from.node. Whole-blueprint searches for "semisimple rank" and "maximal torus" return no matches. Broader searches and the whole DAG search revealed the existing quotient-image and orbit-dimension inputs, so there is no reason to introduce new nodes.

The required Mathlib searches were actually run with msearch.py and their results read. Loogle and grep return no matching torus results. LeanSearch returns module-rank quotient formulas and finitely generated abstract-group rank; the two LeanFinder phrasings return abstract subgroup results or Lie-algebra rank. None states this theorem about reductive group schemes in arbitrary characteristic. The inherited searches are retained and the five new logged searches are appended with exact tool/query strings.

## Not duplicates

No new nodes. In particular I reuse `lem-sfb-quotient-borel-torus-images`, `lem-sfb-algebraic-group-homomorphism-factorization` and `lem-sfb-smooth-group-orbit-geometry` instead of creating maximal-torus-image, quotient-identification or quotient-dimension nodes.

## Review by Q47

I read the item against Milne 17.61(a),(b), 17.20, Definition 19.20 and Proposition 19.21(a), printed pp.372, 357--358 and 401--402. The source proves centre containment using the scheme centralizer and computes rank by the dimension of the quotient torus. Our radical torus R is the smooth central torus, so this route works in positive characteristic without identifying R with the possibly nonreduced entire centre. No SGA route or source is used.

For Step 1 I opened `lem-sfb-reductive-torus-self-centralizer`: its statement gives equality of centralizer functors on all test algebras. Its field hypothesis is satisfied because F is algebraically closed, and geometric maximality is ordinary maximality here. A central element of C(A) centralizes T after every further algebra extension, precisely the quantifier in that statement. Thus the factorization through T is scheme-theoretic, not just a containment of F-points. This proves the assertion for every central torus, including R.

For Step 2 I opened `lem-sfb-multiplicative-type-largest-subtorus` and checked the sentence "Every torus is smooth and connected" against Milne 12.14 and its following paragraph, p.236. I opened `lem-sfb-affine-normal-quotient-geometry`; its statement gives kernel R, faithful flatness and finite presentation, as well as smoothness and geometric connectedness of Q. Those assertions are read in Milne 5.25--5.29, p.105. Centrality supplies normality, all groups are affine finite type as required, and reductivity supplies the smooth connected H. Since F is already algebraically closed there is no extra descent issue for connectedness.

For Step 3 I opened `lem-sfb-quotient-borel-torus-images`: it explicitly gives both maximality of the scheme image S and faithful flatness T -> S, without restricting the kernel. Milne 17.20 proves exactly this for connected group varieties, and Step 2 supplies that hypothesis for H and Q. I opened `lem-sfb-algebraic-group-homomorphism-factorization`: it explicitly identifies the image with the represented fppf quotient by the scheme kernel. Milne 5.39 and Remark 5.42, p.108, supply that identification. The restriction has kernel T intersect R, which equals R by Step 1 on every test algebra. This obtains the actual quotient torus as a closed subgroup of Q, not only a torus abstractly isogenous to it. These are existing statements, not facts borrowed from a node's proof.

For Step 4 I opened `lem-sfb-smooth-group-orbit-geometry`: it states the dimension formula with the scheme-theoretic stabilizer, allowing nonreduced stabilizers. The acting group is T, smooth and connected from Step 2; the target S is affine and finite type, hence separated, and the point is its identity. Multiplication composed with q_T defines an action by the homomorphism identity. Its orbit map is the surjective q_T, and its stabilizer is the scheme kernel R on all algebras. Thus the quoted orbit-dimension formula has precisely the objects used in the step. I read the orbit/quotient assertions in Milne 7.4 and 7.11 together with 5.23. I also opened `def-kun-topological-krull-dimension`: its definition depends only on the topology. This justifies replacing the reduced orbit by S for dimension without asserting an unproved equality of schemes or citing an unnecessary reducedness theorem.

Step 5 is elementary assembly: the maximal torus S computes rank by the definition in the item, and R is smooth connected normal solvable by the preceding step and commutativity of products of unit groups. The maximality hypothesis is exactly the radical characterization, so Definition 19.20 identifies the resulting rank with semisimple rank. No separate existence or radical-quotient theorem is used. The arithmetic is substitution of dim S, not another hidden dimension theorem.

For the B--E checks, no new statement-only nodes or duplicate clauses have been created; every non-elementary assertion in the five steps is an explicit cited statement, with verbatim excerpts in citations.json. All proof dependencies are their union and I checked that their dependency closures do not reach the item. All six cited statement nodes are in the item's unit; the seventh citation is an existing definition of Krull dimension, which is exempt from the proof-route restriction. The statement dependencies retain the quotient and reductivity definitions that the statement actually uses. No proof step exceeds 2000 characters. The argument is an assembly of existing inputs with explicit kernel, orbit and radical calculations, not a relabelling of the item into a new node.

Small cases: for H=1 all tori and Q are trivial and the formula reads 0=0. For H a torus the maximality hypothesis forces R=H, and T/R=1 has rank zero. For a semisimple group R=1 and the formula reads rank H=dim T. For GL_n the scalar radical is one-dimensional and gives n-1, including n=1. In characteristic p, SL_p may have nonreduced centre mu_p; the proof uses the radical torus, not that centre, and preserves all scheme kernels on nonreduced algebras. These cases expose no missing smoothness, characteristic or positive-rank hypothesis.

## Unfinished work

None in this item's one-level split. Existing unsplit dependencies remain items in their own right; no new lemma was needed.
