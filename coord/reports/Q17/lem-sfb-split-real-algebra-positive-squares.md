## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-split-real-algebra-positive-squares.json`: item, split with its original statement unchanged and four proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-positive-definite-feasibility.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-positive-definite-gram.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `citations.json`: a verbatim statement quotation for each of the three step citations.

Attachments: none. Searches under `lean/WeilConjectures/` for the item tag, split-real algebras, sums of squares, positivity, rational matrices and Gram matrices found no declaration stating the item or either auxiliary. The trace-energy sum-of-squares results concern real trace energies, not elements of a rational algebra; the rational perfect pairing code concerns nonsingularity, not positive definite rational feasibility or Gram factorization.

WANTED: a human-written reference proving rational strict feasibility for symmetric matrix equations and rational rectangular Gram factorization, for the two new nodes. No unidentified theorem is attributed to an unavailable book: complete agent arguments are recorded below.

The old item was statement-only. Its source already explicitly calls it an agent auxiliary rather than a theorem of Milne. I read Milne, *Abelian Varieties*, II §1, proof of Lemma 1.3, printed pp.77–78 (PDF pages 83–84): it discusses finite rational algebras, their real extensions, and positive involutions; it does not assert the present sum-of-squares theorem. I preserved that distinction in every source field and marked the item's proof `by: agent`. No Stacks tag is claimed: these are rational linear algebra auxiliaries, not a Stacks theorem that has been assigned a guessed tag. No SGA source is used.

Nothing remains unfinished in this one-level split. The two new nodes deliberately have statements only and no proof dependencies. Their proofs below are handover material for their future splitters, not hidden proof text in their JSON statements.

## Argument for the item

Choose a rational basis of C. Its coordinate maps extend to C tensor R by (c,t) ↦ λ(c)t. Bilinearity shows both that the extended basis spans and that the coordinate maps are its dual. This also proves that the scalar inclusion c ↦ c tensor 1 is injective, without citing an unrelated faithfully flat theorem. An empty rational basis means C is the zero ring and one zero square suffices.

For the nonempty case write the split-real coordinate idempotents e_i in that basis, with real coordinate columns t_i. They form a real basis. If x_i are the strictly positive coordinates of x, put G = Σ_i x_i t_i t_iᵀ. For a nonzero real vector z, at least one dot product z·t_i is nonzero, so zᵀGz = Σ_i x_i(z·t_i)² > 0. Contract G with the multiplication table b_a b_b. The contraction is Σ_i x_i e_i² = Σ_i x_i e_i = x tensor 1. This is the key algebra-specific construction, and it stays in the item's own proof.

The coordinates of the multiplication table define a rational linear map from symmetric matrices to Q^n. The constructed G is a positive definite real solution of the equation prescribing the rational coordinate vector of x. The feasibility auxiliary yields a rational positive definite solution H of those exact equations. The Gram auxiliary writes H as Σ_k v_kv_kᵀ with rational v_k. Setting q_k = Σ_a(v_k)_a b_a and expanding gives Σ_k q_k² = x in C. Append a zero square to ensure at least one summand. Approximation is used only to obtain H inside the exact affine fibre, never to replace the final equality by an approximation.

## Handover argument for rational feasibility

Use the upper-triangular coordinates of a symmetric matrix. The equation L(H)=b is an ordinary finite rational linear system. Row reduction over Q has the same pivot pattern over R, because all nonzero rational pivots remain nonzero. Existence of the real solution rules out every inconsistent row. Taking all free variables zero gives a rational particular solution H_0. Taking one free variable at a time equal to 1 gives rational kernel vectors K_1,...,K_s, whose real images span the real kernel by the same row reduction. Thus every real solution, in particular G, is H_0 + Σ_j α_j K_j for real α_j.

For n>0, the continuous function z ↦ zᵀGz on the Euclidean unit sphere has a positive minimum δ: the sphere is compact and every value is positive. If a symmetric perturbation E has each entry of absolute value less than δ/(2n), then |zᵀEz| ≤ max|E_ab| (Σ_a |z_a|)² ≤ n max|E_ab| ||z||² < δ||z||²/2, so G+E remains positive definite. Choose rational coefficients a_j close enough to α_j that E = Σ_j(a_j−α_j)K_j satisfies this entry bound. For example, if s>0 set B = 1+Σ_j max_ab|(K_j)_ab| and take |a_j−α_j| < δ/(2nB). Density of Q in R gives these finitely many choices. H=H_0+Σ_j a_jK_j is rational, satisfies L(H)=b exactly, and is positive definite. If s=0, H=H_0=G. If n=0 there is only the empty matrix, the positivity condition is vacuous, and real consistency says b=0. The empty matrix is already the required rational solution. The case m=0 is included without an equation.

## Handover argument for rational Gram decomposition

Induct on n. For n=0 use r=0. For n>0 write H in blocks as [[a,uᵀ],[u,B]]. Positive definiteness gives a>0. The rational Schur complement S=B−uuᵀ/a is positive definite over R, because for nonzero z its quadratic value is the value of H at the nonzero vector (−uᵀz/a,z). The exact block identity is

H = a wwᵀ + diag(0,S),  where w=(1,u/a).

Write the positive rational a=A/D with positive integers A,D. Then a is the sum of AD copies of (1/D)². Consequently a wwᵀ is the sum of AD rational outer products (w/D)(w/D)ᵀ. By induction S is a finite sum of rational outer products; extend their vectors by a zero first coordinate. The displayed block identity combines the two finite lists, proving H=Σ_k v_kv_kᵀ. This proof requires neither irrational square roots nor Lagrange's four-square theorem. It also explains why a square rational Cholesky factor is not asserted: H=[2] has no 1-by-1 rational square factor but is [1][1]ᵀ+[1][1]ᵀ.

## Mathlib and duplicate searches

The commands used were exclusively the required `msearch.py Q17 lem-sfb-split-real-algebra-positive-squares ...`; their unmodified results are logged in `searches.jsonl`. Each JSON record names the exact tool and exact query executed. For every new node and the item I tried two semantic phrasings before the no-match verdict. All services used here returned successfully. The grep log for a single file misparses displayed file/line columns; that query was supplemented with directory searches and I read the actual source directly.

I read `Matrix.PosDef` in `Mathlib/LinearAlgebra/Matrix/PosDef.lean:161` and its immediate consequences. They define and preserve positivity but do not construct a rational point of an affine fibre. I read `QuadraticForm.equivalent_weightedSumSquares` in `Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean:172`: it diagonalizes over a field but neither proves that its weights are positive nor removes them to produce rational vectors. Both are additional arguments, so it is not an exact match or a one-line specialization of the Gram node. `LDL.lower_conj_diag` in `Mathlib/Analysis/Matrix/LDL.lean:115` and the square Gram characterizations in `Mathlib/Analysis/Matrix/Order.lean` are under `RCLike` hypotheses. Q is excluded; passing through R loses the rational factors. `IsSumSq` and `RingPreordering.mem_of_isSumSq` supply definitions and the forward direction, not strict positivity implying sum of squares in C.

Before creating the two ids I searched all `dag/nodes/` and the project Lean by the matrix concepts and names, and parsed node statements to exclude matches that occur only in inherited proof text. I searched the entire imported blueprint with `tools/blueprint_refs.py search 'sum of squares'`, `'positive definite'`, and `'rational matrix'`, and searched all current blueprint Markdown. The sole sum-of-squares blueprint hit is the unrelated trace-energy result `lem-fd-l2-middle-extension`; the two matrix searches returned zero. The ancestor command reports `blueprint.from.node = None` for this pre-existing agent auxiliary. I preserved that inherited null and its full chain, prepending the item in the new nodes' `via`, and gave each a precise place within the algebraic auxiliary.

I read the chapter record and the unit record `sk-thm-sf-ctf-stability`, then the current unit under `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` (latest snapshot ef6f9619fdbffa59e88528fb56483d76c70258c8). The generic algebra auxiliary is already introduced below that unit through the abelian endomorphism-span chain. No chapter/unit statement or route is changed, and no off-unit theorem is used.

## Not duplicates

lem-sfb-rational-positive-definite-feasibility vs lem-sfb-split-real-algebra-positive-squares: the new statement concerns rational solutions of an arbitrary linear system on symmetric matrices; it neither mentions an algebra nor asserts that an algebra element is a sum of squares. The item's construction of a strictly feasible matrix is still necessary.

lem-sfb-rational-positive-definite-gram vs lem-sfb-split-real-algebra-positive-squares: the new statement factors a given rational positive definite matrix. It does not construct that matrix from a split algebra or identify its multiplication contraction with x.

lem-sfb-rational-positive-definite-feasibility vs lem-sfb-rational-positive-definite-gram: the former finds a rational point in an exact affine fibre, while the latter decomposes a supplied rational point and has no system L or right-hand side b.

lem-sfb-rational-positive-definite-gram vs lem-sfb-positive-form-lattice-sublevels-finite: the existing statement bounds lattice sublevels of a form, not a rational factorization.

lem-sfb-rational-positive-definite-feasibility vs lem-sfb-rational-killing-root-duality: the existing statement concerns Killing forms and root duality, not rational points in an affine matrix fibre.

## Review by Q17

I checked B–E with the item, both new statements, and the three cited statements open. Milne II §1 Lemma 1.3 was read on printed pp.77–78 for the item and both new nodes. It supplies the motivation, not any of these three assertions. The new matrix statements are explicitly agent auxiliaries, with their actual arguments above and no fabricated Stacks label. Both introduce their own finite sizes, scalars, matrices, positivity inequality and conclusions; feasibility also defines scalar extension by its coordinate formula. They have no proof or proof dependencies, as required for a one-level split. Their elementary matrix notions are defined inline. Both cite the existing field definition `def-weil-field` for the rational and real scalar fields; I opened its statement (a nonzero commutative ring with inverses for all nonzero elements) and verified that these are exactly the fields used. No new definition node is needed. Both ids were absent from the live DAG before writing.

Step 1 cites only `def-weil-pbc-module-tensor-product`. I read its full statement: it provides precisely the bilinear universal property needed to extend λ_j, as well as generation by pure tensors needed to check the reconstruction identity. The spanning and dual-coordinate identities are written out rather than asserted by a tensor-basis theorem. Step 2 has no cited theorem: in the explicitly given product algebra the e_i are idempotents and a basis, so the displayed finite sums prove both positive definiteness and contraction. Orthogonality to a spanning set implies orthogonality to z itself, and Σ z_a²=0 implies z=0. These are direct finite-coordinate computations, so steps 1 and 2 are elementary, although they contain the item's algebra-specific idea.

Step 3 uses exactly `lem-sfb-rational-positive-definite-feasibility`. I checked its hypothesis L is rational linear by the rational multiplication table; its size is n with m=n; its real extension has the identical structure constants; the equation follows by the coordinate functionals from step 1; and G is strictly positive by step 2. Its statement really returns a rational H satisfying the exact rational equation and strict real positivity, which are the two things step 3 takes. Step 4 uses exactly `lem-sfb-rational-positive-definite-gram`, whose statement returns a finite list of rational vectors and the entrywise rational equality used in the expansion. H is symmetric and strictly positive by step 3. The remaining conversion q_k=Σ_a(v_k)_a b_a is an explicit distributivity calculation in the commutative algebra C, not an uncited comparison theorem. The quotation file copies the full statements verbatim, covering every clause used.

For E I checked the zero algebra/empty basis first: r=1 and q_1=0 satisfies the conclusion. For C=Q and x=2 the construction gives G=H=[2], and the Gram lemma permits two rational vectors [1], [1]; it never demands a rational square root of 2. In C=Q×Q, x=(1,2) gives the diagonal matrix and the squares (1,0),(0,1),(0,1). In Q(sqrt(2)), sqrt(2) itself is excluded because one coordinate is negative, while 2+sqrt(2) has both positive and the construction applies. I also checked the helpers at n=0, m=0, a zero-dimensional affine fibre, and the first nontrivial 2-by-2 Schur-complement step. Strict positivity is essential in the feasibility argument; no positive-semidefinite relaxation was silently used. All denominators in the Gram argument are nonzero because a>0. No domain assumption on C is used, so products and the zero ring remain included.

I corrected the tempting but invalid shortcut of using the RCLike Gram theorem to get rational factors: the delivered split instead leaves the rational Gram input as its own statement-only node with the rational Schur-complement argument above. There are no statement disputes, weakened hypotheses, circular citations, or long steps over 2000 characters (lengths are 582, 722, 692, 528). The two genuine linear algebra facts are each isolated as a reusable lemma, while basis-coordinate identities, finite sums, and the final ring calculation remain steps. This is my direct-delivery review; no second worker or other agent was started.

## Dry-run repairs

The first dry run required an explicit notion citation in each new statement. I added `def-weil-field` to both statements and their `stmt_deps`, after reading its actual definition; the matrix notions remain defined inline. I refreshed the verbatim quotation file and reran the required dry run. No mathematical hypothesis or conclusion changed.
