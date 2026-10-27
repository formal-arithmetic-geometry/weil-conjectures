## Worker report

Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-killing-root-duality.json`: statement split into eight calculation steps; statement and statement dependencies preserved; no whole-item Mathlib match.
- `citations.json`: ten verbatim statement quotations covering every proof-step citation.
- `searches.jsonl`: actual msearch output records, retained in full.

New nodes: none. New Mathlib leaves: none. The existing leaf `lem-sfb-finite-dimensional-perfect-pairing` supplies the only general theorem required beyond explicit short calculations and definitions.

Attachments: none. Project searches for the exact blueprint tag, Killing form, root duality and Cartan duality found `LieAlgebra.HasTrivialRadical.killingForm_nondegenerate` in `lean/WeilConjectures/Mathlib/Algebra/Lie/CartanCriterion.lean:82`, and the trace definition at `Radical.lean:68`. Neither gives all clauses of this item, so there is no attachment. No Lean was written and no compiler, Lake or build tool was run.

WANTED: none. Milne's cited PDF and all required Mathlib sources are available locally.

The input was statement-only and its statement is correct. Milne, *Algebraic Groups*, Section 23h, printed p.503 (PDF p.515), gives the split Cartan root decomposition; printed p.508 (PDF p.520) normalizes the coroot by root value 2 and gives the Chevalley-basis context for Theorem 23.71. These pages assume the underlying semisimple Lie theory; they do not contain this complete rational Killing-duality calculation. I therefore marked the proof as agent-written and supplied the missing computation, rather than attributing it to a printed proof. No change of statement, no source error and no route change are claimed.

Nothing mathematical remains unfinished in this one-level split. Its general perfect-pairing dependency is already a Mathlib leaf. The inherited `blueprint.from.node = null` was confirmed by `tools/blueprint_refs.py ancestor`; the inherited via chain and source place were retained, and split_report explains its place in that chain. I read the latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially proof (3); this linear-algebra input belongs to the existing long alteration prerequisite chain, not to a replacement for the unit proof.

## Searches and reuse

I searched the whole DAG for Killing, nondegenerate bilinear forms, duality, trace cyclicity, and finite-dimensional perfect pairings, and ran `tools/blueprint_refs.py search` for Killing, nondegenerate, bilinear and dual. The rational Killing-duality assertion has no identical imported blueprint node. `lem-ag-killing-nondegenerate` is a statement over the algebraic closure of a local field, so its statement cannot be applied as though it were over Q. I did not cite it. `lem-sfb-faithful-semisimple-trace-form` concerns full trace nondegeneracy and does not state the positive split restriction. Neither is necessary for the proof below.

Before making a potential auxiliary node for duality I searched for it and found `lem-sfb-finite-dimensional-perfect-pairing`; no new node was made. I opened its statement and read the Mathlib definition of `IsPerfPair` at `LinearAlgebra/PerfectPairing/Basic.lean:40-42` and `IsPerfPair.of_injective` at lines 116-120. These give exactly its two induced isomorphisms, including dimension zero. The related `BilinForm.toDual`, `toDual_def` and `apply_toDual_symm_apply` were read at `LinearAlgebra/BilinearForm/Properties.lean:349-363`.

All new Mathlib searches used msearch.py and their actual queries/results are recorded in the item's `mathlib_searches` and the search log. Both semantic phrasings of the item return related Cartan/IsKilling interfaces and root-system constructions. I read `Algebra/Lie/Weights/Killing.lean:76-78,232-285`. Those declarations require the Cartan/IsKilling interfaces, and they do not prove rational positivity directly under the explicit decomposition assumed here. RootPairing positivity is about a constructed root form, whose identification with this Killing form would require work. Thus the whole item is not a one-line Mathlib specialization. The auxiliary duality hits are already covered by the reused DAG leaf. No unavailable service was represented as a negative answer.

## Not duplicates

No new node is proposed, so there are no new/existing node pairs to distinguish.

## Review by Q22

I read the source pages and each cited node statement, with delivery-errors B-E open. The three statement definitions are the project's Lie algebra, semisimplicity as absence of nonzero solvable ideals, and ordinary matrix trace. The input already spells out its subalgebra, root spaces, decomposition and positivity convention; I introduced no alternative root-system definition or additional hypothesis. No SGA reference or trace route is used.

Step 1 cites `def-weil-endomorphism-trace` for the diagonal sum and `def-wf-lie-algebra` for the linear adjoint map. The displayed double sum proves trace cyclicity directly; this is not a hidden invocation of a general trace theorem. Bilinearity follows from the same sums.

Step 2 cites the same two statements: the Lie definition explicitly states that ad is a representation, hence ad[x,y]=AC-CA. The equality of the two triple traces is step 1 applied to C and AD. This proves the exact invariance identity with its stated order and sign.

Step 3 cites the trace definition only. The simultaneous eigenspace decomposition and one-dimensionality are hypotheses of the item, not facts obtained from an uncited structure theorem. A basis of H together with the root vectors gives a basis of L by that assumed direct sum. Its diagonal entries give the sum of root products. In particular no theorem identifying abstract Cartan data with those hypotheses is needed.

Step 4 cites the Lie definition and the semisimplicity definition. Each says exactly what is used: a central line is an ideal whose first derived subspace is zero, and semisimplicity excludes a nonzero such ideal. This proves that the roots jointly detect H; it does not assume without proof that they span its dual. Positivity uses the usual ordering on Q and finitely many nonnegative squares, one strictly positive. The same diagonal test proves separation in both arguments without any use of nondegeneracy on all of L.

Step 5 is the sole non-elementary step and cites `lem-sfb-finite-dimensional-perfect-pairing`. I checked both its vanishing hypotheses using step 4, with M=N=H and K=Q. H is a finite-dimensional subspace of finite-dimensional L, and the chosen H basis already supplies this directly. The lemma states that the actual curried maps are isomorphisms, not just an equality of dimensions. Its inverse is therefore linear, supplies every t_lambda uniquely, and preserves nonzero vectors. The positive dual form follows by evaluating the already positive restriction on this inverse image.

Step 6 cites the Jacobi and bracket conventions of `def-wf-lie-algebra`. The root-vector equations give zero weight for [x,y]. Its zero-weight space is H because a nonzero root functional has a nonzero value somewhere; comparison of components in the direct sum removes each nonzero-weight component. The displayed calculation uses [y,h]=rho(h)y, whose positive sign is necessary. Restricted nondegeneracy from step 4 then gives the full bracket identity, including x=0 or y=0. No root-pairing nondegeneracy theorem is needed.

Step 7 cites the same Lie node because it defines [I,J] as the span of brackets. Step 6 puts every generator in the line Qt_rho, so it puts the given h_rho there. Since rho is nonzero, t_rho is nonzero and d_rho is strictly positive; only then is division performed. Applying rho gives exactly the factor 2/d_rho. This proves the coroot formula from its assumed normalization rather than presupposing the formula to prove the bracket.

Step 8 uses preceding steps and bilinearity only. I wrote the coefficients of both cross terms and the final quadratic term explicitly. Their cancellation proves the asserted identity for arbitrary functionals, not just roots. It uses d_rho>0 from step 7 and never divides by b(lambda,lambda) or b(mu,mu), so zero functionals cause no exception.

Small cases checked: L=H=0 and R empty give vacuous strict positivity and the unique zero dual vector; all root clauses are vacuous. In sl_2(Q), with [h,e]=2e and [h,f]=-2f, the formulas give B(h,h)=8, B(e,f)=4, t_rho=h/4, d_rho=1/2 and 2t_rho/d_rho=h; the bracket formula gives [e,f]=h. Replacing rho by -rho changes t and h by a sign and leaves d unchanged. Direct sums merely add squares, so the argument does not assume that L is simple. Rationality is essential to the ordering argument, and is present throughout.

No new lemma hides in a long step: every step is below 500 characters. The only dimension/duality theorem has an explicit existing citation; the remaining steps are written matrix identities, uses of definitions, or short calculations from the assumed decomposition. There is no proof sketch in a new statement because there are no new statements. I corrected the initial temptation to use full Killing nondegeneracy or to create a new duality lemma by giving the elementary positivity argument and citing the existing pairing node. The citations file was checked against the actual statement strings. The only changed DAG file is the assigned item; all other files in the shared repository remain read-only.
