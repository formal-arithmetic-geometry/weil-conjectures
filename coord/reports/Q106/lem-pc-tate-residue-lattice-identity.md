## Files written

- `dag/nodes/sec-picard-framework/lem-pc-tate-residue-lattice-identity.json`: statement; split, with eight proof steps. Statement unchanged. Mathlib verdict: no match.
- `citations.json`: a verbatim statement quotation for every citation in all eight steps.
- No new nodes and no new Mathlib leaves. No unit record is changed: this item is not the unit's statement node.

## Attachments

No whole-item attachment. I read the project's `WeilConjectures/RingTheory/TateResidue/ResidueProperties.lean`, especially the hypotheses at lines 49–52, `res_eq_add_of_exact` at line 55, `Admissible.prod` at line 120, and `TateResidue.res_sup_add_res_inf` at line 143. The last theorem is sorry-free in its displayed proof and gives the residue equality in the reverse direction under exactly the relevant algebra/module/admissibility assumptions. However, its conclusion does not assert admissibility of the sum or intersection. The residue function is defined as zero for inadmissible subspaces (`Residue.lean`, lines 327–348), so merely mentioning these residues does not supply those clauses. There is no named `Admissible.sup` or `Admissible.inf` in these modules; the exact-sequence theorem proves such intermediate admissibility facts locally in its proof, which is not a public statement I can attach. Thus the brief's every-clause requirement prevents an ATTACH answer. No Lean is written or compiled.

The maintainer can retain `TateResidue.res_sup_add_res_inf`, `WeilConjectures/RingTheory/TateResidue/ResidueProperties.lean:143`, as evidence that the equality clause already has a project proof. I am not claiming that it states the entire item.

## WANTED

None. I read the available Tate paper directly, converting it into the sandbox's `tate.txt`; no literature was downloaded.

## Errors and corrections

The item statement agrees with Tate's property R5 on printed p.153, including both admissibility conclusions. There is no statement dispute and no statement change. The source's numbering differs from the upstream Lean module: the paper's R5 is the module's R3; the existing source field already records this correctly.

The imported proof was empty. I supplied Tate's compatible-projection argument, including the finite-dimensional subspaces needed to justify trace subtraction. Additivity of the trace on arbitrary finite-potent operators would be an invalid shortcut and is never used. The existing `lem-pc-finite-potent-trace-calculus` only states a pairwise finite-rank additivity clause, so I do not cite that clause for the length-three products used here. I instead use its explicit characterization by restriction to a finite invariant subspace. The eight length-three images give such a subspace, with an explicit invariance argument; matrix subtraction then gives the desired trace differences.

The current main-20261015 blueprint unit's residue/cokernel-trace statement and the chapter record were read. They supply the same Tate residue route. Its statement is not a separate statement of this abstract sum/intersection identity. Neither chapter nor unit route is changed. The existing `blueprint.from` is retained and `same_as` is `[]` after whole-blueprint searches.

## Unfinished work

None for this one-level stage-1 split. Its existing dependencies retain their own stage states. The natural-language proof is complete relative to their statements.

## Searches and reuse

I searched the whole DAG for Tate residue, finite-potent trace, exact-sequence residue and the source numbering, and used `tools/blueprint_refs.py search` for `tate residue lattice identity`, `Tate`, `finite-potent`, `residue exact`, `finite-potent trace`, `trace filtration`, `finite potent`, `sum intersection residue`, and `T4`. The broad `Tate` search includes `sk-thm-picard-duality`; I read that unit and its current main-20261015 source. No blueprint node separately states this identity or the trace-linearity subclaim. The project's explicit theorem is discussed in Attachments.

The required `msearch.py Q106 lem-pc-tate-residue-lattice-identity ...` searches are in `searches.jsonl`; the item's original searches are preserved, and new item-specific searches are appended to `mathlib_searches`. Both natural-language phrasings returned residue-field/valuation or finite-sum/annihilator results. Loogle for `"res_sup_add_res_inf"` returned zero hits; grep for `finite.?potent|tateTrace|res_sup_add_res_inf` returned zero hits. The semantic search results are not differential-residue maps. Searches for a possible trace helper returned ordinary finite-dimensional matrix/linear-map trace and field trace, not Tate trace. In particular `LinearMap.trace` and `Matrix.trace_add` do not assert the relevant infinite-dimensional result. No unavailable result was classified as absence.

After reading `lem-pc-finite-potent-trace-calculus` in full, I recognized that its finite-invariant-subspace characterization already supports the required computation. Its statement determines the trace of every operator in each of our two-dimensional spans on the explicit common finite-dimensional subspace. A proposed new general T4 or almost-filtration node would therefore be unnecessary here. No candidate node was written or delivered.

## Not duplicates

No new node is created. The proof cites the existing abstract residue and finite-potent trace calculus, plus the ordinary trace and differential definitions. In particular it does not duplicate `lem-pc-tate-endomorphism-ideals` or add a general trace theorem already derivable in this instance from the existing characterization.

## Review by Q106

I checked the original statement against Tate, *Residues of differentials on curves* (1968), §2 R5 and its proof, printed p.153, and read §1 T1–T5 on pp.149–150 and the finite commutator formula (*) on p.152. I also read the chapter, the unit, its main-20261015 statement, the full statements of all four cited DAG nodes, and the relevant project Lean definitions and theorems. There are no new-node sources to certify.

Step 1 uses only the admissibility definition from `lem-pc-tate-abstract-residue-calculus`. The two finite defects of A and B are hypotheses, not conclusions borrowed from another node. The injection into the direct sum of the two quotients proves the intersection case; the sum case has the displayed finite error space. These calculations work for infinite-dimensional V and do not assume f is invertible.

Step 2 is the explicit elementary complement construction from Tate's choice of four compatible projections. The chosen decomposition is valid because the bases added to a basis of I in A and B remain independent modulo I. Checking the four summands verifies the projection identity, so this step does not hide an existence claim about incompatible projections.

Step 3 cites precisely the commutator formula stated by `lem-pc-tate-abstract-residue-calculus`, which uses `[pi m_f,m_g]` (not a different pair of lifts). Its finite-potence and residue formula apply because all four subspaces are admissible by Step 1 and the original hypotheses. For the extra image bounds I wrote the calculation: `(pi_L-1)` kills L, and the f and fg defects are finite-dimensional. The identity uses only commutativity of C and multiplication on its module. No assumption that a projection is C-linear occurs.

Step 4 contains three elementary finite-error inclusions and the explicit eight-image construction. In multiplying the errors, the operators need not preserve any finite error space: images of finite-dimensional spaces under arbitrary k-linear maps are still finite-dimensional. Invariance of W follows instead from writing the fourth-order word as its length-three prefix applied to the final vector. No commutativity of the Z operators is asserted; expansion of their cube includes all eight words. The construction is exactly the finite-dimensional F^n V argument in Tate's proof of T4, specialized and written out, rather than an uncited general theorem.

Step 5 uses the sentence of `lem-pc-finite-potent-trace-calculus` saying that a finite-potent trace equals the ordinary trace on ANY finite-dimensional invariant U containing a power image. W is finite, invariant, and contains each third power, including the cube of the difference; hence every hypothesis is checked separately. `def-weil-endomorphism-trace` states the diagonal-entry formula, from which subtraction is entrywise. This is a computation on W, not the unsupported claim that finite-potent trace is globally additive.

Step 6 checks the second filtration explicitly, V to B to I to zero modulo finite errors. In particular the finite restriction of Z_B to B also has finite image on I. It repeats the same eight-image construction for this particular pair and uses the same restriction-characterization sentence and the ordinary trace definition. It does not assume the first common subspace works for the second pair.

Step 7 uses the exact projection identity, so the two differences are the very same endomorphism of V. They have the same canonical trace even though their two finite invariant spaces may differ; the independence of the subspace is part of the cited trace-calculus statement. The formula from the abstract residue node is exactly the one substituted. Step 8 cites the explicit quotient-of-the-free-module construction in `def-weil-pbc-kahler-differentials`; it implies generation by the fdg symbols. Together with the explicitly stated k-linearity of the residues, it extends the equality to every differential. I do not use a C-linear universal property to compare the k-linear residue maps.

I checked small cases A=B, A=0, B=V, A contained in B, V=0, finite-dimensional V, and characteristic two. In A=B or a containment case one of the difference operators can be zero and the finite-space proof still applies. For zero or full subspaces the admissibility calculation has zero defect. Empty word-image sums can be zero and still are finite-dimensional invariant subspaces. No step divides by 2 or introduces a sign that fails in characteristic two. Arbitrary non-domain C and nonfaithful C-actions are allowed throughout; only commutativity and k-linearity are used.

Against delivery-errors B–E: the unchanged statement introduces its objects and cites its residue construction; there is no statement-only child containing a disguised proof, no elementary child, no relabelled clause, and no route change. Every non-elementary use is one of the cited nodes' actual statement sentences, copied verbatim into `citations.json`. Every proof dependency is the union of the step uses. All step texts are below 2000 characters. No SGA source, finite-dimensionality hypothesis on V, separability hypothesis, field hypothesis on C, or unmentioned invertibility hypothesis is used. The only off-unit nodes are the ordinary trace and differential definitions, both Mathlib leaves; the substantive residue and trace statements are in the same unit.
