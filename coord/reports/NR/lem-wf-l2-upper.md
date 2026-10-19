# Stage-1 delivery: lem-wf-l2-upper (NR)

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-wf-l2-upper.json — item, statement, split into seven steps. No Mathlib match for the sheaf theorem.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-rational-stalk-exact.json — statement only, unsplit, exact Frobenius fibres on the rational constructible heart. Mathlib has ordinary site stalk functors and exact-functor interfaces but no one-line match for this rational constructible/Weil assertion.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-trace-power-eigenvalues.json — statement only, unsplit, root cardinality and the trace power-sum formula for an arbitrary endomorphism. Mathlib searches return the n=1 trace formula, eigenvectors of powers and characteristic-p trace identities; the exact all-n formula is in the project extension, with attachment candidates below.
- dag/nodes/sec-deligne-laumon-a1/lem-wf-geometric-decay.json — statement, Mathlib leaf: tendsto_pow_atTop_nhds_zero_of_lt_one, Mathlib/Analysis/SpecificLimits/Basic.lean:188–192, specialized to ℝ.
- citations.json — one entry for each step/cited-node pair, quoting the actual statement verbatim.
- searches.jsonl — the unmodified records produced by msearch.py; all searches used by new nodes were run and their hits read.

## Attachments

LinearMap.card_roots_charpoly, LinearMap.trace_pow_eq_sum_pow_roots_charpoly belong to lem-wf-trace-power-eigenvalues; WeilConjectures/Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean:81 and :99. Both direct proofs are present and have no sorry. The node's lean_candidates records them for the maintainer's transitive-closure check; this delivery does not assert a closed audit state without that check.

No attachment for the item. In WeilConjectures/DeligneLaumon/AffineLine/TraceEnergy.lean:478–502, exists_traceEnergy_le_of_hasWeightsAtMost has sorry, and the following l2Weight_le_of_hasWeightsAtMost calls it. The latter's proof being syntactically sorry-free does not finish the item. Its analytic helper l2Weight_le_of_traceEnergy_le is proved, but does not supply the geometric energy bound.

## WANTED

None. The blueprint, Bhatt–Scholze and Weil II used here are available locally. No document was downloaded, no Lean was written, and no compiler, Lake or build tool was run.

## Corrections and source comparison

The imported statement called X₀ merely “the affine curve”, while def-wf-l2-norm requires a smooth geometrically connected affine curve. The current main-20261015 node and the item's blueprint_update already explicitly supply exactly these hypotheses. The delivered statement follows that authorized update, names the coefficient data and relevant definition nodes, and preserves the inequality and weight hypothesis. This is an update to explicit current-source context, not a disputed new mathematical hypothesis. All blueprint_* metadata and import flags are retained.

The imported proof used mixedness as an eigenvalue bound without explaining the filtration, used local Frobenius powers without a node, and passed to the limsup without displaying the decaying ratio. These passages are now explicit. In particular, def-weil-punctual-weights defines a filtration by pure quotients; it does not itself assert the spectral union or exactness of rational fibres. The split cites the separate statements that supply these.

The Lean helper assumes HasWeightsAtMost, a stalk eigenvalue bound, whereas the natural-language item assumes mixedness via a pure filtration. Step 1 proves the needed implication; the two notions are not silently identified. The helper's quasi-compact smooth-curve generality is broader than the affine geometrically connected item, while the final Lean theorem has the affine/connected hypotheses.

The unit sk-l-dl-a1-energy has a different key statement (weight detection from a positive energy bound for a nonzero pure sheaf). This item is its subsidiary upper bound and cannot fill the unit's realized.statement. The chapter, unit and their realized fields are untouched. The proof keeps the blueprint route: punctual weights, elementary trace estimate, point-count bound, normalized growth supremum.

## Not duplicates

- lem-wf-rational-stalk-exact vs prop-weil-pbc-geometric-stalks-exact: the existing statement is the stalk functor Ab(T_et) → Ab; the new statement concerns the rational constructible heart, its finite-dimensional Q̄ℓ fibres and equivariance for the normalized local Weil operators. Applying the existing discrete-coefficient statement alone would silently change coefficient categories.
- lem-wf-rational-stalk-exact vs cor-galois-lisse-representations: the existing exact equivalence concerns lisse sheaves on a connected scheme. The filtration in def-weil-punctual-weights is explicitly allowed to have constructible subquotients, so the new statement permits those without a lissity hypothesis.
- lem-wf-rational-stalk-exact vs lem-weil-point-fibre-equivalence: that statement concerns complexes already on Spec k and a triangulated equivalence; it does not assert exactness of the closed-point fibre functor on a scheme's constructible heart.
- lem-wf-trace-power-eigenvalues vs lem-a1-spectrum-exact-sequence: the latter is spectral union in a Frobenius-compatible short exact sequence, not a trace-of-powers formula.
- lem-wf-trace-power-eigenvalues vs p-linear-spectra: p-linear-spectra computes tensor, exterior-power and dual spectra, not traces of iterated compositions. In particular tensor powers and operator powers are distinct.
- lem-wf-trace-power-eigenvalues vs lem-zl-log-det-identity: the latter gives the determinant/trace generating-series identity, not the stated root cardinality and all-n power-sum formula.
- lem-wf-geometric-decay vs def-wf-l2-norm: a definition of the positive-limsup supremum does not state convergence of geometric sequences.

Before writing these files I searched the whole DAG for the concepts, likely declarations, trace/root formulas, stalk exactness and geometric limits. blueprint_refs.py searches included “trace eigenvalues”, “trace_eq”, “limsup”, “power sum”, “geometric sequence”, “stalk exact”, “stalks are exact”, “short exact constructible”, “trace power eigenvalues”, “power tends” and “geometric decay”. The only relevant blueprint limit hit was def-wf-l2-norm; none states a new node. No new node carries a Stacks tag shared with another node: their sources are the ℓ-adic literature and the particular Mathlib/project results, not an unrelated Stacks section number.

## Review by NR

I read the original blueprint proof, the current main-20261015 statement and blueprint_update, the chapter and energy unit, the slopmaster2 declarations and docstrings, and every statement cited in the seven proof steps. I also read Bhatt–Scholze §§6.8.4–6.8.15 and Weil II (1.1.1), pp. 146–147, to distinguish rational constructible sheaves from ordinary discrete module sheaves. Bhatt–Scholze 6.8.7 supplies constructible kernel/cokernel closure, 6.8.14 compares the rationalized constructible category with the sheaf model, and 6.8.15 describes closed-immersion pullback; these support the new rational-stalk statement. Frobenius compatibility is naturality of the operator defined by pullback and the Weil isomorphism. The project's StalkFunctor.lean:99–123 proves mono/epi preservation and additivity, and :295–306 proves Frobenius naturality, but I have not claimed that a single project declaration states the new combined exactness assertion. It remains a statement-only node.

For the trace-power node, I read the complete project proofs in WeilConjectures.Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs, including the generalized-eigenspace argument; the formula applies to arbitrary operators, not only diagonalizable ones. I read Mathlib's trace-root result at LinearAlgebra/Eigenspace/Charpoly.lean:54–58 and the returned finite-field power formulas and rejected them as matches for all powers in characteristic zero. The new node states no proof sketch. For the geometric-decay leaf I read the actual Mathlib theorem at Analysis/SpecificLimits/Basic.lean:188–192 and its hypotheses; specializing its ordered Archimedean semifield to ℝ introduces no additional hypothesis.

Step 1 uses the literal pure-quotient filtration from def-weil-punctual-weights, the new exact-Frobenius-fibre statement, and the spectral union stated by lem-a1-spectrum-exact-sequence. Its induction starts with the zero stalk and adds one quotient at a time; it never invokes an unprovided punctual bound as part of a definition. Since q_x=q^e>1, the inequality from w_i≤w remains valid for negative w. No assumption that the constructible filtration subobjects are lisse is made.

Step 2 uses the finite-stage Weil category from def-wf-weil-category and p-real-integral for a geometric lattice on the full curve (U₀=C₀=X₀). Its finite reductions are locally free and hence have finite Tor amplitude. This verifies the integral-representative input of lem-trf-rational-local-frobenius-powers. That node explicitly states conjugacy to F_x^(m/e) and only requires invertibility after rationalization; I do not assume that the Weil map preserves a lattice. The point has e|m by the finite-field degree tower. The conjugacy equality survives scalar extension, and trace conjugacy invariance is written as a matrix double-sum computation. The current blueprint rational-local-powers proof was read at thm-trf-l-function-euler-product.proof.md, Step 1, and not taken from an unrelated finite-coefficient statement. p-real-integral is declared as a generic tool in split_report; it supplies only a lattice for this comparison, not an alternate weight argument.

Step 3 takes exactly the root count and trace power sum stated in lem-wf-trace-power-eigenvalues. Applying ι preserves the finite sum and powers; the triangle inequality then gives the rank bound and its square in a few lines. Step 4 takes the precise uniform point-count conclusion of lem-wf-point-count-linear-growth, whose smooth affine finite-type hypotheses the item satisfies, and the energy definition in def-wf-l2-norm. Both finite summation and the choice C=dr²≥0 are explicit. The point-count node is already Lean-closed, so it is reused without a new geometric lemma.

Step 5 uses the positive-real-power definition and laws in def-weil-real-power; division is legitimate because q>1. Step 6 takes the actual b^m→0 statement of the Mathlib leaf and writes the ε/C estimate, treating C=0 separately. This proves limsup=0 both in ℝ and the extended nonnegative reals used in Lean. Step 7 uses precisely the supremum definition from def-wf-l2-norm; every exponent above w has been excluded, so w is an upper bound, including the empty-set value −∞.

Against delivery-errors B–E: every new non-leaf is statement-only and introduces its data, the necessary definition dependencies are named, TeX has single decoded backslashes, no section number masquerades as a Stacks tag, and every recorded search comes from the search log. The new nodes are generic ingredients rather than a restatement of the L² upper bound. The short arguments (triangle inequality, finite summation, exponent rearrangement, supremum) remain elementary steps rather than nodes. No step borrows an uncited node's proof or strengthens its stated conclusion. No non-elementary step exceeds 2,000 characters (maximum is 1,092); the genuine reusable fibre theorem was separated rather than hidden inline. I checked the zero-rank/empty-filtration case, empty rational-point sets for particular m, negative w, repeated roots and non-semisimple Frobenius, and b=0 for the independent Mathlib leaf (the application itself has b>0). The full item has no nonzero-sheaf requirement, and the proof never adds one.

## Unfinished work

No part of the one-level split is left as a prose gap. The rational-stalk lemma is intentionally unsplit and queued; the trace-power node is intentionally statement-only with exact project attachment candidates, pending the maintainer's transitive verification. The delivery must pass the server dry run before push.

## Dry-run repair

The first captured server preflight required the geometric-decay leaf to name a definition node for its power notation. I added def-weil-real-power for positive bases and explicitly stipulated the zero-base natural powers. This changes no convergence assertion or Mathlib match. Its citation quotation was refreshed from the amended statement.
