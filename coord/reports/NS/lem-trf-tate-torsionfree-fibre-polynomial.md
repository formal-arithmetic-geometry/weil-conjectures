## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tate-torsionfree-fibre-polynomial.json`: item split into seven proof steps, statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-tate-factorial-normal.json`: statement-only analytic input, not in Mathlib.
- `dag/nodes/sec-trace-formula/lem-trf-tate-root-spectral-formula.json`: Mathlib leaf, `max_norm_root_eq_spectralValue`, `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:294`.
- `citations.json`: one verbatim statement quotation for each citation in each proof step.

## Attachments

None. Searched the project source under `lean/WeilConjectures` for the blueprint tag, TateAlgebra, affinoid, torsion-free fibres and the polynomial formula. No complete declaration states this item. `minpoly.ker_eval` in Mathlib requires the target algebra to be a domain, so it cannot discharge the nonreduced and product-algebra cases in this item.

## WANTED

WANTED: archival Bosch, *Lectures on Formal and Rigid Geometry* (April 2008), Section 1.2 Proposition 14 and Section 1.4 Lemmata 10 and 12, for the item and `lem-trf-tate-factorial-normal`. The source is absent from the local literature; I read the primary PDF online at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf. Accordingly `proof_origin.by` is `agent`, with that reading as guidance, rather than claiming an archived document proof.

## What was wrong or changed

The item was unsplit and had no proof in the sandbox. Its statement agrees with Bosch Lemma 12(i)-(ii); no statement dispute or alteration is necessary. The parent spectral-equation node cites this item, so it cannot be used to prove it. The proof instead constructs the generic minimal polynomial and descends it using the existing normal-monic-divisor node. I corrected an initial draft that would have reduced an inclusion modulo a maximal ideal: such reduction need not be injective. The final argument applies lying-over to the actual inclusion T[c]⊂C, before reduction. It compares sets of absolute values, and never claims that roots with multiplicities biject with maximal ideals.

Mathlib searches are recorded from actual msearch.py results in this item's `searches.jsonl`. Semantic searches with two phrasings distinguish formal PowerSeries factoriality from restricted-series factoriality, and distinguish field minimal-polynomial statements from a torsion-free algebra that may have zero divisors. I read the hits in `PowerSeries/Inverse.lean:270-289`, `PowerSeries/Ideal.lean:32-45`, `Polynomial/GaussLemma.lean:75-90`, `Minpoly/IsIntegrallyClosed.lean:35-105`, and `SpectralNorm.lean:95-119,230-335,770-795`. The split-root numerical theorem is an exact Mathlib specialization and is therefore delivered as a leaf. No Lean was written or compiled.

## Not duplicates

lem-trf-tate-factorial-normal vs lem-trf-tate-weierstrass-norm-division: the existing node gives division/preparation for a distinguished series, not unique factorization or integral closure of the entire Tate ring.

lem-trf-tate-factorial-normal vs lem-trf-tate-normalization-lift: the existing node gives a finite injective normalization presentation of a quotient, not factoriality or normality of the source ring.

lem-trf-tate-factorial-normal vs lem-trf-affinoid-polynomial-closed-point-comparison: the existing statement gives Noetherianity, complete normed quotients and completed-local-ring comparisons, not factoriality/normality.

lem-trf-tate-root-spectral-formula vs lem-trf-spectral-norm-algebraic-extension: the existing node constructs a norm from each element's minimal polynomial; the new Mathlib leaf gives the maximum root norm for any specified split monic polynomial, including repeated roots.

lem-trf-tate-root-spectral-formula vs lem-sfb-monic-spectral-value-coefficients: the existing node characterizes spectralValue≤1 by coefficient inequalities; it does not compare spectralValue to root norms.

lem-trf-tate-root-spectral-formula vs lem-trf-tate-torsionfree-fibre-polynomial: the new leaf is a numerical polynomial theorem over normed fields, with a supplied factorization and algebra norm. It does not construct an evaluation kernel, descend coefficients, or identify any maximal-ideal fibre; those arguments are in the item.

The DAG/blueprint searches for Tate algebra, spectral value, root norm, restricted series, factorial, minimal polynomial and monic factor found no blueprint node stating either new fact. Searches by the precise Mathlib declaration found no existing root-spectral node. The current `latest` blueprint ancestor is the contracting-correspondence local-term node; the analytic chain here is inherited historical supporting material below that node, not a replacement of its current unit argument.

## Review by NS

I read Bosch Section 1.2 Proposition 14 (factoriality and normality, printed pp.15-16) and Section 1.4 Lemma 12(i)-(ii) (printed pp.26-27), including its reduction to the monogenic subalgebra and its root calculation. For the new root leaf I read the exact Mathlib theorem and its hypotheses at lines 294-298 and the spectralValue definitions at 101-115. The item keeps all its original hypotheses and conclusions, including torsion-freeness, nonzero C, arbitrary d≥0, and no reducedness or separability assumption. I read every dependency statement rather than relying on titles, and copied them into citations.json.

Step 1 uses the normal-domain clause of the new Tate factoriality node, finite-module integrality from the existing 00GK node, and precisely the coefficient-descent conclusion of the normal-monic-divisor node (00H6). T is a domain and integrally closed, so the latter applies to its fraction field. Torsion-freeness gives the localization injection directly by the fraction relation. Least-degree monic annihilators and long division work in a finite algebra with zero divisors as well as a field extension; no irreducibility of the minimal polynomial is asserted. Step 2 spells out monic division and coefficient injectivity to prove the evaluation kernel, uniqueness and the explicit quotient isomorphism; it is elementary and creates no extra clause node.

Step 3 uses the injective integral map T⊂C for `pqf-lem-lying-over` (00GU), then exactly the prime-over-maximal conclusion of the 00GS node. The finite spanning set survives reduction, so the existing finite-dimensional-Artinian node (00J6) and Artinian-spectrum-finite node apply to C/mC. Their statements include nonreduced algebras. Quotient ideal correspondence is written out. The supremum-calculus statement supplies the finite residue extensions and unique norms for T and C, both nonzero affinoids.

Step 4 uses algebraic-closure existence (09GT), algebraic embeddings (09GU), the existing spectral norm on an algebraic extension of the complete nontrivially valued base K, and uniqueness of extending absolute values. Its finite residue field k embeds into the chosen closure of K, and its residue norm equals the restricted norm by that uniqueness statement. Root existence and repeated linear division give the factorization explicitly. Step 5 applies finite-module integrality to A=T[c]⊂C, where the original T-generators still generate over A. The root map A→Ω has image the finite domain k[α], and the multiplication argument proves it is a field. Lying-over applies to the original injection A⊂C and the prime-over-maximal lemma makes the lift maximal. Uniqueness of absolute values applies to A/q over K, a finite field extension. It proves equality of the root norm and the lifted residue norm, without claiming injectivity after reduction.

Step 6 applies the 09GU embedding theorem to C/n over k with the same chosen embedding k→Ω, and applies uniqueness on the finite extension C/n of K. Hence every fibre norm is also a root norm; this proves equality of sets of norms, not of root multiplicities. Step 7 uses precisely the Mathlib leaf's nonarchimedean power-multiplicative norm and the positive-degree factorization from step 4, then reindexes j=r−i. No hidden generic-freeness or separability claim remains.

I checked B–E against the files and sources: the new unsplit node has a statement only and introduces K,d,T; its UFD and normality meanings are explicit. The root leaf excludes the empty maximum by r≥1, and records declaration, file and line. Both have full inherited blueprint ancestry and same_as=[] after whole-blueprint searches. No SGA source is used. All non-elementary facts are cited in the step taking them, and no proof step exceeds 2000 characters. I tested d=0, C=K, c=0 (p=Z), C=K[ε]/(ε²), c=ε (p=Z² with both sides zero), C=K×K and c=(0,1) (p=Z(Z−1), root maximum one), and inseparable repeated-root polynomials. None requires a stronger hypothesis.

## What could not be finished

No mathematical clause remains unaccounted for. Stage 1 only: the new factoriality node is intentionally left statement-only for its later split.
