# Q114 — lem-trf-power-series-adic-gradient-control

## Files written

- dag/nodes/sec-trace-formula/lem-trf-power-series-adic-gradient-control.json: statement, split into four steps; unchanged statement and statement dependencies; no full Mathlib match.
- citations.json: nine entries, one for every step/node citation, each quoting the cited statement verbatim.
- report.md: this report. searches.jsonl is the search command's actual log.

New nodes: 0. New Mathlib leaves: 0. Existing nodes supply all non-elementary input.

## Attachments

None. Searched lean/WeilConjectures for the item id, adic-gradient terminology, formal power series/differentials and pderiv. No declaration states every clause. Read the coefficient criterion's project declaration power_series_mem_combined_ideal_pow_iff in WeilConjectures/RingTheory/PowerSeriesCombinedIdealCoefficients.lean: this is an input, not an attachment for the full item. Also inspected Derivation/PowerSeriesPolynomialDifferential.lean; its theorem concerns finite coefficient subrings, not this item.

## Wanted

None.

## Findings and corrections

The imported item had no proof. Its statement is correct and was retained exactly. In particular the finite-level formula does not require partial differentiation to descend to an endomorphism of D/n^r: that would generally be false (the derivative of t^r need not vanish modulo t^r). The proof instead chooses a polynomial representative at precision r+1, compares its partial derivatives modulo n^r, and differentiates its equal class in Q_r.

Read Stacks algebra.tex Tag 02HQ, lemma-differential-mod-power-ideal (34194–34209), and Tag 00RX, lemma-differentials-polynomial-ring (34310–34340). The former only supplies context for the one-power loss, not the entire formal-series assertion; the latter supplies the polynomial differential calculation. The coefficient/truncation assembly is explicitly marked agent-written. No claim that these tags state the whole result is made.

Read the chapter and unit records, and current literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md and lem-trf-local-term-locality.proof.md. The current ancestor concerns contracting correspondences; the item's inherited provenance describes an auxiliary nodal/Jacobian branch beneath it. This delivery preserves that existing auxiliary route and does not alter the chapter or unit. Ran blueprint_refs.py ancestor and whole-blueprint searches for power series and differential, and searched the whole DAG for total-degree, derivative/ideal-power terminology and tags 02HQ and 00RX. Reused the existing combined-ideal coefficient criterion and polynomial differential formula instead of creating duplicates or nodes restating the item's clauses.

Read all six current search results (two LeanFinder phrasings, Loogle, LeanSearch, two grep patterns) as logged. The meaningful hits are MvPowerSeries.coeff_pderiv and pderiv_coe, and KaehlerDifferential.mvPolynomialBasis_repr_apply. Read Derivative.lean 110–150 and the existing polynomial-basis node, which records the exact polynomial formula and Mathlib match. No hit is the combined statement; no additional leaf is needed for a coefficient formula already present in the formal-derivative definition's statement. All previous search records remain intact.

## Unfinished

Nothing in the one-level split. Server dry-run and delivery results will be appended after validation.

## Not duplicates

No new nodes. The general combined-ideal coefficient node is reused with coefficient ideal zero; the polynomial-basis node is reused for its explicit formula. The broader formal-relative-derivation-expansion node and the sibling truncated-differential-presentation node are not used to replace the argument or create circular dependencies.

## Review by Q114

I read delivery-errors B through E in full and checked this split against the actual statements and sources. There are no new statements to introduce unbound objects, incomplete hypotheses or unsourced notions. The item's five definition dependencies already introduce the rings, derivatives and universal differentials it uses. No imported fields were removed, and no target or definition was changed.

For step 1 I opened lem-weil-pbc-power-series-combined-ideal-coefficients and checked its precise generality: it allows any commutative coefficient ring, zero base ideal, and all nonnegative numbers of variables. With positive exponent k and |E|<k the exponent k-|E| is positive, so the required ideal coefficient is exactly zero. I then used the coefficient formula actually written in def-trf-formal-power-series-partial-derivative, with |E+e_i|=|E|+1. The exceptional s=1 case is handled separately and does not invoke a negative-degree condition. This step is marked non-elementary because it invokes the substantive existing coefficient criterion; its application is recorded as a generic off-unit tool use.

For step 2 I compared the explicit monomial formula in def-weil-pbc-polynomial-partial-derivative with the coefficient formula of the formal derivative node. They give the same coefficients on a polynomial, without an assumption about arbitrary derivations on series being determined by coordinate values. The map of ideal powers is written as finite sums of products of their generators, which checks the precise hypothesis needed to apply step 1. This is an elementary calculation from those definitions, not a hidden comparison theorem.

For step 3 I checked def-weil-pbc-mv-polynomial-ring really defines finite sums and that finitely many variables make the truncation finite (all coordinates are bounded by r). The same combined-ideal criterion gives the tail membership directly. Additivity is part of the stated formal-derivative definition, and step 1 with s=r+1 gives the desired r-bound. No completeness, characteristic zero, Noetherian assumption or division is used.

For step 4 I opened lem-weil-pbc-polynomial-ring-kahler-basis-any-variables and verified its statement explicitly gives dg as the sum of the partial derivatives times coordinate differentials; it is not merely a freeness claim. I opened def-weil-pbc-kahler-differentials and checked its universal property gives exactly the P-linear map induced by the derivation p -> d(q(p)). This transports that polynomial equality, and step 3 supplies both equalities of quotient classes. The proof does not assert the incorrect descent of partial differentiation to Q_r or use an infinite sum in algebraic differentials.

Small cases: n=0 has D=P=F, zero variable ideals, constant truncation and zero relative differentials. For s=1 the gradient bound is membership in D. For r=1, Q_1=F, so the universal differential formula vanishes; the degree-1 part in p_2 is harmless since every d(q(t_i)) is zero. In characteristic p, t_i^p has zero partial derivative and no implication is reversed, so the argument still holds. The formulas multiply by integer classes and never divide by them. Each step is under 800 characters, so no long step conceals a separate non-elementary lemma. All nine uses have literal statement quotes in citations.json. No new node simply repeats a clause; all elementary arguments remain steps.

## Validation

The required server dry run exited 0 and printed OK (not pushed), commit 2a20aa25e80, with maintainer preflight passed. This validates the one-level split and citation records mechanically; the maintainer's independent mathematical review follows delivery.
