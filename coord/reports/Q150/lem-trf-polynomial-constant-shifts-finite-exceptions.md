# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-polynomial-constant-shifts-finite-exceptions.json`: statement item, split, no direct Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-monic-polynomial-divisors.json`: statement, Mathlib leaf `Polynomial.fintypeSubtypeMonicDvd`, `Mathlib/RingTheory/Polynomial/UniqueFactorization.lean:101–113`.
- `citations.json`: verbatim statements for each node cited in each proof step.

## Attachments

None. Searched the exact blueprint tag and the notions constant shifts, separability, derivative and finite monic divisors in the read-only `WeilConjectures/` source. There is no project declaration giving this item or the new leaf. Master was checked only as reference, never as evidence of a finished proof.

## WANTED

None for this split. The algebraic proof is agent-written from the explicitly recorded convention, existing polynomial PID node, and verified Mathlib leaf. It does not need the contextual Temkin PDF wanted by the parent delivery.

## Findings and changes

The statement is correct as imported and was preserved byte for byte. The original source description does not claim that Stacks 09H0 or 09H1 directly states the finite-exception theorem; I retain that distinction. Those tags supply the ideal/derivative background. The proof strengthens the parent's suggested irreducible-factor argument to indexing by all nonunit monic divisors, avoiding any new irreducible-factor or algebraic-closure lemma. This changes no unit route: the current `main-20261015` local-term node and unit use contracting correspondences, and this already queued algebraic auxiliary belongs to the explicitly historical normalization chain.

For the item I read the inherited searches and their actual recorded hits: neither `separable_iff_derivative_ne_zero` (which requires irreducibility) nor `separable_X_add_C` (only linear polynomials) states the item. They remain in the item's record; there was no reason to repeat those same questions. New-node searches are recorded as run in `searches.jsonl`, including a second semantic phrasing, Loogle's Fintype query, and source grep. Read the matching declaration, its general UFD coefficient hypotheses and the field-instance chain; no nontrivial Mathlib specialization is hidden.

## Not duplicates

lem-trf-finite-monic-polynomial-divisors vs lem-weil-pbc-polynomial-ring-normal-domain: the existing node states that a polynomial ring over a normal domain is a normal domain; it says nothing about finiteness of the monic divisors of a fixed nonzero polynomial.

lem-trf-finite-monic-polynomial-divisors vs lem-trf-normal-polynomial-surjection: the existing node presents every commutative ring as a quotient of a normal integral polynomial ring over the integers in possibly infinitely many variables; it gives no finite divisor set.

lem-trf-finite-monic-polynomial-divisors vs lem-pur-polynomial-field-pid: the former states finiteness of monic divisors of a fixed nonzero polynomial; the latter states principality of ideals. Both cite the field-polynomial background in Stacks 030A; neither statement implies the other in one line from the literal recorded conclusion.

Whole-DAG statement scans for finite factors/divisors, monic divisors, the exact declaration, coprimality and polynomial PIDs found no duplicate of the new statement. Whole-blueprint searches for coprime, factorization, monic, divisor and finite monic found none. The existing PID node is cited instead of duplicated; the new leaf does not restate a clause of the item, as it has an arbitrary polynomial, no derivative or shifts, and supplies only the finite index set used in the proof.

## Review by Q150

I read Stacks `fields.tex`, labels `lemma-irreducible-polynomials` (09H0) and `definition-separable` (09H1), and `algebra.tex`, label `lemma-polynomial-domain-normal` (030A), first sentence of the proof. The source's 09H1 convention is stated there for irreducible polynomials; the cited `def-pc-separable-polynomial` explicitly supplies the general coprime-to-derivative definition used by this item. The new leaf was checked against Mathlib `Polynomial.fintypeSubtypeMonicDvd`, lines 101–113 of `RingTheory/Polynomial/UniqueFactorization.lean`, including its coefficient hypotheses at line 85. Its statement says exactly finite monic divisors; it is not a new unsplit proof obligation. For the inferred field UFD instance I read `DivisionSemiring.isPrincipalIdealRing` at `PrincipalIdealDomain.lean:72–74` and `PrincipalIdealRing.to_uniqueFactorizationMonoid` at lines 371–373.

Step 1 cites the new leaf's actual statement and applies it to p = h prime, nonzero by the item's only extra hypothesis; passage to the nonunit subset is elementary finite-set reasoning. Step 2 cites the entire derivative/separability definition: the constant contributes zero to the coefficient formula for the derivative, and nonseparability is exactly failure of a Bezout identity. Step 3 cites the literal statement of the existing polynomial PID node: it allows the ideal (h+b,p), with no irreducibility hypothesis. I wrote out why its generator divides both entries, why it is nonzero, and why a unit generator would contradict step 2. Thus the definition node is not being used as the source for the principality theorem. The description of the two-generated ideal is elementary: the sums U(h+b)+Vp form an ideal and contain the generators.

Step 4 cites the actual polynomial coefficient and field definitions, whose statements were opened: nonzero leading coefficient is invertible; coefficientwise scalar multiplication makes the divisor monic, and multiplication by that scalar is reversible. Divisibility and nonunit status survive without invoking a factorization theorem. Step 5 uses just field inversion: subtracting the two multiples gives a multiple equal to b-c, and a nonzero b-c would exhibit an explicit inverse for d. This proves the at-most-one assertion within the proof instead of creating a spurious lemma node. The final finite union covers every exceptional b by step 4. All steps are under 2000 characters.

Checked edge cases: if h prime is a nonzero constant (e.g. a linear h or T^p+aT with a nonzero in characteristic p), its monic divisor set is {1} and D0 is empty, so no exception is forced. For h=T^2 in characteristic different from 2, only b=0 can be exceptional. For h=T^3 in characteristic 2, h prime=T^2 and again b=0 is the sole exception. Finite fields cause no issue and no infinitude was used. The new leaf includes nonzero constant p and arbitrary nonmonic p; its assumption p nonzero is essential (over an infinite field zero has infinitely many monic linear divisors). The item's derivative hypothesis is likewise essential: over an algebraically closed field of characteristic p, T^p+b is inseparable for all b. No perfectness, monicity, valuation or characteristic condition entered the proof.

I corrected an initially drafted field-instance annotation to the actual PID-to-UFD instance chain after opening its source. Citations now quote the full verbatim statement of each cited node, including the derivative formula; there are no quotes from another node's proof. The B–E audit found no additional statement change, cycle, hidden lemma, missing source, duplicate, hollow definition or SGA citation. Only the sandbox was written; no Lean or compiler was used.

The first dry run requested two additional tag-030A duplicate comparisons. I opened both existing nodes and recorded the precise differences above; neither states the finite monic-divisor result.

## Unfinished

None. Required server dry run and delivery follow this report.
