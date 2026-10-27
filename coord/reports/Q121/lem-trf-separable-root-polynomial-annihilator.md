# Stage-1 report: lem-trf-separable-root-polynomial-annihilator

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-root-polynomial-annihilator.json`: statement, split into four elementary coefficient calculations; no complete Mathlib match.
- `citations.json`: six verbatim citation records covering every node used by every step.
- `report.md`: this report. The search command maintains `searches.jsonl`.

There are zero new nodes and zero new Mathlib leaves. The item statement, its statement dependencies, source and inherited blueprint ancestry are retained.

## Attachments

None. The project-source searches for the exact blueprint tag, divided differences, polynomial annihilation and derivative nonvanishing found no declaration stating all clauses with a finished proof. Project uses of `Polynomial.Separable.aeval_derivative_ne_zero` prove only an ingredient and are not attachments.

## WANTED

None: the relevant Stacks source is available locally.

## Findings and changes

The initial node had an explicit and correct statement but no proof. Stacks Algebra Tag 0C2X (`lemma-separable-algebraic-diagonal`, algebra.tex:10221-10262) factors the minimal polynomial and asserts that its complementary factor is nonzero at the chosen root; it calls the ensuing localization calculation clear. I expanded the finite coefficient calculation required by this item's more general statement. The proof is marked agent-written because these explicit divided differences and the unrestricted evaluation identity are elaborations of that paragraph, rather than a verbatim proof in Stacks. No statement dispute or source error was found. The field and polynomial-ring definition statements were read, as was `def-pc-separable-polynomial`; the latter already gives the formal derivative formula and the Bezout identity, so derivative nonvanishing does not require a new lemma node.

I read the chapter and unit records and followed the existing ancestry through separable-algebraic diagonal localization. This item is a subsidiary algebra calculation, not the statement of the unit; no unit or chapter record is changed. I read the parent localization node: its step 3 needs exactly the nonzero value and annihilation supplied here. Nothing from that parent's proof is used to prove this item.

The item's imported searches are preserved. I also ran and read the required leanfinder, loogle, grep and leansearch queries with the authorized msearch command; the six new records correspond exactly to this sandbox's log, including a second natural-language phrasing and a focused polynomial grep. All four services returned successfully. I inspected Mathlib FieldTheory/Separable.lean:44-53,136-147; Algebra/Polynomial/FieldDivision.lean:630-641; Algebra/Ring/GeomSum.lean:181-197; FieldTheory/Minpoly/MinpolyDiv.lean:35-80; and Algebra/Polynomial/SumIteratedDerivative.lean:168-202. These give derivative nonvanishing, monic division or geometric sums, or a different iterated-derivative sum. None states the whole explicit D formula, diagonal value and annihilator identity by one-line specialization. The item therefore stays a split statement, not a Mathlib leaf.

## Not duplicates

No new node was created. Blueprint searches for `divided difference`, `polynomial annihilator`, `separable root` and `divided` found no blueprint match. I searched the whole DAG for divided differences, complementary factors, polynomial annihilators, separability/derivative statements and Tag 0C2X. Existing uses of 0C2X concern tensor-localization, scalar restriction, or related derived tensor consequences; none needs a duplicate because the elementary argument can be written directly in this item. The statement of the separability definition supplies all its needed content explicitly.

## Review by Q121

I checked delivery-errors B through E against the actual node, source and cited statements. For the item I read Stacks algebra.tex Tag 0C2X, including the finite primitive-element argument and general-union paragraph, and fields.tex Tag 09H1 (`definition-separable`) with its preceding derivative calculation. There are no new nodes whose source or hypotheses could be unreviewed.

Step 1 cites `def-weil-polynomial-ring`, whose statement defines finitely supported coefficient sequences and convolution multiplication. Expanding `(T-alpha)` times the finite inner sum cancels every interior monomial; summing with the coefficients gives the desired identity as a polynomial identity, even over finite fields. No appeal to equality of polynomial functions is made.

Step 2 cites `def-pc-separable-polynomial`, whose statement explicitly gives the formal derivative `sum n c_n T^(n-1)`. Evaluating each of the j summands gives the same power alpha^(j-1), and repeated addition gives exactly that derivative. This step needs no separability theorem and introduces no division by j.

Step 3 cites `def-pc-separable-polynomial` for the exact Bezout equality `UP+VP'=1`, `def-weil-polynomial-ring` for convolution, and `def-weil-field` for `0 != 1`. I wrote the finite double-sum argument proving that evaluation preserves products. With the given root hypothesis, evaluation of Bezout gives `V(alpha)P'(alpha)=1`, which forbids `P'(alpha)=0` in L. Crucially, nontriviality is used only in L; no such hypothesis is introduced on R. The factorization and equality Q(alpha)=P'(alpha) follow from the preceding steps with G=P.

Step 4 cites `def-weil-polynomial-ring` and explicitly computes product evaluation through the specified unital coefficient map iota. The commutativity hypothesis on R permits the reordering from Q(t)(t-iota(alpha))H(t) to P(t)H(t). The latter is zero by the item's hypothesis P(t)=0. This uses no field embedding into R, no injectivity of iota, and no cancellation in R. All citations were checked against the statements, not the proofs, of those nodes; citations.json copies the relevant complete definition statements verbatim.

I tested the small cases in the formulas: G constant gives D=0 and zero derivative; G=0 and F=0 have empty coefficient support and H=0; P=T-alpha gives Q=1 and forces t=iota(alpha); alpha=0 still has powers with exponent zero equal to one. In characteristic p the j-fold sum can vanish when p divides j, exactly as in the derivative; the Bezout/root hypotheses still force the particular derivative P'(alpha) to be nonzero. P=0 is excluded by separability, and a nonzero constant P cannot have a root in the field. For the zero ring R all evaluations and all products are zero, so the final calculation still holds. I also checked that the proof never assumes monicity, irreducibility, characteristic zero, or nonzero F.

Each step is a short expansion from definitions or substitution into earlier steps. No hidden non-elementary result is invoked, so creating a separate node for any of these arguments would violate the rule against elementary new nodes. Each proof step is below 2000 characters. The proof-dependency list is exactly the union of the uses lists; the dependency definitions have no path requiring this item. The blueprint field and statement dependencies remain faithful to the existing item. No protected repository, launcher, Lean, unit or chapter file was written, and no compiler or Lake command was run.

## Unfinished work

None in the mathematical split. The required server dry run and direct delivery follow this self-review; the maintainer supplies the independent review.
