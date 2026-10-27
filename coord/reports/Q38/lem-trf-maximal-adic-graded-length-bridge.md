# Q38: lem-trf-maximal-adic-graded-length-bridge

## Files written

- dag/nodes/sec-trace-formula/lem-trf-maximal-adic-graded-length-bridge.json: item, statement, split into five explicit steps; no complete Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-rational-power-sum-formula.json: new statement, Mathlib leaf, exact sum_range_pow, Mathlib/NumberTheory/Bernoulli.lean:295–298.
- citations.json: verbatim statements for all six node citations in the five steps.

## Attachments

None. The project-source searches for the blueprint id, associated graded, and Hilbert–Samuel found no declaration proving this entire item. Ideal.associatedGraded_finiteType in WeilConjectures/RingTheory/AssociatedGradedFiniteType.lean proves only finite type, not the degree-one, length and eventual-polynomial clauses; it is not an attachment for this item.

## WANTED

None. All literature used is present. The explicit monomial-summation leaf is stated verbatim by the installed Mathlib source. Its source locates the Stacks discrete-summation task and gives the precise declaration/file/lines for the explicit implementation.

## Corrections and scope

The item was statement-only, not already split or reviewed, and no earlier sandbox split/report/searches existed. Its statement is correct, including P=0, and is unchanged. The imported source index uses n+1 in chi, while the item uses n; the proof explicitly sums i<n. The proof origin is agent because the concrete rational power-sum implementation and the leading-coefficient estimate expand the Stacks proof rather than reproduce its binomial-basis language literally. No chapter/unit files were changed. No compiler, Lake, or repository git commands were run.

The existing finite-type associated-graded node is not used for degree-one generation: its statement promises only finite type. The existing graded-injective-multiplication-polynomial-lift node concerns dimensions of a graded module with a chosen injective degree-one element. It cannot be applied directly to an arbitrary maximal-adic graded ring, which may have zero divisors. The explicit Faulhaber leaf avoids that hypothesis altogether.

## Unfinished work

None for this one-level split. The one new node is already an exact Mathlib leaf.

## Not duplicates

lem-trf-rational-power-sum-formula vs lem-trf-graded-injective-multiplication-polynomial-lift: the shared Stacks Tag 00JZ describes finite-difference integration in the latter; the new statement is solely the explicit rational sum-of-powers formula, with no graded modules, injective multiplication, quotient grading, or eventual dimension assertion. It is a Mathlib leaf used to write the summation argument, not a replacement for that existing lemma.

lem-trf-rational-power-sum-formula vs lem-trf-maximal-adic-graded-length-bridge: the shared Tag 00JZ is the discrete-summation source. The new leaf has no ring, maximal ideal, associated graded ring, module length, or eventual Hilbert function. It is the exact finite identity for sums of powers; the item must still form the cumulative polynomial and prove its positivity.

The whole DAG and blueprint searches for Faulhaber, Bernoulli, sum_range_pow and sums of powers found no pre-existing formula node. Blueprint searches for numerical polynomial, associated graded and length were read; none states this leaf. The new node follows the recorded blueprint ancestor/via chain and specifies the discrete-summation place served.

## Review by Q38

I read algebra.tex at proposition-hilbert-function-polynomial (00K8), its preceding power-filtration identity, lemma-numerical-polynomial (00JZ), lemma-dimension-is-length (00IY), lemma-length-independent (00IX), lemma-length-additive (00IV), and the polynomial-cover paragraph in lemma-completion-Noetherian (05GH). For the only new node I read Mathlib/NumberTheory/Bernoulli.lean:291–298 and BernoulliPolynomials.lean:159–174 after the searches identified them. Loogle and both semantic services returned the exact power-sum formula. The grep with a directory root gives the full Mathlib file and line. All new-node search records are queries actually present in searches.jsonl.

Step 1 cites the Noetherian definition, which says every ideal is finitely generated; the associated-graded ring-structure statement, whose clauses (1)–(3) give the multiplication and quotient scalar laws; and the standard-graded definition, whose exact degree-zero and finite degree-one generation conditions are verified. The finite monomial generating argument is written out by induction, not taken from the proof of the weaker finite-type node. The maximal ideal annihilates each graded piece by the power identity. The degree-zero case includes the empty monomial and does not assume t>0. The structure theorem is a generic algebraic tool from another unit, declared in split_report.tool_uses; it replaces no step of the trace-formula unit's route.

Step 2 cites only the module-length definition and writes the argument of 00IY explicitly: a submodule is a subspace because every residue scalar lifts, and a basis flag both realizes the dimension and bounds every strict chain. This is a short elementary use of finite-dimensional linear algebra, not an unsupported citation to a definition for a theorem. The item assumes a nonzero local ring, so its residue field is nonzero and d_0=1.

Step 3 uses exactly the additivity promised by lem-weil-pbc-length-additive-short-exact, including its assertion that finite length is closed under extensions. I checked the inclusion/reduction maps and their kernel explicitly before applying it. The base is R/m^0=0; the result is H_R(n)=sum_{i<n}d_i, not the off-by-one Stacks convention. All subquotients have finite length by step 2, so no subtraction involving infinite lengths occurs.

Step 4 uses only the explicit sum of powers in the new leaf. The proof defines each polynomial F_p and their coefficient-weighted sum, subtracts the finite initial segment at a, and sets Q=A+H_R(a)-A(a). Its value identity follows by interchanging finite sums. It does not assume that P has positive degree or is nonzero. The new node does not restate any clause of the item, and all its objects, including the sign convention b_1=-1/2, are introduced in its statement. The recurrence agrees with the rational Bernoulli convention in the source.

Step 5 uses the already proved bound H_R(n)>=1. It is an explicit elementary coefficient estimate: for n>=1 each lower power is bounded by n^(d-1), so a negative leading coefficient forces a negative value for large n. Constants are treated separately. No unrecorded polynomial-asymptotics theorem is needed.

I tested the field case m=0 (empty generating list, S_0=k, all other pieces zero, P=0, Q=1), k[epsilon]/(epsilon^2) (dimensions 1,1,0,..., eventual Q=2), and a DVR (dimensions all one, H(n)=n). For the Faulhaber leaf I checked n=0 (empty sum, every displayed power of n has positive exponent), p=0 (sum=n) and p=1 (n(n-1)/2). These catch the Bernoulli sign convention and both indexing boundaries. I also checked redundant and zero generators: they change neither the ideal-power spanning argument nor any dimension assertion. All steps are shorter than 2000 characters, new statements have no proof sketches or proof dependencies, citation quotes are copied verbatim, and no dependency is a downstream citer of this item.

The first completed dry run requested an explicit notion citation and a numeric Mathlib line field on the leaf. I added def-weil-polynomial-ring to introduce F_p as a rational polynomial, and mathlib_match.line=295, verified against the displayed source. Its statement remains a one-line specialization of sum_range_pow by expanding F_p and evaluation.
