# Q96: lem-trf-affinoid-spectral-banach-norm

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affinoid-spectral-banach-norm.json: statement, now split; statement unchanged; no project attachment and no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-affinoid-finite-module-strictness.json: statement-only, unsplit; no Mathlib match. Finite modules over an affinoid, not finite-dimensional vector spaces over a field.
- dag/nodes/sec-trace-formula/lem-trf-affinoid-finite-galois-envelope.json: statement-only, unsplit; no Mathlib match. Algebraic finite normal envelopes after normalization and inseparable base enlargement.
- dag/nodes/sec-trace-formula/lem-trf-tate-galois-trace-supremum-bound.json: statement-only, unsplit; no Mathlib match. An analytic norm bound for field trace, not merely the algebraic trace formula.
- citations.json: one verbatim statement quotation for every node cited by every numbered proof step.
- searches.jsonl: actual msearch records; all searches recorded in nodes were run. Reports of unavailable services are retained as unavailable.

## Attachments

None. I searched WeilConjectures for the blueprint tag and the affinoid/spectral notions. No project declaration proves this statement. The item has lean_audit state none. Mathlib spectralAlgNorm concerns algebraic field extensions; this item includes positive-dimensional reduced rings and rings with zero divisors.

## Literature

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Theorem 6.2.4/1, for lem-trf-affinoid-spectral-banach-norm. The listed archive is absent; I do not claim to have read it.

WANTED: Brian Conrad, Several approaches to non-archimedean geometry, Theorem 1.2.6(1),(5) and subsequent paragraph, pp.6–7, https://math.stanford.edu/~conrad/papers/aws.pdf, for the item. I read this online; no download was made.

WANTED: Kiran Kedlaya, More on affinoid algebras, Theorem 4 and its proof, PDF pp.2–3, https://kskedlaya.org/18.727/spectra2.pdf, for the item, lem-trf-affinoid-finite-galois-envelope and lem-trf-tate-galois-trace-supremum-bound. I read all four pages online.

WANTED: Kiran Kedlaya, A little p-adic functional analysis (part 2 of 2), Lemma 1, p.1, https://kskedlaya.org/18.727/p-adic2.pdf, for lem-trf-affinoid-finite-module-strictness. I read the proof online. Finite generation and the open mapping theorem give automatic continuity and the injective norm estimate from the closed-submodule theorem.

WANTED: Siegfried Bosch, Lectures on Formal and Rigid Geometry (2008), sections 1.2–1.4, in particular 1.4 Proposition 2(i), Proposition 4 and Proposition 19, https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, for the normalization, finite-module and quotient-norm background of the three new nodes. I read the relevant pages online (printed pp.14,21–31).

I also read the local Stacks sources fields.tex around tag 0BIL (trace pairing) and resolve.tex around tag 0AXL (trace-coordinate lattice). Those support the existing lem-per-integral-trace-dual-lattice, which is reused rather than duplicated. No SGA source is used. I have not read Fresnel–van der Put Theorem 3.4.9; attempted online access timed out, and it is not relied on.

## Source correction and blueprint placement

The item statement is correct and unchanged. The original unsplit item supplied no proof. Kedlaya's Lemma 3 and the reduction preceding Theorem 4 assert closedness for an arbitrary affinoid inclusion. This is false: for 0<|pi|<1, the injective map K<T> to K<T>, T maps to pi*T, has dense proper image. Polynomials belong to the image. The restricted series sum(pi^n*T^n) does not: its unique inverse coefficients would all be 1, which do not tend to zero. I therefore use only finite inclusions, with closedness and norm comparison supplied by the finite-module theorem. This is a source-proof correction, not a dispute of the item's conclusion.

In positive characteristic, perfection of K does not make Frac(K<X>) perfect. The envelope statement explicitly allows changing the Tate normalization. For each domain component finite over T0, first pass to a p^m-root-variable Tate algebra T=K<U> with U_j^(p^m)=X_j, for an exponent killing the inseparable part of the finite fraction extension. Since K is perfect, Frac(T)=Frac(T0)^(1/p^m). Take the finite separable normal closure over Frac(T) of the resulting compositum, and its integral closure over T. Finiteness of normalization for Tate algebras makes this an affinoid finite over T and over the component. Minimal primes give finitely many such envelopes; reducedness gives the injection into their product. This is exactly the algebraic preparation deferred to the new envelope node; it does not assume the spectral norm theorem being proved. In characteristic zero the root-variable step is unnecessary. The normal closure construction is not an application of the Mathlib instance assuming a perfect fraction field.

I read the current literature/blueprint/latest ancestor lem-trf-local-term-locality and the chapter and unit sk-i-curve-zero. The ancestor's current contracting-local-term clauses (1)–(3) have no affinoid spectral-norm sentence. This item was introduced down the inherited Temkin analytic-support chain; its blueprint.from.place and each new node's place explicitly record that supporting role and that there is no identical current blueprint node. I keep this local analytic item and do not replace a step of the unit's current route. Whole-blueprint searches for affinoid, Banach, finite Banach, normal closure, Galois trace and trace coordinates found no equivalent statement. I declared the two off-unit generic tools (character contractivity and the nonsingular integral trace matrix) in split_report.tool_uses.

## Not duplicates

lem-trf-affinoid-finite-module-strictness vs lem-trf-affinoid-quotient-norm-topology: the latter proves quotient norms for surjections from Tate algebras, not closed images of maps between finite modules over an affinoid.

lem-trf-affinoid-finite-module-strictness vs lem-trf-banach-surjective-bounded-lifts: the latter starts with a surjective continuous Banach linear map; it does not prove module maps continuous or their images closed.

lem-trf-affinoid-finite-galois-envelope vs lem-trf-tate-normalization-lift: normalization provides a finite Tate subalgebra; the new assertion constructs normal finite overrings with Galois fraction extensions, including the inseparable base adjustment and reduced product embedding.

lem-trf-tate-galois-trace-supremum-bound vs lem-per-integral-trace-dual-lattice: the existing statement supplies a nonsingular integral trace matrix (and a sheaf lattice map), with no analytic supremum or Gauss-norm bound. I reuse its first clause for that algebraic part.

lem-trf-tate-galois-trace-supremum-bound vs lem-trf-finite-affinoid-spectral-equation: a finite affinoid spectral equation is not a trace contraction estimate. Neither new analytic assertion is a restatement of the item's norm-equivalence clause.

## Review by Q96

I checked delivery-errors B through E against the seven proof steps, the actual cited statements, and the sources above. None of the three new nodes merely repeats a clause of the item: strictness is a general finite-module theorem; the envelope is algebraic preparation; the trace bound is a specialized norm estimate. Their proofs are intentionally left unsplit as the one-level rule requires. Elementary character calculations, product completeness and the final Cauchy argument remain steps, not nodes. No proof step exceeds 2000 characters.

For step 1 I opened lem-trf-affinoid-quotient-norm-topology, lem-trf-affinoid-supremum-seminorm-calculus and lem-per-banach-character-norm-bound. The affinoid Banach topology supplies the initial complete algebra topology; a chosen Tate presentation is continuous and surjective. The first cited statement supplies completeness and equivalence for its quotient norm. The second explicitly supplies finite residue fields, finiteness of the supremum and its lower comparison with the quotient norm. Algebraic closedness identifies each residue field with K. I added an explicit argument that the quotient norm of 1 is 1, because the character-bound theorem assumes it: the constant lift gives at most 1, while submultiplicativity and nondegeneracy give at least 1. That theorem then supplies continuity of all residue characters. Conversely every unital K-character is onto and has maximal kernel. Thus the change from maximal ideals to the continuous characters of the item's formula is justified; no analytic Nullstellensatz is hidden in the step beyond the cited residue-field theorem.

For step 2 I checked the complete finite-module hypotheses of strictness. The envelope supplies finite C-module structures and bounded j_i. The finite maximum norm is complete coordinatewise, and module generators concatenate. Submultiplicativity gives the displayed bounded scalar action. C is finite over itself, so the injective j has the lower bound asserted by strictness. This is precisely where finite inclusion repairs the erroneous arbitrary-inclusion source argument.

For step 3 I reopened the full statement of lem-per-integral-trace-dual-lattice. I use only its first clause, which explicitly supplies an integral fraction-field basis and a trace matrix with nonzero determinant. T_i and B_i are normal domains, the injection is finite, and the envelope gives separability. The trace-bound node says the trace of every e_ik*b belongs to T_i. The adjugate argument then proves injectivity of the coordinate map in three lines. I corrected an earlier version using the statement's sheaf clause, to avoid importing unnecessary affine-scheme normality and section-identification facts. The present step uses only the cited algebraic assertions.

For step 4 I opened lem-trf-restricted-series-gauss-completion and the new strictness and trace-bound statements. T_i^n is complete with its maximum Gauss norm. B_i is finite over T_i, and E_i plus submultiplicativity bounds its scalar action. Thus strictness applies to the map of step 3, without needing to prove automatic continuity separately. The trace node supplies exactly the displayed coordinate norm bound. Multiplicativity in residue fields gives the remaining submultiplicative supremum inequality directly. The supremum-calculus node says these finitely many constants are finite. The trace-bound source argument uses trace=sum of Galois conjugates, invariance of maximal-ideal suprema under Galois automorphisms, maximal-ideal lying over for the finite integral extension, and the Gauss=supremum identity on the Tate algebra. Those ingredients belong to that new unsplit theorem, not to an unsupported assertion in the item's proof. Its trace lies in T because it is integral and belongs to Frac(T), and T is integrally closed. There is no division by the Galois group order, including in wild characteristic.

For step 5 the existing supremum-calculus statement explicitly gives the required functorial inequality for every affinoid homomorphism, including j_i. Substitution of the bounds of steps 2 and 4 gives the upper comparison with rho. M is enlarged to at least 1, and nondegeneracy follows immediately. The chosen presentation was arbitrary. For step 6 the residue/character formulas give the ultrametric and algebra-norm axioms pointwise; nonemptiness gives rho(1)=1. The cited calculus theorem explicitly states the positive-power identity. For step 7 both inequalities give the Cauchy and convergence implications written out; no completeness assumption for rho is used circularly.

I tested the statements on C=K (Tate dimension zero), Tate algebras themselves, C=K x K, and the reduced ring K<X,Y>/(XY). The product case explains why the envelope and the proof cannot assume C is a domain. If reducedness were dropped, a nonzero nilpotent would have rho=0, so reducedness is essential and retained. All B_i and T_i are nonzero; the finite product has at least one factor. Empty/zero finite modules are permitted in strictness and cause no problem with its positive bound. The trace construction has n_i>=1 and works when the extension has degree 1 or degree divisible by the characteristic. The inseparable-normalization issue was corrected as described above. All citations.json entries are exact quotations from the statements actually used, not from their proofs or sources.

The source inspections and actual logged searches distinguish Mathlib's finite-dimensional vector-space bounds from finite modules over analytic algebras. I read the spectralAlgNorm field hypotheses, the closed-range hypothesis of ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range, and the algebraic trace/normal-closure hits before rejecting them as matches. I did not write Lean, invoke a compiler, or write to the shared repository or launcher.

## Unfinished work

No missing argument remains in the assembly proof. The three new substantive inputs are statement-only DAG obligations, deliberately not recursively split in this delivery. Required dry-run and push results are reported by the delivery tool.
