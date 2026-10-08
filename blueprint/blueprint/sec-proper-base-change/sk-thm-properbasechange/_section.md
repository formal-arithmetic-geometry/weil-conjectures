+++
id = "sk-thm-properbasechange"
kind = "section"
title = "Proper base change"
order = 1205
lean = ["AlgebraicGeometry.Etale.isIso_baseChange_of_isProper"]
uses = ["sk-def-conv", "sk-def-exchange", "sk-def-pbc", "sk-thm-p1", "sk-thm-reduction"]
+++
*Theorem (sketch).*

For a proper morphism $f:X\to Y$ and every
torsion sheaf $F$ on $X_{\Et}$, $\mathrm{PBC}(f)$ holds in the sense
of [sk-def-pbc]: the exchange morphism

$$
\Ex_{\square,F}:g^{-1}Rf_*F\xrightarrow{\ \sim\ }Rf'_*g'^{-1}F
$$

is an isomorphism.

## Proof

**Step 1 ($\Pone$).** By [sk-thm-p1], $\Pone_S\to S$
satisfies PBC for every $S$.

**Step 2 (reduction).** [sk-thm-reduction] now applies:
every proper morphism $f$ satisfies $\mathrm{PBC}(f)$ for
$\Fq$-coefficients, all primes $r$.

**Step 3 (finite torsion).** A sheaf killed by $n$ is
decomposed by the exact sequences $0\to F[r]\to F\to rF\to0$
(induction on the number of prime factors of $n$, five lemma); any
torsion sheaf is the filtered union of its $n$-torsion parts, over
which the proper $R^qf_*$ commutes. Hence $\mathrm{PBC}(f)$ for
every torsion sheaf: [sk-thm-properbasechange].

Uses: [sk-def-conv], [sk-def-exchange], [sk-def-pbc], [sk-thm-p1], [sk-thm-reduction]
