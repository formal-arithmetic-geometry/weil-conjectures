+++
id = "lemma-weil-pbc-prime-factor-induction"
kind = "lemma"
title = "Prime-factor induction"
order = 1088
uses = ["def-weil-pbc-derived-exchange"]
+++
If a statement about torsion sheaves is stable under short exact sequences,
then its verification for all $F[n]$ reduces by induction on the total number
of prime factors of $n$ to its verification for sheaves killed by one prime.

## Proof

Choose a prime $\ell\mid n$ and use the short exact sequence
$0\to F[\ell]\to F[n]\xrightarrow{\ell}\ell F[n]\to0$.
The kernel is killed by $\ell$, while $\ell F[n]$ is killed by $n/\ell$ and
therefore has fewer prime factors in its exponent. Let
$C(F)=\operatorname{Cone}(\operatorname{Ex}_{\square,F})$ and use the
cohomological cone convention
$d_{C}(y,x)=(d_Yy+u(x),-d_Xx)$. Applying the two derived functors to the
short exact sequence gives a distinguished triangle of exchange maps and,
by the octahedral axiom, a triangle

$$
C(F[\ell])\longrightarrow C(F[n])\longrightarrow
C(\ell F[n])\xrightarrow{+1}C(F[\ell])[1].
$$

The connecting map is the class of $(y,x)\mapsto y$ in the above cone
convention; the sign in the last arrow is forced by
$d_C^2=0$. Induct on
$\nu(n)=\sum_\ell v_\ell(n)$. If the two end cones are acyclic, the long
exact cohomology sequence of this triangle makes the middle cone acyclic.
The base $\nu(n)=1$ is the prime-torsion input. This displays the invariant
and all connecting morphisms.
