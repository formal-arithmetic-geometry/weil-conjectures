+++
id = "lem-wf-finite-field-curve-quasi-projective"
kind = "lemma"
title = "Finite-field curves admit a projective closure"
order = 2612
uses = ["def-weil-pbc-scheme-conventions"]
+++
Let $k_0$ be a field and let $U_0$ be an integral separated scheme of
finite type over $k_0$ of dimension at most one. There are an integer $N$,
a locally closed immersion $a:U_0\hookrightarrow\mathbf P^N_{k_0}$,
and an integral projective scheme $X_0$ such that $a$ identifies
$U_0$ with a dense open subscheme of $X_0$, its scheme-theoretic
closure in $\mathbf P^N_{k_0}$.

## Proof

The dimension-one quasi-projectivity lemma of the Stacks Project,
Varieties, Lemma 33.43.3,
[Tag 0A25](https://stacks.math.columbia.edu/tag/0A25), says that
$U_0$ has an ample invertible sheaf. Its proof is elementary at the
level needed here: powers of an ample sheaf have finitely many sections
whose nonvanishing loci are affine, and the resulting section map is a
locally closed immersion into projective space. Thus choose such an
immersion $a$. A locally closed immersion is an open immersion into its
scheme-theoretic closure $X_0$. The latter is closed in projective space,
so it is projective by the projective-space and scheme conventions of
[def-weil-pbc-scheme-conventions]. Since $U_0$ is integral, its closure $X_0$ is
integral and the image of $U_0$ is dense.
