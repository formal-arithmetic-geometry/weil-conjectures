+++
id = "p-linear-triangular"
kind = "theorem"
title = "Triangularization"
order = 2390
tags = ["latex:proposition"]
+++
A single endomorphism of a finite-dimensional
$k$-space admits a full flag of invariant subspaces,
with one-dimensional graded pieces.

## Proof

Induct on $\dim V$, the zero space carrying the empty flag. Since $k$ is
algebraically closed, the characteristic polynomial of $f$ has a root, so
$f$ has an eigenvector $v$ and the line $L=kv$ is invariant. The induced
endomorphism of $V/L$ is well defined, and by induction it has a full
invariant flag with one-dimensional quotients. Pulling that flag back
along $V\to V/L$ and prepending $L$ gives a full invariant flag of $V$.
In a basis adapted to it, $f$ is upper triangular with the flag's
eigenvalues on the diagonal. Mathlib has the generalized eigenspace
decomposition `Module.End.iSup_maxGenEigenspace_eq_top` over an
algebraically closed field, but no flag statement.
