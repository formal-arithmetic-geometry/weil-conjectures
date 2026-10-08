+++
id = "lem-weil-pbc-local-rings-ind-zariski"
kind = "lemma"
title = "Local-ring identifications with w-local target"
order = 1230
uses = ["def-weil-pbc-ind-etale-algebra", "def-weil-pbc-w-local", "lem-weil-pbc-w-local-partition"]
+++
Suppose $A\to B$ identifies every local ring: for every prime $q\subset B$,
the map $A_{q\cap A}\to B_q$ is an isomorphism. If $\operatorname{Spec}B$ is
w-local [def-weil-pbc-w-local], then $B/A$ is ind-Zariski
[def-weil-pbc-ind-etale-algebra].

## Proof

Consider an arbitrary finitely presented algebra $P/A$ with a map $P\to B$.
At a maximal ideal $q$ of $B$, its finitely many generators become fractions
in $A_{q\cap A}$. Choose a common denominator and then clear the finitely
many defining relations. This gives $f\notin q\cap A$ and $P\to A_f$ inducing
the given local map. Equality with $P\to B$, and invertibility of $f$, hold
on an open neighbourhood $O_q$ of $q$, since only finitely many equalities
must be checked.

By [lem-weil-pbc-w-local-partition], the closed points of
$\operatorname{Spec}B$ have a finite clopen partition subordinate to finitely
many $O_q$'s. Its extension to $\operatorname{Spec}B$ is still subordinate to
these opens. Write $B=\prod_{j=1}^mB_j$ for the corresponding idempotent
decomposition. The local factorizations give

$$
 P\longrightarrow\prod_{j=1}^mA_{f_j}
 \longrightarrow\prod_{j=1}^mB_j=B.
$$

Here is the finite-presentation argument turning this into the claimed
colimit, rather than merely a supply of local maps. Take all finite products
of principal localizations equipped with an $A$-map to $B$. Two have a common
successor by applying the displayed factorization to their tensor product.
For two parallel maps, impose equality on finitely many algebra generators in
their target; the resulting finitely presented quotient still maps to $B$,
and the displayed factorization equalizes the two maps at a successor. Thus
this category is filtered. Polynomial algebras show that its colimit surjects
onto $B$; imposing one equation shows injectivity. This is the ind-Zariski
presentation of [def-weil-pbc-ind-etale-algebra].
