+++
id = "pqf-lem-qf-finitefibres"
kind = "lemma"
title = "Quasi-finite = finite type + quasi-compact + finite fibres"
order = 529
uses = ["def-weil-pbc-scheme-conventions", "pqf-def-quasifinite"]
+++
Let $f:X\to S$ be a morphism of schemes. Then $f$ is
quasi-finite if and only if $f$ is
locally of finite type, of finite type, quasi-compact and has finite
fibres.
(*Stacks Project, Morphisms of Schemes, Lemma 29.21.10, Tag
[02NH](https://stacks.math.columbia.edu/tag/02NH).*)

## Proof

*($\Rightarrow$).* Quasi-finite means: of finite type and every
point of $X$ is isolated in its fibre, by
[pqf-def-quasifinite]. Finite type in the sense of
[def-weil-pbc-scheme-conventions] is quasi-compact plus locally of
finite type, so only the finiteness of the fibres remains. Let $s\in S$
and put $X_s=X\times_S\operatorname{Spec}\kappa(s)$, a scheme
locally of finite type over the field $\kappa(s)$ ($f$ is locally of
finite type). Every point of $X_s$ is isolated, so the open
$X_s$ has dimension zero, and a locally finite type, quasi-compact,
zero-dimensional scheme over a field is the spectrum of an Artinian
$\kappa(s)$-algebra, a finite ring; its spectrum is a finite discrete
set (classical commutative algebra: finite type over a field with
dimension zero is Artinian, and Artinian rings have finitely many
prime ideals, all maximal). Hence $f^{-1}(\{s\})=|X_s|$ is finite.
*($\Leftarrow$).* Assume $f$ is locally of finite type and
quasi-compact (so of finite type by
[def-weil-pbc-scheme-conventions]) and has finite fibres. For
$x\in X$, with $s=f(x)$, the fibre $X_s$ is locally of finite type
over $\kappa(s)$ with finitely many points; restricting to an affine
open $\operatorname{Spec}A\subset X$ around $x$ with
$f(\operatorname{Spec}A)\subset\operatorname{Spec}R$ (which exists
because $f$ is locally of finite type, by
[pqf-def-quasifinite]), the ring
$A\otimes_R\kappa(s)$ has finitely many prime ideals; being of
finite type over the field $\kappa(s)$ it is Artinian, so all its
primes are maximal and $\operatorname{Spec}(A\otimes_R\kappa(s))$ is a
finite discrete set. Thus $x$ is an isolated point of its fibre, and
$R\to A$ is quasi-finite at the prime of $x$ in the sense of
[pqf-def-quasifinite]; hence $f$ is quasi-finite at every point,
which together with finite type is the definition of quasi-finite.
