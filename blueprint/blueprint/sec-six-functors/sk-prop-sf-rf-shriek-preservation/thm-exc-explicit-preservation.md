+++
id = "thm-exc-explicit-preservation"
kind = "theorem"
title = "Preservation in the open and finite etale cases"
order = 2063
uses = ["def-weil-constructible-intervals", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties", "prop-exc-finite-etale-adjoint", "prop-exc-open-adjoint"]
+++
Let $A=A_{E,n}$, and let $f:V\to X$ be an
open immersion or a finite
etale morphism. Its ambient exceptional right adjoint satisfies

$$
Rf^{\times}D_c^{[a,b]}(X,A)\subseteq D_c^{[a,b]}(V,A).
$$

Here $D_c^{[a,b]}$ denotes the
constructible interval.
It also preserves the same
Tor-amplitude interval.
For every quotient $A\to B=A_{E,m}$, $m\leq n$, its
derived coefficient comparison is
an isomorphism:

$$
(Rf_A^{\times}K)\otimes_A^L B
\simeq Rf_B^{\times}(K\otimes_A^L B).
$$

For finite-Tor input the two sides are bounded constructible.
All bounds are independent of $n$.

## Proof

By [prop-exc-open-adjoint], [prop-exc-finite-etale-adjoint], the ambient
right adjoint is the exact functor $f^*$. Pull back each stratum in
[def-weil-finite-torsion-constructibility]. The resulting partition
is finite and constructible; inverse image of a locally constant finite
module sheaf is locally constant with the same finite module fibres.
Exactness identifies $\mathcal H^q(f^*K)$ with
$f^*\mathcal H^q(K)$, proving the assertion about the intervals of
[def-weil-constructible-intervals].

If $K$ has Tor amplitude $[a,b]$, the usual flat-resolution
criterion for [def-weil-finite-tor-amplitude] represents it by a
complex of flat module sheaves in these degrees. Inverse image preserves
flatness: the relations criterion for flatness is local and is preserved
by the exact inverse-image functor and its compatibility with tensor
products. Pulling back this bounded flat complex and tensoring it with
any module sheaf on $V$ proves the same Tor bound. Finally inverse
image is an exact tensor functor and preserves flat resolutions. Applying
it to a flat resolution in the definition of the derived tensor product
in [def-weil-derived-tensor] gives the displayed coefficient
isomorphism. No assertion that $A\to B$ is flat is used.
