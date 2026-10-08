+++
id = "lem-sc-isogeny-degree"
kind = "lemma"
title = "The degree of an isogeny"
lean = ["AlgebraicGeometry.IsIsogeny.finrank_eq", "AlgebraicGeometry.IsIsogeny.isFinite", "AlgebraicGeometry.IsIsogeny.flat"]
order = 558
uses = ["def-sc-abelian-variety", "def-sc-group-scheme", "def-sc-isogeny", "lem-sc-finite-constant-length-flat", "thm-pqf-finite-iff-proper-finite-fibres"]
+++
Let $f:A\to B$ be an isogeny of
abelian varieties over a field
$k$, with kernel $K=\ker f$ ([def-sc-group-scheme]), and
let $d:=\dim_k\mathcal O(K)$, the order of $K$, i.e. the
degree of $f$ in the sense of [def-sc-isogeny]. Then $f$
is finite and flat and $f_*\mathcal O_A$ is a locally free
$\mathcal O_B$-module of rank $d$: the degree of the finite
flat morphism $f$ is $d$.

## Proof

Since $f$ is an isogeny ([def-sc-isogeny]) it is a
surjective homomorphism of group schemes with finite kernel
$K=\ker f$ ([def-sc-group-scheme]), and $d=\dim_k\mathcal O(K)$ is its order. The morphism $f$ is proper, $A$ being
proper over $k$ ([def-sc-abelian-variety]), and its fibres
are finite: for a point $y$ of $B$ and an algebraically closed field
$\Omega\supseteq\kappa(y)$, the geometric fibre
$f^{-1}(y)\times_{\kappa(y)}\Omega=f_\Omega^{-1}(y_\Omega)$ has an
$\Omega$-point $x$ ($f$ is surjective), and translation by $x$ is an
isomorphism of $\Omega$-schemes from $K_\Omega$ onto it; so the
geometric fibre, hence $f^{-1}(y)$ itself, is finite. Hence $f$ is finite by
[thm-pqf-finite-iff-proper-finite-fibres] (the quasi-finite chapter).
Its fibre length is the constant $d$: the fibre $f^{-1}(y)$ need not
have a $\kappa(y)$-point and need not be isomorphic to $K$ over
$\kappa(y)$ (for $[n]$ on an elliptic curve the generic fibre is the
spectrum of a field extension of degree $n^2$ of the function field),
but the translation isomorphism above gives
$\dim_{\kappa(y)}\Gamma(f^{-1}(y),\mathcal O)
=\dim_\Omega\Gamma(f^{-1}(y)\times_{\kappa(y)}\Omega,\mathcal O)
=\dim_\Omega\bigl(\mathcal O(K)\otimes_k\Omega\bigr)=d$,
the length of a finite scheme over a field being unchanged by
extension of the field.
By [lem-sc-finite-constant-length-flat], the finite
surjective morphism $f$ is flat and $f_*\mathcal O_A$ is
locally free of rank $d$.
