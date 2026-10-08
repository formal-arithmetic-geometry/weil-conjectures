+++
id = "lem-sf-proetale-residue-tor-test"
kind = "lemma"
title = "The residue test on the pro-étale site"
order = 1867
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\geq1$ and $A=A_{E,n}$, put $\kappa=A/(\varpi_E)$, let $T$ be a
scheme on which $\ell$ is invertible, and let
$K\in D^b_c(T_{\Proet},A)$ be a bounded constructible complex of
$A$-modules on the small pro-étale site in the intrinsic sense of
[def-weil-finite-torsion-constructibility]. Then $K$ has finite
Tor amplitude in $[a,b]$ if and
only if the derived tensor product $K\otimes_A^L\kappa_T$ with the
constant sheaf $\kappa_T$ has cohomology only in $[a,b]$.

## Proof

One direction is the definition [def-weil-finite-tor-amplitude], the
constant sheaf $\kappa_T$ being a sheaf of $A$-modules placed in degree
zero. Conversely, every sheaf $N$ of $\kappa$-modules is flat over
$\kappa$ (sectionwise tensor over a field is exact, and so is
sheafification), so by associativity of the derived tensor product of
[def-weil-derived-tensor]

$$
\mathcal H^r(K\otimes^L_AN)\cong\mathcal H^r\bigl((K\otimes^L_A\kappa_T)
\otimes^L_\kappa N\bigr)\cong\mathcal H^r(K\otimes^L_A\kappa_T)\otimes_\kappa N,
$$

which vanishes outside $[a,b]$. A sheaf $M$ of $A$-modules has the finite
filtration $\varpi_E^sM$, $0\le s\le n$, whose graded pieces are sheaves
of $\kappa$-modules; the long exact cohomology sequences of
$K\otimes^L_A-$ applied to the short exact sequences of this filtration
give $\mathcal H^r(K\otimes^L_AM)=0$ for $r\notin[a,b]$, which is finite
Tor amplitude in $[a,b]$. The argument uses no stalks and no comparison
with the étale site.
