+++
id = "lem-wf-curve-finite-level-pd"
kind = "lemma"
title = "Finite-level degree-one Poincare pairing on a curve"
order = 2620
uses = ["def-coefficient-twists-detailed", "def-weil-pbc-etale-cohomology", "lem-sc-cohomological-dimension", "lem-wf-curve-kummer-jacobian-tate-module", "thm-av-final", "thm-pod-equivariance-of-the-twisted-pairing", "thm-pod-point-perfectness", "thm-pod-proper-poincare-duality", "thm-sc-proper-cohomology"]
+++
Let $C_0/k_0$ be a smooth projective geometrically connected curve,
let $C=C_0\times_{k_0}\overline{k}_0$, and put
$A_n=\mathbf Z/\ell^n\mathbf Z$ with
$\ell\ne\operatorname{char}k_0$. The cup product followed by the
trace gives a perfect $A_n$-bilinear pairing

$$
H^1_{\mathrm{\acute et}}(C,A_n)\times
H^1_{\mathrm{\acute et}}(C,A_n(1))\longrightarrow A_n.
\tag{3.4}
$$

Here the coefficient and twist conventions are those of
[def-coefficient-twists-detailed], [def-weil-pbc-etale-cohomology].

## Proof

Write $R=A_n$ and $L=R\Gamma(C,A_n(1))$. By
[lem-sc-cohomological-dimension], $H^i(L)=0$ for
$i\notin\{0,1,2\}$. The degree-zero group is $R(1)$, since $C$ is
connected. The proper-curve Kummer computation in
[thm-sc-proper-cohomology] shows that $H^2(L)$ is free of rank one over $R$; no choice of its basis is needed below.
Finally, Kummer and the Jacobian identification in
[lem-wf-curve-kummer-jacobian-tate-module], followed by
[thm-av-final](c), gives

$$
H^1(L)\cong J[\ell^n](\overline{k}_0)\cong R^{2g},
$$

where $g=\dim J$. Thus every cohomology module of $L$ is finite free. Over the
algebraically closed field, choosing a primitive $\ell^n$-th root gives a
(noncanonical) isomorphism of sheaves $A_n(1)\cong A_n$; hence the
cohomology modules of $R\Gamma(C,A_n)$ are finite free as well.

We record the elementary splitting argument needed here. A bounded complex
of finite free $R$-modules whose cohomology modules are projective is
isomorphic in the derived category to the direct sum of its cohomology
modules placed in their degrees. Indeed, starting in the largest degree,
split $0\to Z^i\to L^i\to B^{i+1}\to0$; then split
$0\to B^i\to Z^i\to H^i(L)\to0$. Descending induction shows that all
boundaries and cycles are projective and produces the direct-sum
decomposition; the complementary two-term summands have identity
differential and are contractible. The required bounded finite-free model
for $L$ is supplied by [thm-pod-point-perfectness].

Apply this splitting to $L$. Proper duality
[thm-pod-proper-poincare-duality], with the constant coefficient object
and $d=1$, identifies

$$
R\Gamma(C,A_n)^\vee\xrightarrow{\sim}L[2].
$$

After the displayed decompositions, the degree-one component of this
isomorphism is

$$
H^1(C,A_n)^\vee\xrightarrow{\sim}H^1(C,A_n(1)).
$$

By construction this component is the adjoint of the cup–trace pairing,
so (3.4) is perfect. No assertion about a degreewise perfect pairing over a
non-field is being taken directly from the derived statement; the freeness
and the elementary splitting above are what pass from derived duality to
degree one. Naturality and Frobenius equivariance of the pairing are the
finite-level specialization of
[thm-pod-equivariance-of-the-twisted-pairing].
