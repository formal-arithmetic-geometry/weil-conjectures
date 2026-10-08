+++
id = "thm-trf-integral-adic-coefficient-morphism-trace-formula"
kind = "theorem"
title = "Integral adic trace formula for Frobenius coefficient morphisms"
order = 2395
uses = ["def-trf-adic-system", "def-trf-admissibility", "def-trf-coefficient-conventions", "def-weil-finite-field-fiber", "def-weil-pbc-etale-origin-witness", "prop-trf-adic-coefficient-morphism-systems", "prop-trf-rational-frobenius-integral-model", "thm-trf-coefficient-morphism-trace-formula"]
+++
Fix the global finite-field datum $p,a,q,k_0,k$ and the coefficient
conventions of [def-trf-coefficient-conventions], with
$A_n=A_{E,n}$. Let $X_0$ be a separated finite-type $k_0$-scheme,
$X=X_0\times_{k_0}k$, let $K_\bullet$ be a normalized $A_\bullet$-system on
$X$ and $\psi_\bullet$ a compatible system of Frobenius coefficient
morphisms on it, in the sense of [prop-trf-adic-coefficient-morphism-systems],
with $P_n$, $P_{\bar y,n}$, $P_{\mathcal O}$, $P_{\bar y,\mathcal O}$ as
there; no invertibility of the $\psi_n$ is assumed. At every finite level
$n$ assume the hypotheses of [thm-trf-coefficient-morphism-trace-formula]
for $(K_n,\psi_n)$: an explicit etale-origin witness for $K_n$
([def-weil-pbc-etale-origin-witness]) and the exceptional-adjoint
admissibility of [def-trf-admissibility] for the graph correspondences and
fixed-point base changes on a chosen compactification defined over $k_0$.

1. For every $m\geq1$,
$$
\boxed{\,
\operatorname{tr}_{\mathcal O_E}\bigl(F_{c,m}(\psi_\bullet)\mid P_{\mathcal O}\bigr)
=\sum_{y\in X_0(\mathbf F_{q^m})}
\operatorname{tr}_{\mathcal O_E}\bigl(\psi_{\bullet,m,\bar y}\mid P_{\bar y,\mathcal O}\bigr)
\,}
$$
in $\mathcal O_E$; that is, $\operatorname{tr}_{\mathcal O_E}(V_m)=\sum_y
\operatorname{tr}_{\mathcal O_E}(V_{y,m})$ for any lifts $V_m$ of
$(F_{c,m}(\psi_n))_n$ and $V_{y,m}$ of $(\psi_{n,m,\bar y})_n$.
1. *Lattice form.* Let $K_{\mathcal O}$, $\varphi_E=\varpi^{-N}u$, $\psi_n=u_n\circ\kappa_{K_n}$,
$U_m$ and $U_{y,m}$ be as in [prop-trf-rational-frobenius-integral-model]
(so $K_\bullet$ is the reduction tower of $K_{\mathcal O}$), and assume the
finite-level hypotheses above. Then for every $m\geq1$
$$
\operatorname{tr}_{\mathcal O_E}\bigl(U_m\mid R\Gamma_c(X,K_{\mathcal O})\bigr)
=\sum_{y\in X_0(\mathbf F_{q^m})}
\operatorname{tr}_{\mathcal O_E}\bigl(U_{y,m}\mid K_{\mathcal O,\bar y}\bigr)
\quad\text{in }\mathcal O_E .
$$

## Proof

*(1).* By [prop-trf-adic-coefficient-morphism-systems], items (1) and (3),
each $P_n$ and $P_{\bar y,n}$ is perfect and the families
$(F_{c,m}(\psi_n))_n$ and $(\psi_{n,m,\bar y})_n$ are compatible; by its
item (2) they have lifts, and by its item (4) the traces of any lifts are
the compatible systems
$$
\operatorname{tr}_{\mathcal O_E}(V_m)=\bigl(\operatorname{tr}_{A_n}(F_{c,m}(\psi_n)\mid P_n)\bigr)_n,
\qquad
\operatorname{tr}_{\mathcal O_E}(V_{y,m})=\bigl(\operatorname{tr}_{A_n}(\psi_{n,m,\bar y}\mid P_{\bar y,n})\bigr)_n .
$$
At each level $n$, [thm-trf-coefficient-morphism-trace-formula], applied to
$(K_n,\psi_n)$ under the assumed hypotheses (it requires no invertibility of
$\psi_n$), gives
$$
\operatorname{tr}_{A_n}\bigl(F_{c,m}(\psi_n)\mid P_n\bigr)
=\sum_{y\in X_0(\mathbf F_{q^m})}\operatorname{tr}_{A_n}\bigl(\psi_{n,m,\bar y}\mid P_{\bar y,n}\bigr)
\quad\text{in }A_n,
$$
with the stalk endomorphism normalized as there and in
[prop-trf-adic-coefficient-morphism-systems]. The index set
$X_0(\mathbf F_{q^m})$ is finite ($X_0$ is of finite type over $k_0$) and the
same for all $n$, and the reduction $\mathcal O_E\to A_n$ is additive. Hence
$\operatorname{tr}_{\mathcal O_E}(V_m)$ and $\sum_y\operatorname{tr}_{\mathcal O_E}(V_{y,m})$
have the same image in every $A_n$, and they are equal because
$\mathcal O_E\to\varprojlim_nA_n$ is injective.

*(2).* By [prop-trf-rational-frobenius-integral-model], item (2), the
$\psi_n$ form a compatible system of Frobenius coefficient morphisms on the
reduction tower of $K_{\mathcal O}$; this tower, with the associativity
isomorphisms $K_{n+1}\otimes^L_{A_{n+1}}A_n\cong
K_{\mathcal O}\otimes^L_{\mathcal O_E}A_n=K_n$ as $\nu_n$, is a normalized
$A_\bullet$-system of [def-trf-adic-system], its levels lying in
$D^b_{ctf}(X,A_n)$ by hypothesis. For it
$P_{\mathcal O}=R\Gamma_c(X,K_{\mathcal O})$ and
$P_{\bar y,\mathcal O}=K_{\mathcal O,\bar y}$
([prop-trf-adic-coefficient-morphism-systems]). By items (3) and (4) of
[prop-trf-rational-frobenius-integral-model], $U_m$ is the derived limit of
the levelwise operators $F_{c,m}(\psi_n)$ and $U_{y,m}$ that of the
$\psi_{n,m,\bar y}$, i.e. $\mathrm{pr}_n\circ U_m=F_{c,m}(\psi_n)\circ\mathrm{pr}_n$
and likewise for the stalks; so by item (2) of
[prop-trf-adic-coefficient-morphism-systems] they are lifts of the two
compatible families, and (1) gives the identity.
