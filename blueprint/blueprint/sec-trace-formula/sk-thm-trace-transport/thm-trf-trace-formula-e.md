+++
id = "thm-trf-trace-formula-e"
kind = "theorem"
title = "Trace formula over a finite extension"
order = 2396
uses = ["def-trf-adic-system", "def-trf-admissibility", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-weil-cohomological-support", "def-weil-derived-complete-integral-detailed", "def-weil-finite-field-fiber", "def-weil-integral-rational-qbar-compact-support", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-etale-origin-witness", "def-weil-pbc-rational-category", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "lem-trf-chain-supertrace", "prop-trf-adic-coefficient-morphism-systems", "prop-trf-rational-frobenius-integral-model", "prop-trf-trace-formal-laws", "prop-weil-pbc-rational-transport", "thm-trf-coefficient-morphism-trace-formula", "thm-trf-integral-adic-coefficient-morphism-trace-formula"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and the
coefficient conventions of [def-trf-coefficient-conventions], with
$A_n=A_{E,n}=\mathcal O_E/\varpi^n$. Let $X_0$ be
separated finite-type
over $k_0$ ([def-weil-scheme-morphism-properties]), put
$X=X_0\times_{k_0}k$, let
$K_E\in D^b_c(X,E)$ be an object of the
rationalized
$E$-coefficient category ([def-weil-rationalization-karoubi],
[def-weil-pbc-rational-category]), and let

$$
\varphi_E:Lg_\gamma^*K_E\longrightarrow K_E
$$

be an arbitrary morphism of $D^b_c(X,E)$, for instance the Weil
structure of an $E$-Weil complex. No invertibility of $\varphi_E$, no
invertibility of a rescaling $c\,\varphi_E$ on a lattice, and no
integral Weil presentation is assumed. Let $F^{\,m}_{c,K_E}$ on
$R\Gamma_c(X,K_E)$ and $F_{y,m}$ on $K_{E,\bar y}$ be the $E$-stage
Frobenius operators of $(K_E,\varphi_E)$ defined in
[prop-trf-rational-frobenius-integral-model] (the stalk being
$K_{\mathcal O,\bar y}\otimes_{\mathcal O_E}E$ for a lattice
$K_{\mathcal O}$, as there).

*Lattice and finite-level hypotheses.* Let $K_{\mathcal O}\in
D^b_c(X,\mathcal O_E)$ ([def-weil-derived-complete-integral-detailed])
together with an isomorphism $\alpha:K_{\mathcal O}\xrightarrow{\sim}K_E$
of $D^b_c(X,E)$ be a lattice of $K_E$. One always exists: the objects of
$D^b_c(X,E)$ are those of $D^b_c(X,\mathcal O_E)$, so one may take
$K_{\mathcal O}=K_E$ and $\alpha=\operatorname{id}$. Put
$K_n=K_{\mathcal O}\otimes^L_{\mathcal O_E}A_n$. Assume at every finite
level $n$ the finite-level hypotheses of
[thm-trf-coefficient-morphism-trace-formula] for $K_n$. These are an
explicit etale-origin witness for $K_n$
([def-weil-pbc-etale-origin-witness]) and the exceptional-adjoint
admissibility of [def-trf-admissibility] for the graph correspondences of
the iterates $\Phi^m$ and the fixed-point base changes on a chosen
compactification defined over $k_0$. They concern $K_n$ and the geometry
of $X_0$ only, not $\varphi_E$; they are the data "assumed at each
finite level" in the source and are not proved here.

Then the $E$-vector spaces $H_c^i(X,K_E)$ and $H^j(K_{E,\bar y})$ are
finite-dimensional and nonzero for only finitely many $i$, $j$, and for
every $m\geq1$,

$$
\sum_{i\in\mathbf Z}(-1)^i
\operatorname{Tr}\bigl(F_{c,K_E}^m\mid H_c^i(X,K_E)\bigr)
=
\sum_{y\in X_0(\mathbf F_{q^m})}
\sum_{j\in\mathbf Z}(-1)^j
\operatorname{Tr}\bigl(F_{y,m}\mid H^j(K_{E,\bar y})\bigr)
$$

in $E$. For any clearing of denominators $\varphi_E=\varpi^{-N}u$ on the
lattice, the two sides are $\varpi^{-Nm}$ times the images under
$\mathcal O_E\to E$ of the two sides of the integral identity of
[thm-trf-integral-adic-coefficient-morphism-trace-formula], item (2), and
they agree with the corresponding $E$-valued categorical traces by the
supertrace law over the field $E$ of [prop-trf-trace-formal-laws].

This covers the Weil structure of every $E$-Weil complex. It also covers
Weil maps that are not invertible after any rescaling on any lattice, such
as $\varphi_E=\operatorname{diag}(1,\ell)$ on $E^2$ over
$X_0=\Spec\mathbf F_q$ (the example of
[prop-trf-rational-frobenius-integral-model]). The earlier hypothesis of a
strict integral Weil presentation of some rescaling $c\,\varphi_E$ is a
special case and is no longer needed.

## Proof

*Step 0: the reduction tower.* By
[def-weil-derived-complete-integral-detailed] each $K_n$ lies in
$D^b_c(X,A_n)$, and the cohomological supports
([def-weil-cohomological-support]) of all $K_n$ lie in one interval
$[r,s]$. Each $K_n$ has Tor amplitude in $[r,s]$, hence lies in
$D^b_{ctf}(X,A_n)$. Indeed, let $N$ be an $A_n$-module. The subquotients
$N'$ of the finite filtration $\varpi^iN$ are $A_1$-modules, and
$K_n\otimes^L_{A_n}N'\cong(K_n\otimes^L_{A_n}A_1)\otimes^L_{A_1}N'
\cong K_1\otimes_{A_1}N'$ by associativity of the derived tensor product
($K_n\otimes^L_{A_n}A_1\cong K_{\mathcal O}\otimes^L_{\mathcal O_E}A_1=K_1$).
Since $A_1$ is a field, $N'$ is free, so this is a direct sum of copies of
$K_1$, with cohomology sheaves in degrees $[r,s]$. The distinguished
triangles of the filtration give the same bound for
$K_n\otimes^L_{A_n}N$. The associativity isomorphisms
$K_{n}\otimes^L_{A_{n}}A_j\cong K_j$ ($j\leq n$) and the transitions of the
functorial reduction tower of [def-weil-pbc-adic-coefficient-datum] make
$K_\bullet$ a normalized $A_\bullet$-system of [def-trf-adic-system]. In
particular $K_{\mathcal O}$ satisfies the hypotheses of
[prop-trf-rational-frobenius-integral-model].

*Step 1: reduction to $\alpha=\operatorname{id}$.* Put
$\varphi_{\mathcal O}=\alpha^{-1}\circ\varphi_E\circ Lg_\gamma^*\alpha:
Lg_\gamma^*K_{\mathcal O}\to K_{\mathcal O}$ in $D^b_c(X,E)$. By induction
on $m$ and functoriality of the rationalized pullbacks,
$\varphi_{\mathcal O}^{[m]}=\alpha^{-1}\circ\varphi_E^{[m]}\circ
Lg_\gamma^{m*}\alpha$. The base-change isomorphisms $g_{\gamma,c}^{m,*}$ and
the stalk transports $\tau_{y,m}$ at the stage $E$ are rationalizations of
natural integral transformations ([prop-weil-pbc-rational-transport]),
hence natural. So the operators of
[prop-trf-rational-frobenius-integral-model] for
$(K_{\mathcal O},\varphi_{\mathcal O})$ are
$R\Gamma_c(X,\alpha)^{-1}\circ F^{\,m}_{c,K_E}\circ R\Gamma_c(X,\alpha)$ and
$\alpha_{\bar y}^{-1}\circ F_{y,m}\circ\alpha_{\bar y}$. Passing to
cohomology, these are conjugate to the operators for
$(K_E,\varphi_E)$ by $E$-linear isomorphisms, which changes neither the
dimensions nor the traces. We may therefore assume $K_E=K_{\mathcal O}$
(viewed in $D^b_c(X,E)$) and $\alpha=\operatorname{id}$.

*Step 2: the integral model.* By
[prop-trf-rational-frobenius-integral-model], item (1), choose $N\geq0$ and
an integral $u:Lg_\gamma^*K_{\mathcal O}\to K_{\mathcal O}$ with
$\varphi_E=\varpi^{-N}u$. By its item (2), $\psi_n=u_n\circ\kappa_{K_n}$ is a
compatible system of Frobenius coefficient morphisms on $K_\bullet$, not
necessarily invertible. By its items (3) and (4), the integral operators
$U_m$ on $R\Gamma_c(X,K_{\mathcal O})$ and $U_{y,m}$ on
$K_{\mathcal O,\bar y}$ satisfy

$$
F^{\,m}_{c,K_E}=\varpi^{-Nm}\bigl(U_m\otimes_{\mathcal O_E}E\bigr),
\qquad
F_{y,m}=\varpi^{-Nm}\bigl(U_{y,m}\otimes_{\mathcal O_E}E\bigr).
$$

By item (2) of [prop-trf-adic-coefficient-morphism-systems], applied to
the reduction tower $K_\bullet$ (for which
$P_{\mathcal O}=R\Gamma_c(X,K_{\mathcal O})$ and
$P_{\bar y,\mathcal O}=K_{\mathcal O,\bar y}$), both complexes are
represented by bounded complexes of finite free $\mathcal O_E$-modules.
Hence $R\Gamma_c(X,K_E)=R\Gamma_c(X,K_{\mathcal O})\otimes_{\mathcal O_E}E$
([def-weil-integral-rational-qbar-compact-support]) and
$K_{E,\bar y}=K_{\mathcal O,\bar y}\otimes_{\mathcal O_E}E$ are bounded
complexes of finite-dimensional $E$-vector spaces, which is the finiteness
assertion.

*Step 3: the integral identity.* The finite-level hypotheses assumed in the
statement are those of
[thm-trf-integral-adic-coefficient-morphism-trace-formula] for
$(K_\bullet,\psi_\bullet)$: they do not involve $\psi_n$. Its item (2)
gives

$$
\operatorname{tr}_{\mathcal O_E}\bigl(U_m\mid R\Gamma_c(X,K_{\mathcal O})\bigr)
=\sum_{y\in X_0(\mathbf F_{q^m})}
\operatorname{tr}_{\mathcal O_E}\bigl(U_{y,m}\mid K_{\mathcal O,\bar y}\bigr)
\quad\text{in }\mathcal O_E .
$$

*Step 4: rationalization.* Let $\rho:\mathcal O_E\to E$ be the inclusion.
Since $E$ is flat over $\mathcal O_E$, $P\otimes^L_{\mathcal O_E}E=P\otimes
_{\mathcal O_E}E$ for the complexes of Step 2, and the scalar-extension law
of [prop-trf-trace-formal-laws], item (3), gives
$\rho\bigl(\operatorname{tr}_{\mathcal O_E}(U_m)\bigr)
=\operatorname{tr}_E\bigl(U_m\otimes E\mid R\Gamma_c(X,K_E)\bigr)$, and
likewise for each $U_{y,m}$ (directly: by the chain-level computation of
[lem-trf-chain-supertrace] over $\mathcal O_E$ and over $E$, both sides
equal $\sum_i(-1)^i\operatorname{Tr}(U_m^i\mid M^i)$ for a finite free
model $M$ of Step 2 and a chain representative of $U_m$). By the
supertrace law over the field $E$,
item (4) of the same proposition,
$\operatorname{tr}_E(U_m\otimes E)=\sum_i(-1)^i\operatorname{Tr}
\bigl(H^i(U_m\otimes E)\mid H_c^i(X,K_E)\bigr)$, and likewise for the stalks.
The cohomology functors $H^i$ are $E$-linear on morphisms and the ordinary
trace is $E$-linear, so by Step 2

$$
\sum_i(-1)^i\operatorname{Tr}\bigl(F^{\,m}_{c,K_E}\mid H_c^i(X,K_E)\bigr)
=\varpi^{-Nm}\rho\Bigl(\operatorname{tr}_{\mathcal O_E}\bigl(U_m\mid
R\Gamma_c(X,K_{\mathcal O})\bigr)\Bigr),
$$

and likewise
$\sum_j(-1)^j\operatorname{Tr}(F_{y,m}\mid H^j(K_{E,\bar y}))
=\varpi^{-Nm}\rho\bigl(\operatorname{tr}_{\mathcal O_E}(U_{y,m}\mid
K_{\mathcal O,\bar y})\bigr)$. The set $X_0(\mathbf F_{q^m})$ is finite
($X_0$ is of finite type over $k_0$) and $\rho$ is additive. Applying $\rho$
to the identity of Step 3 and multiplying by $\varpi^{-Nm}$ gives the
displayed identity. The result does not depend on the choice of $(N,u)$:
replacing it by $(N+1,\varpi u)$ multiplies $U_m$, $U_{y,m}$ by $\varpi^m$
and leaves $\varpi^{-Nm}(U_m\otimes E)$ unchanged
([prop-trf-rational-frobenius-integral-model]).
