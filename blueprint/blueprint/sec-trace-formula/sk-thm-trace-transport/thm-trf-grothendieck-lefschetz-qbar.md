+++
id = "thm-trf-grothendieck-lefschetz-qbar"
kind = "theorem"
title = "Grothendieck–Lefschetz formula over $\\Qlb$"
order = 2399
uses = ["def-trf-coefficient-conventions", "def-trf-frobenius-operators", "def-trf-karoubi-trace", "def-trf-trace-class", "def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-finite-field-fiber", "def-weil-ordinary-compact-cohomology", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "prop-trf-karoubi-independence", "prop-trf-rational-frobenius-integral-model", "prop-trf-trace-formal-laws", "thm-trf-trace-formula-e"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and the
coefficient conventions.
Let $X_0$ be a
separated finite-type
$k_0$-scheme, put $X=X_0\times_{k_0}k$, let
$K\in D^b_{c,\mathrm W}(X,\Qlb)$ be a
Weil complex, represented by
$(E,K_E)$ with $E/\Ql$ finite in $\Qlb$ and
$K_E\in D^b_{c,\mathrm W}(X,E)$, as in the
common-stage
coefficient construction, with underlying Weil map
$\varphi_E:Lg_\gamma^*K_E\to K_E$ in $D^b_c(X,E)$. The Frobenius operators
$F^{\,m}_{c,K}$ on $R\Gamma_c(X,K)=R\Gamma_c(X,K_E)\otimes_E\Qlb$ and
$F_{y,m}$ on $K_{\bar y}=K_{E,\bar y}\otimes_E\Qlb$ are the scalar
extensions of the $E$-stage operators of $(K_E,\varphi_E)$ of
[prop-trf-rational-frobenius-integral-model]; at the finite levels these
are the operators of [def-trf-frobenius-operators]. No integral Weil
presentation of $\varphi_E$, or of any rescaling of it, is assumed.
Assume only the finite-level hypotheses of [thm-trf-trace-formula-e] for
some lattice of $K_E$: at every level $A_{E,n}$, an explicit etale-origin
witness for its reduction and compactification admissibility.
For every integer $m\geq1$,

$$
\boxed{
\sum_{i\in\mathbf Z}(-1)^i
\operatorname{Tr}\bigl(F_{c,K}^{\,m}\mid H_c^i(X,K)\bigr)
=
\sum_{y\in X_0(\mathbf F_{q^m})}
\sum_{j\in\mathbf Z}(-1)^j
\operatorname{Tr}\bigl(F_{y,m}\mid H^j(K_{\bar y})\bigr).}
$$

All vector spaces are finite-dimensional over $\Qlb$, only finitely
many degrees occur, every trace is the image of an $E$-valued trace
along $E\hookrightarrow\Qlb$, and the equality is independent of the
finite field, the representative, and the common overfield.

## Proof

Apply [thm-trf-trace-formula-e] to
$K_E\in D^b_{c,\mathrm W}(X,E)$ with its Weil map $\varphi_E$; that
theorem needs no integral Weil presentation and only the finite-level
hypotheses assumed here. It gives finite-dimensional $E$-cohomology in
finitely many degrees, and the identity holds in $E$ for the
categorical traces and, by the supertrace law
[prop-trf-trace-formal-laws], for the alternating sums of the
traces on compact-support and stalk cohomology. The object $K$ is
represented by $K_E$, so the global cohomology and each local stalk
are the scalar extensions along $E\hookrightarrow\Qlb$ of the
$E$-level ones, and the traces are the images of the $E$-traces, by
the scalar-extension law of [prop-trf-trace-formal-laws] applied
to the summand traces of [def-trf-karoubi-trace] (at the identity
idempotent the summand trace is the ordinary categorical trace); hence
applying the summand trace to both sides of the $E$-identity gives
the displayed identity after scalar extension $E\hookrightarrow\Qlb$.
Independence is [prop-trf-karoubi-independence].
