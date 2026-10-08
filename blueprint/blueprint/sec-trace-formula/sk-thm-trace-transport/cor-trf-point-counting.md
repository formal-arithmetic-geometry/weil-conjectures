+++
id = "cor-trf-point-counting"
kind = "theorem"
title = "Point-counting trace formula"
order = 2401
tags = ["latex:corollary"]
uses = ["cor-trf-constant-stalk-trace", "def-trf-frobenius-operators", "def-weil-finite-field-fiber", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-etale-origin-witness", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "thm-trf-grothendieck-lefschetz-qbar"]
+++
Fix the global finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, let $X_0$ be a
separated finite-type
$k_0$-scheme, put $X=X_0\times_{k_0}k$, and let
$K=(\Qlb)_X$ be the constant
Weil sheaf with its canonical
Weil structure, the geometric Frobenius acting trivially. Assume
the compactification admissibility of
[thm-trf-grothendieck-lefschetz-qbar] for the constant lattice
$(\mathcal O_E)_X$ of $E_X$ at every finite level (the etale-origin
witnesses required there are supplied in the proof). Then for every
$m\geq1$,

$$
\#X_0(\mathbf F_{q^m})
=
\sum_{i\in\mathbf Z}(-1)^i
\operatorname{Tr}\bigl(F^m\mid H_c^i(X,\Qlb)\bigr),
$$

and, when $X_0$ is
proper,

$$
\#X_0(\mathbf F_{q^m})
=
\sum_{i\in\mathbf Z}(-1)^i
\operatorname{Tr}\bigl(F^m\mid H^i(X,\Qlb)\bigr),
$$

compactly supported cohomology being the ordinary one.

## Proof

The constant finite-level sheaves $A_{E,n}$ on the etale sites,
with their identity identifications after comparison pullback,
give the explicit witnesses of
[def-weil-pbc-etale-origin-witness] for the reductions
$(A_{E,n})_X$ of the constant lattice $(\mathcal O_E)_X$ of $K_E=E_X$.
Thus the finite-level hypotheses of
[thm-trf-grothendieck-lefschetz-qbar] hold for this lattice, and that
theorem applies to $K$.
For the constant Weil sheaf, the local geometric Frobenius
[def-trf-frobenius-operators] is the identity of the one-dimensional
stalk
$(\Qlb)_{\bar y}$, so

$$
\sum_{j}(-1)^j\operatorname{Tr}\bigl(F_{y,m}\mid H^j(K_{\bar y})\bigr)=1
$$

for every rational point $y$ (the unit stalk trace of [cor-trf-constant-stalk-trace], read at the field stage), and the right-hand side of
[thm-trf-grothendieck-lefschetz-qbar] is the cardinality of
$X_0(\mathbf F_{q^m})$, which is finite because $X_0$ is of finite
type. This is the first identity; the second is the identification
$H_c^i\simeq H^i$ for proper $X_0$ of
[def-weil-ordinary-compact-cohomology].
