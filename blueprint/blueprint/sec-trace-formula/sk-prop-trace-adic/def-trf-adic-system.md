+++
id = "def-trf-adic-system"
kind = "definition"
title = "Normalized adic Weil system"
order = 2385
uses = ["def-trf-coefficient-conventions", "def-weil-derived-complete-integral-detailed", "def-weil-finite-field-fiber", "def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-derived-inverse-limit"]
+++
Fix the global finite-field datum
and the coefficient
conventions, with $A_n=A_{E,n}$. An
*$A_\bullet$-system* on $X$ is a family

$$
K_\bullet=\bigl(K_n,t_{n+1,n}\bigr)_{n\geq1},\qquad
K_n\in D^b_{ctf}(X,A_n),
$$

with transition morphisms compatible with the quotients
$A_{n+1}\twoheadrightarrow A_n$; it is *normalized* if
$K_n\otimes_{A_n}^LA_j\xrightarrow{\sim}K_j$ for $j\leq n$. Using the
adic coefficient datum of
the proper-base-change chapter and the
derived inverse limit,
define

$$
K_{\mathcal O_E}:=R\!\varprojlim_n\operatorname{Res}_{n,X}K_n,
$$

and let $\mathcal D^b_{ctf,\mathrm W,adic}(X,\mathcal O_E)$ be the
category of normalized systems with a strict Weil structure at every
level, compatible with the transitions; the resulting realizations are
the derived-complete bounded
constructible $\mathcal O_E$-complexes of the framework chapter with finite
Tor amplitude, by the reconstruction of the proper-base-change chapter (the levelwise
statements below).
