+++
id = "def-weil-ordinary-compact-cohomology"
kind = "definition"
title = "Ordinary and compactly supported cohomology"
order = 1510
uses = ["def-coefficient-twists-detailed", "def-compact-support-direct-image-detailed", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-finite-coefficient-point", "def-weil-finite-field-fiber", "def-weil-pbc-proetale-site", "def-weil-rationalization-karoubi", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$, where
$q=p^a$, and a prime $\ell\neq p$. Write $\Ql=\mathbf Q_\ell$, choose an
algebraic closure $\Qlb$ of $\Ql$, and choose a finite extension $E/\Ql$
contained in $\Qlb$, with valuation ring $\mathcal O_E$, uniformizer
$\varpi_E$, and $n\geq1$. Put $A_{E,n}=\mathcal O_E/\varpi_E^n$ and
$\Lambda\in\{A_{E,n},\mathcal O_E,E,\Qlb\}$. Let $Y$ be a separated
finite-type [def-weil-scheme-morphism-properties] $k$-scheme and $a_Y:Y\to
s=\Spec k$ its structure morphism. Use the finite coefficient categories
[def-weil-finite-coefficient-point], Weil complexes
[def-weil-weil-sheaf-complex], derived direct image
[def-weil-derived-direct-image], compact-support direct image
[def-compact-support-direct-image-detailed], and Tate twists
[def-coefficient-twists-detailed]. Evaluation at the geometric point of $s$
gives equivalences

$$
\begin{aligned}
 \operatorname{Fib}_s:D^b_c(s,A_{E,n})&\xrightarrow{\sim}
 D^b_{\mathrm{fin}}(A_{E,n}),\\
 \operatorname{Fib}_s:D^b_c(s,\mathcal O_E)&\xrightarrow{\sim}
 D^b_{\mathrm{fg}}(\mathcal O_E),\\
 \operatorname{Fib}_s:D^b_c(s,E)&\xrightarrow{\sim}D^b_{\mathrm{fd}}(E).
\end{aligned}
$$

For $\Qlb$, the target is the stagewise $D^b_{\mathrm{fd}}(\Qlb)$ defined in
the finite-coefficient construction
[def-weil-finite-coefficient-point]. For $K\in D^b_c(Y,\Lambda)$, define the
coefficient complexes

$$
 \RGamma(Y,K)=\operatorname{Fib}_s(Ra_{Y*}K),
 \qquad
 \RGammac(Y,K)=\operatorname{Fib}_s(Ra_{Y!}K),
$$

and

$$
H^i(Y,K)=\mathrm H^i\bigl(\RGamma(Y,K)\bigr),
\qquad
H_c^i(Y,K)=\mathrm H^i\bigl(\RGammac(Y,K)\bigr).
$$

For a coefficient ring $\Lambda$ in the displayed list, let $\Lambda_Y$
denote its coefficient object on the small pro-etale site
[def-weil-pbc-proetale-site]: it is the finite-level constant
sheaf $(A_{E,n})_Y$ for $\Lambda=A_{E,n}$, the completed coefficient sheaf
$\widehat{\mathcal O}_{E,Y}$ from the derived-complete integral construction
[def-weil-derived-complete-integral-detailed] for $\Lambda=\mathcal O_E$, and
the scalar extensions supplied by the rationalized coefficient construction
[def-weil-rationalization-karoubi] and the algebraically closed coefficient
construction [def-weil-algebraically-closed-coefficients] for
$\Lambda=E,\Qlb$. When $\Lambda\in\{E,\Qlb\}$, equip it with the canonical
Weil structure from the Weil-sheaf structure
[def-weil-weil-sheaf-complex]. Abbreviate

$$
 H^i(Y,\Lambda)=H^i(Y,\Lambda_Y),\qquad
 H_c^i(Y,\Lambda)=H_c^i(Y,\Lambda_Y).
$$

For every integer $m$, the notation with a Tate twist means

$$
 H^i(Y,\Lambda(m))=H^i\bigl(Y,\Lambda_Y(m)\bigr),\qquad
 H_c^i(Y,\Lambda(m))=H_c^i\bigl(Y,\Lambda_Y(m)\bigr),
$$

where $\Lambda_Y(m)=\Lambda_Y\otimes^L_\Lambda\Lambda(m)_Y$ uses the
coefficient-twist construction [def-coefficient-twists-detailed]. In
particular, $(\Ql)_Y(m)$ denotes the twisted constant coefficient object and
$\Ql(m)$ is its coefficient-space notation in these abbreviations. If $K$ is
a Weil complex [def-weil-weil-sheaf-complex], each of these four symbols is
obtained by applying the displayed construction to $\operatorname{For}(K)$.
Whenever one of these coefficient spaces is finite-dimensional over its
field, its dimension, trace, and determinant have their ordinary
linear-algebraic meanings.
