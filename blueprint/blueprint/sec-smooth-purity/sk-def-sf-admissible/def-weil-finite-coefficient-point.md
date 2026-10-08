+++
id = "def-weil-finite-coefficient-point"
kind = "definition"
title = "Finite coefficient categories over a point"
order = 1509
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-finite-field-fiber", "def-weil-finite-torsion-constructibility"]
+++
Fix the global finite-field datum [def-weil-finite-field-fiber] $p,a,q,k_0,k$,
and fix a prime $\ell\neq p$. Write $\Ql=\mathbf Q_\ell$, choose an algebraic
closure $\Qlb$ of $\Ql$, and fix a finite extension $E/\Ql$ with valuation
ring $\mathcal O_E$, a uniformizer $\varpi_E$, and $n\geq1$. Put
$A_{E,n}=\mathcal O_E/\varpi_E^n$. The finite-torsion constructibility
[def-weil-finite-torsion-constructibility] and derived-complete integral
[def-weil-derived-complete-integral-detailed] conventions give the ordinary
derived categories $D(A_{E,n})$ and $D(\mathcal O_E)$. The
$\Qlb$-coefficient category uses the common finite-stage construction
[def-weil-algebraically-closed-coefficients]. Let $\mathcal E_\ell$ denote
the directed set of finite extensions $E'/\Ql$ contained in $\Qlb$. Let
$D^b_{\mathrm{fin}}(A_{E,n})$ be the full subcategory of $D(A_{E,n})$
consisting of bounded complexes with finite cohomology modules. Let
$D^b_{\mathrm{fg}}(\mathcal O_E)$ be the full subcategory of $D(\mathcal
O_E)$ consisting of bounded derived-complete complexes with finitely
generated cohomology modules, and let $D^b_{\mathrm{fd}}(E)$ be the bounded
derived category of finite-dimensional $E$-vector spaces. Put

$$
D^b_{\mathrm{fd}}(\Qlb)=
 \underset{E\in\mathcal E_\ell}{\operatorname{2-colim}}
 D^b_{\mathrm{fd}}(E).
$$

For $s=\operatorname{Spec}k$, evaluation at its geometric point defines
equivalences

$$
\operatorname{Fib}_s:D^b_c(s,A_{E,n})\xrightarrow{\sim}
D^b_{\mathrm{fin}}(A_{E,n}),\qquad
\operatorname{Fib}_s:D^b_c(s,\mathcal O_E)\xrightarrow{\sim}
D^b_{\mathrm{fg}}(\mathcal O_E),\qquad
\operatorname{Fib}_s:D^b_c(s,E)\xrightarrow{\sim}D^b_{\mathrm{fd}}(E).
$$

At the algebraically closed coefficient, the same functor is obtained
stagewise and then passed to the finite-stage colimit:

$$
\operatorname{Fib}_s:D^b_c(s,\Qlb)\xrightarrow{\sim}
D^b_{\mathrm{fd}}(\Qlb).
$$
