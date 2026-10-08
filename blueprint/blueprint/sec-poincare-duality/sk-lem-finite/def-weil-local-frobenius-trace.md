+++
id = "def-weil-local-frobenius-trace"
kind = "definition"
title = "Local Frobenius and local alternating trace"
order = 2428
uses = ["def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-global-geometric-frobenius", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex"]
+++
Fix the finite-field datum $p,a,q,k_0,k$, a prime $\ell\neq p$. Write
$\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of $\Ql$, and choose
a finite extension $E/\Ql$ contained in $\Qlb$. Let $Y_0$ be a finite-type
$k_0$-scheme, put $Y=Y_0\times_{k_0}k$, and choose $K\in D^b_{c,\mathrm
W}(Y,E)$, a Weil complex. For a closed point $y\in|Y_0|$, with $|Y_0|$ and
$\kappa(y)$ the closed-point and residue-field notation, let $y$ have degree
$r=[\kappa(y):\Fq]$. Choose an embedding $\kappa(y)\hookrightarrow k$ and the
associated geometric point $\bar y\to Y$. Iterating the Weil isomorphism $r$
times and using the resulting return to $\bar y$ defines, for every
$j\in\mathbf Z$, the local operator $F_y$ associated with the global
geometric-Frobenius action on the stalk of the cohomology sheaf $\mathcal
H^j(\operatorname{For}K)_{\bar y}$.

More generally, for every $n\in\mathbf Z_{\geq1}$ and $x\in Y_0(\mathbf
F_{q^n})$ in the finite-field point set, choose an associated geometric point
$\bar x\to Y$; the $n$-fold iterate at $\bar x$ defines $F_x^{(n)}$. Put

$$
  K_{\bar x}:=
  L\bar x^*\operatorname{For}(K),\qquad
  \Tr(F_x^{(n)}\mid K_{\bar x})=
 \sum_{j\in\mathbf Z}(-1)^j
 \Tr\bigl(F_x^{(n)}\mid
 \mathcal H^j(\operatorname{For}K)_{\bar x}\bigr).
$$

Here $L\bar x^*$ is the derived pullback.
