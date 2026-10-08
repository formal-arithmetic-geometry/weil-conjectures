+++
id = "def-weil-finite-field-fiber"
kind = "definition"
title = "Finite field and geometric fiber"
order = 411
uses = ["def-weil-finite-type-morphism"]
+++
Throughout this blueprint, fix a prime $p$ and an integer $a\in\mathbf
Z_{\geq1}$, and put $q=p^a$. Set

$$
 k_0=\Fq,
 \qquad
 k=\Fbar\text{ (a fixed algebraic closure of }k_0\text{)}.
$$

The tuple $(p,a,q,k_0,k)$ is the *global finite-field datum* used throughout.
For every integer $n\geq1$, let $\mathbf F_{q^n}\subset k$ be the unique
subfield with $q^n$ elements. For any scheme $S$, write $|S|$ for its set of
closed points and, for $s\in|S|$, write $\kappa(s)$ for the residue field at
$s$. For a $k_0$-scheme $Y_0$ whose structure morphism is of finite type
[def-weil-finite-type-morphism], write

$$
 Y=Y_0\times_{k_0}k,
 \qquad
 a_Y:Y\longrightarrow\Spec k
$$

for its geometric fiber and structure morphism. For every finite-type
$k_0$-scheme $Y_0$ and every $n\geq1$, define

$$
 Y_0(\mathbf F_{q^n})
 =\operatorname{Hom}_{k_0}\bigl(\operatorname{Spec}\mathbf F_{q^n},Y_0\bigr),
 \qquad
 \#Y_0(\mathbf F_{q^n})=\#\operatorname{Hom}_{k_0}
 \bigl(\operatorname{Spec}\mathbf F_{q^n},Y_0\bigr).
$$

For each prime $\ell\neq p$, write $\Ql=\mathbf Q_\ell$, choose an algebraic
closure $\Qlb$ of $\Ql$, and write $\Zl$ for the valuation ring of $\Ql$.
Thus $\Qlb$ is algebraically closed over $\Ql$, and $\Zl$ consists of the
elements of nonnegative $\ell$-adic valuation. A single choice of $\ell$ and
its coefficient fields is understood whenever they occur without a subscript.
For every finite extension $E/\Ql$, write $\mathcal O_E$ for its valuation
ring, choose a uniformizer $\varpi_E$, and, for every $n\geq1$, set

$$
 A_{E,n}=\mathcal O_E/\varpi_E^n.
$$
