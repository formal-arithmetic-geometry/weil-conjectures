+++
id = "def-weil-numbers"
kind = "definition"
title = "Weil numbers"
order = 2864
uses = ["def-weil-finite-field-fiber"]
+++
Fix a prime $p$, an integer $a\in\mathbf Z_{\geq1}$, and let
$q=p^a$ be the fixed prime power.
Fix an algebraic closure $\overline{\mathbf Q}$ of $\mathbf Q$. For every number field
$L\subset\overline{\mathbf Q}$, define

$$
\operatorname{Emb}_{\mathbf Q}(L,\mathbf C)=
\{\tau:L\longrightarrow\mathbf C:
\tau\text{ is a field homomorphism and }\tau|_{\mathbf Q}
=\operatorname{id}_{\mathbf Q}\}.
$$

For $\alpha\in\overline{\mathbf Q}^{\times}$, let
$\mathbf Q(\alpha)$ be the smallest subfield of $\overline{\mathbf Q}$
containing $\mathbf Q$ and $\alpha$. For $w\in\mathbf R$, call
$\alpha$ a
*$q$-Weil number of weight $w$* if

$$
\forall\tau\in
\operatorname{Emb}_{\mathbf Q}(\mathbf Q(\alpha),\mathbf C),
\qquad |\tau(\alpha)|=q^{w/2}.
$$

It is an *algebraic integer* if there are an integer $m\geq1$ and
integers $a_0,\ldots,a_{m-1}$ such that

$$
\alpha^m+a_{m-1}\alpha^{m-1}+\cdots+a_1\alpha+a_0=0.
$$
