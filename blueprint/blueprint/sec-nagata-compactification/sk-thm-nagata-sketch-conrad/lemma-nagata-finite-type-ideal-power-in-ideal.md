+++
id = "lemma-nagata-finite-type-ideal-power-in-ideal"
kind = "lemma"
title = "A power of a finite type ideal inside an ideal with larger zero set"
order = 213
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_pow_le"]
+++
Let $X$ be quasi-compact and let $\mathcal A,\mathcal B\subseteq\mathcal O_X$ be
quasi-coherent ideals with $\mathcal B$ of finite type and
$V(\mathcal A)\subseteq V(\mathcal B)$. Then $\mathcal B^n\subseteq\mathcal A$ for
some $n\geq 0$.

## Proof

The inclusion $V(\mathcal A)\subseteq V(\mathcal B)$ says exactly that
$\mathcal B\subseteq\sqrt{\mathcal A}$. On an affine open $\operatorname{Spec}(R)$ the
two ideals are ideals $\mathfrak b\subseteq\sqrt{\mathfrak a}$ of $R$ with
$\mathfrak b$ finitely generated, so $\mathfrak b^n\subseteq\mathfrak a$ for some $n$.
Since $X$ is quasi-compact it is covered by finitely many affine opens, and the maximum
of the exponents obtained there works on each member of the cover; containment of
quasi-coherent ideals may be checked on an affine cover.
