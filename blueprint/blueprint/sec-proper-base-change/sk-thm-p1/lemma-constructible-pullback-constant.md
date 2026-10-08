+++
id = "lemma-constructible-pullback-constant"
kind = "lemma"
title = "Pullback of a constant sheaf"
order = 1160
lean = ["AlgebraicGeometry.Scheme.upperStarConstantSheafIso"]
uses = ["def-constructible-constant"]
+++
For $g\colon Y\to X$ and $M\in\mathcal A$ there is a natural isomorphism
$g^*(M_X)\cong M_Y$. In particular $g^*$ sends constant sheaves to constant
sheaves.

## Proof

Both $M\mapsto g^*(M_X)$ and $M\mapsto M_Y$ are left adjoint to
$\mathcal G\mapsto\Gamma(Y,\mathcal G)=\Gamma(X,g_*\mathcal G)$, because
base change along $g$ preserves the terminal object of the site
($Y\times_XX\cong Y$); left adjoints are unique up to unique isomorphism.
