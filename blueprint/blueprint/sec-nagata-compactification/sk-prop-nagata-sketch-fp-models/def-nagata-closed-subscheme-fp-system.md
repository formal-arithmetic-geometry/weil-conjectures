+++
id = "def-nagata-closed-subscheme-fp-system"
kind = "definition"
title = "Finite-presentation closed-subscheme system"
order = 387
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.FGSub", "AlgebraicGeometry.Scheme.IdealSheafData.fgSubCone", "AlgebraicGeometry.Scheme.IdealSheafData.fgSubDiagram"]
+++
Let $X=V(\mathcal I)\hookrightarrow Y$ be closed with $Y$ qcqs. Let
$A_{X/Y}$ be the directed set of finite type quasi-coherent subideals
$\mathcal I_\alpha\subseteq\mathcal I$, ordered by inclusion. Define

$$
X_\alpha=V(\mathcal I_\alpha)\hookrightarrow Y,
$$

and for $\alpha\leq\beta$ define the transition
$X_\beta\hookrightarrow X_\alpha$ from
$\mathcal I_\alpha\subseteq\mathcal I_\beta$.
