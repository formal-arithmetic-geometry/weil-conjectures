+++
id = "def-nagata-finite-type-ideal-extension"
kind = "definition"
title = "Finite-type extension of an ideal from a quasi-compact open"
order = 166
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteType_comap_eq"]
uses = ["def-nagata-extended-ideal", "lemma-nagata-dense-flat-pullback", "lemma-nagata-finite-type-ideal-extension-exists"]
+++
Let $X$ be quasi-compact and quasi-separated, let $W\subseteq X$ be a
quasi-compact open, and let
$\mathcal J\subseteq\mathcal O_W$ be a finite type quasi-coherent ideal.
By classical choice from
[lemma-nagata-finite-type-ideal-extension-exists], select a finite type
quasi-coherent ideal on $X$ restricting to $\mathcal J$, and define

$$
\operatorname{Ext}_{X,W}(\mathcal J)\subseteq\mathcal O_X
$$

to be this selected ideal.
