+++
id = "def-pc-ext"
kind = "definition"
title = "Extensions"
order = 1166
lean = ["CategoryTheory.Abelian.Ext", "CategoryTheory.ProjectiveResolution.isoExt", "isZero_Ext_succ_of_projective"]
+++
Let $\mathcal A$ be an abelian category (for a scheme $X$: the category
of $\mathcal{O}_X$-modules, or any abelian subcategory of it closed under the
operations below) and let $F,G$ be objects of $\mathcal A$ and
$i\ge0$. The *$i$-th Ext group* is

$$
\operatorname{Ext}^{i}_{\mathcal A}(F,G)
\;:=\;\Hom_{D(\mathcal A)}\bigl(F,\;G[i]\bigr),
$$

the group of morphisms from $F$ to the $i$-fold shift of $G$ in the
derived category ([def-pc-derived-category]); equivalently
(i.e. by the standard identification of the two descriptions, the
classical one via an injective resolution of $G$) it is the $i$-th
cohomology of the derived $\mathbf R\Hom(F,G)$. For sheaves on a
scheme $X$ one writes $\operatorname{Ext}^{i}_{\mathcal{O}_X}(-,-)$ (or
$\operatorname{Ext}^{i}_X(-,-)$) for the case
$\mathcal A$ the category of $\mathcal{O}_X$-modules, and

$$
\mathcal{E}xt^{i}_{\mathcal{O}_X}(F,G):=H^i\mathcal{H}om^{\bullet}_{\mathcal{O}_X}(F,G)
$$

denotes the associated sheaf ($\mathcal{H}om^{\bullet}$ the derived
inner hom of sheaves).
