+++
id = "def-pur-supported-cup"
kind = "definition"
title = "Cup product with closed supports"
order = 1941
uses = ["def-pur-support-cohomology", "def-weil-derived-tensor", "def-weil-scheme-morphism-properties", "lem-pur-supported-hom"]
+++
Let $i:Z\hookrightarrow X$ and $j:W\hookrightarrow X$ be
closed immersions, and
write $h:Z\times_XW\hookrightarrow X$. For classes
$\alpha\in H_Z^a(X,F)$ and $\beta\in H_W^b(X,G)$ in
supported cohomology, represent
them by morphisms as in [lem-pur-supported-hom].
Their *supported cup product* is the morphism

$$
h_*\Lambda_{Z\times_XW}
\cong i_*\Lambda_Z\otimes^L_\Lambda j_*\Lambda_W
\xrightarrow{\alpha\otimes\beta}(F\otimes^L_\Lambda G)[a+b],
$$

read as an element of $H_{Z\cap W}^{a+b}(X,F\otimes^L_\Lambda G)$.
The first identification is the stalkwise identification of the
coefficient sheaves: each stalk is either $0$ or the free module
$\Lambda$, so these sheaves are flat and their tensor is the
coefficient sheaf on the intersection. Tensor and shifts are those
of derived tensor.
