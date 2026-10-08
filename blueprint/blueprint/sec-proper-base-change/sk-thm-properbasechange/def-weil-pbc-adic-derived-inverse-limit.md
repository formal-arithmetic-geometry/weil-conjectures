+++
id = "def-weil-pbc-adic-derived-inverse-limit"
kind = "definition"
title = "Explicit adic derived inverse limit"
order = 1256
uses = ["def-weil-pbc-complete-coefficient-datum"]
+++
For a tower $M_\bullet=(M_n,t_{n+1,n})$, put

$$
s((x_n)_n)=(t_{n+1,n}(x_{n+1}))_n,
\qquad
R\varprojlim_nM_n:=\operatorname{Cone}
\left(1-s:\prod_nM_n\longrightarrow\prod_nM_n\right)[-1].
$$

Thus there is a functorial distinguished triangle

$$
R\varprojlim_nM_n\longrightarrow\prod_nM_n
\xrightarrow{1-s}\prod_nM_n\longrightarrow .
$$

Maps of towers act componentwise on the two products and hence on the cone.
