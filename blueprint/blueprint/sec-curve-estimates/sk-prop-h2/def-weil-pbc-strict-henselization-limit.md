+++
id = "def-weil-pbc-strict-henselization-limit"
kind = "definition"
title = "Strict henselization from pointed neighbourhoods"
order = 944
uses = ["def-weil-pbc-pointed-etale-neighbourhoods"]
+++
Let

$$
\mathcal I_{\bar s}:=
(\mathcal N^{\mathrm{aff}}_{\bar s})^{\mathrm{op}}.
$$

For $V=\operatorname{Spec}A_V$, define
$D_{\bar s}:\mathcal I_{\bar s}\to\mathbf{CRing}$ by
$D_{\bar s}(V,\bar v)=A_V$. An arrow
$(W,\bar w)\to(V,\bar v)$ in $\mathcal I_{\bar s}$ represented by a pointed
map $a:(V,\bar v)\to(W,\bar w)$ is sent to
$a^\#:A_W\to A_V$. Put

$$
A^{\mathrm{sh}}_{S,\bar s}:=\varinjlim_{\mathcal I_{\bar s}}D_{\bar s},
\qquad
S_{(\bar s)}:=\operatorname{Spec}A^{\mathrm{sh}}_{S,\bar s}.
$$

The affine scheme–ring anti-equivalence carries the colimit cocone to the
canonical limit cone

$$
S_{(\bar s)}\xrightarrow{\sim}
\varprojlim_{(V,\bar v)\in\mathcal N^{\mathrm{aff}}_{\bar s}}V.
$$

## Detailed form

For affine $(V,\bar v)$ with $V=\operatorname{Spec}A_V$, put

$$
 \mathcal O^{\mathrm{sh}}_{S,\bar s}
   =\varinjlim_{(V,\bar v)}A_V,
 \qquad
 S_{(\bar s)}=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{S,\bar s}.
$$

The canonical maps from $S_{(\bar s)}$ to the affine pointed etale
neighborhoods identify it with their inverse limit; these affine
neighborhoods form the indexing subcategory used in the displayed colimit.
