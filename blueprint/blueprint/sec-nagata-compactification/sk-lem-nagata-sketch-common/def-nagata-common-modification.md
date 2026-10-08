+++
id = "def-nagata-common-modification"
kind = "definition"
title = "Common-modification construction"
order = 239
lean = ["AlgebraicGeometry.CommonModification"]
uses = ["def-nagata-admissible-blowup", "def-nagata-elimination-indeterminacy", "def-nagata-extended-admissible-blowup", "def-nagata-global-blowup", "def-nagata-scheme-theoretic-image", "prop-nagata-global-blowup-cover-independent"]
+++
Let $U\hookrightarrow X_i$ be open immersions over $S$, with
$U,X_1,X_2$ separated and of finite type over the qcqs scheme $S$.
Construct the following objects in order.

1. Let
$$
X_{12}=\operatorname{SIm}
\bigl(U\longrightarrow X_1\times_SX_2\bigr)
$$
and write $p_i\colon X_{12}\to X_i$ for the projections.
1. Apply [def-nagata-elimination-indeterminacy] to $(p_i,U)$.
Denote the resulting blow-ups by
$X_i^i= X^{\mathrm{el}}(p_i,U)$, their center ideals by
$\mathcal I_i$, and the open strict transforms by
$X_{12}^i\subseteq X_i^i$.
1. On $X_{12}$ define
$$
\mathcal K_{12}
=p_1^{-1}\mathcal I_1\mathcal O_{X_{12}}\,
p_2^{-1}\mathcal I_2\mathcal O_{X_{12}},
\qquad
X'_{12}=\operatorname{Bl}_{\mathcal K_{12}}(X_{12}).
$$
1. The product-center blow-up maps to each $X_{12}^i$. Extend
$X'_{12}\to X_{12}^i$ across the open
$X_{12}^i\subseteq X_i^i$ by
[def-nagata-extended-admissible-blowup]; call the resulting
ambient schemes $X'_i$.
1. Define
$$
\mathsf{CM}(X_1,X_2;U)=X'_1\amalg_{X'_{12}}X'_2
$$
using the two constructed open immersions of $X'_{12}$.

The construction includes the maps $X'_i\to X_i$, the two open maps
$X'_i\to\mathsf{CM}(X_1,X_2;U)$, and the identified copy of $U$.

*Packaged interface.* What is recorded as data — and what the
formalised structure `CommonModification` carries — is only: the two
$U$-admissible blow-ups $X'_i\to X_i$, the two open immersions
$X'_i\to\mathsf{CM}(X_1,X_2;U)$ together with the fact that they cover
$\mathsf{CM}(X_1,X_2;U)$, the two lifted copies of $U$ and their agreement in
the glued scheme, and separatedness and finite type of
$\mathsf{CM}(X_1,X_2;U)\to S$. The stronger overlap identification of step 5
— that the two opens glue along *exactly* $X'_{12}$ and not merely along
their topological intersection — is an internal step of the construction: it is
used in the proof of [lemma-nagata-common-modification] to obtain
separatedness of the glued scheme, and separatedness is part of the packaged
interface. The downstream consumers
([def-nagata-two-open-final-modification] and
[lemma-nagata-two-open-density-transport]) use only the packaged
interface: density transport needs the two charts to cover and the copies of
$U$ to agree, and the valuative lifting argument needs only separatedness of
$\mathsf{CM}(X_1,X_2;U)\to S$.
