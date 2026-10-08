+++
id = "lem-weil-closed-costalk-duality"
kind = "lemma"
title = "Exceptional restriction of a Verdier dual"
order = 2125
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-open-closed-recollement"]
+++
Let $i:Z\hookrightarrow T$ be a closed immersion and suppose the
ambient exceptional adjoints are defined, with
$\omega_Z=Ri^!\omega_T$. Put
$D_T=R\mathcal Hom_T(-,\omega_T)$ and
$D_Z=R\mathcal Hom_Z(-,\omega_Z)$. Then there is a natural
isomorphism

$$
\alpha_K:Ri^!D_TK\xrightarrow{\sim}D_Zi^*K.
$$

This assertion does not use biduality.

## Proof

For any test complex $N$ on $Z$, the tensor adjunction of
[def-weil-derived-pullback-tensor-hom] and the closed exceptional
adjunction of [def-weil-exceptional-inverse-image] give

$$
\begin{aligned}
\operatorname{Hom}_Z(N,Ri^!D_TK)
&\cong\operatorname{Hom}_T(i_*N\otimes^L K,\omega_T)\\
&\cong\operatorname{Hom}_T(i_*(N\otimes^L i^*K),\omega_T)\\
&\cong\operatorname{Hom}_Z(N\otimes^L i^*K,\omega_Z)\\
&\cong\operatorname{Hom}_Z(N,D_Zi^*K).
\end{aligned}
$$

The middle projection identity holds for a closed immersion in the
recollement of [def-weil-open-closed-recollement] because
$i_*$ is exact and fully faithful, and its stalkwise extension by
zero commutes with tensor product; flat resolutions give the derived
identity. The calculation localizes on every etale test object, so it
identifies the internal Hom objects. Yoneda proves the isomorphism.
Every arrow is defined by adjunction and evaluation, giving naturality.
