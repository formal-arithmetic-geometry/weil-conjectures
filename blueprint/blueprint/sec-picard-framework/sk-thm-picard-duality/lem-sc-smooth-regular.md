+++
id = "lem-sc-smooth-regular"
kind = "lemma"
title = "Smoothness implies regularity"
order = 692
uses = ["def-sc-curves", "lem-sc-regular-local-domain"]
+++
Let $C$ be a smooth curve over a field
$k$. Then every local ring $\mathcal O_{C,P}$ is regular (hence
a domain).

## Proof

By definition, a morphism is smooth if and only if it is locally of
finite presentation, flat, and has geometrically regular fibres
(the standard definition of smoothness: the fibres are regular and
remain regular after every base change by a field extension). For
the structure morphism $C\to\operatorname{Spec}k$, this says that
each local ring $\mathcal O_{C,P}$ is geometrically regular over
$k$: the ring $\mathcal O_{C,P}\otimes_kk'$ is regular for every
finite extension $k'/k$. Taking $k'=k$, the ring
$\mathcal O_{C,P}$ itself is regular, hence a domain by
[lem-sc-regular-local-domain].
