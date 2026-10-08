+++
id = "sk-lem-sf-open-ctf"
kind = "section"
title = "Extension by zero preserves the finite-Tor constructible category"
order = 2159
uses = ["sk-def-sf-operations"]
lean = ["AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek"]
+++
*Lemma (sketch).*

Let $j:U\hookrightarrow Y$ be an open immersion of finite-type $k$-schemes and
let $K\in\Dctf(U,\Lambda)$ at a finite coefficient stage. Then
$j_!K\in\Dctf(Y,\Lambda)$, and its cohomological range and Tor amplitude may be
taken to be those of $K$.
Chapter 19, lem:trf-open-ctf: $j_!$ is exact, so
$\mathcal H^r(j_!K)=j_!\mathcal H^r(K)$ and the range does not grow; a finite
stratification of $U$ witnessing constructibility, together with the closed
complement $Y\setminus U$, stratifies $Y$; and the amplitude is tested by
restricting an arbitrary sheaf on $Y$ to $U$.

Uses: `\Cref{sk-def-sf-operations}`, `lem-trf-open-ctf`
