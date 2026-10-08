+++
id = "lem-weil-field-tor-amplitude"
kind = "lemma"
title = "Finite Tor amplitude at field coefficients"
order = 2060
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-rationalization-karoubi"]
+++
Let $F$ be a field, let $Y$ be a scheme, and let $K$ be a bounded
constructible complex at a field coefficient stage: an object of the
rationalized category $D^b_c(Y,E)$ of [def-weil-rationalization-karoubi] with
$F=E$, or an object of the common-stage category $D^b_c(Y,\Qlb)$ of
[def-weil-algebraically-closed-coefficients] with $F=\Qlb$. Then $K$ has
finite Tor amplitude in the sense of [def-weil-finite-tor-amplitude]: there
are integers $a\leq b$ such that

$$
 \mathcal H^r\bigl(K\otimes^L_FM\bigr)=0
 \qquad(r\in\mathbf Z\setminus[a,b])
$$

for every sheaf $M$ of $F$-modules placed in degree zero, the derived tensor
product being that of [def-weil-derived-tensor].

## Proof

Over a field $F$ every $F$-module is flat, so a sheaf $M$ of $F$-modules
placed in degree zero is K-flat and the derived tensor product of
[def-weil-derived-tensor] is computed by the ordinary tensor product; hence
$\mathcal H^r(K\otimes^L_FM)\cong\mathcal H^r(K)\otimes_FM$ for every
$r\in\mathbf Z$. The bounded constructibility imposed in
[def-weil-rationalization-karoubi] and in
[def-weil-algebraically-closed-coefficients] gives integers $a\leq b$ with
$\mathcal H^r(K)=0$ for $r\notin[a,b]$; on this interval the vanishing
required by [def-weil-finite-tor-amplitude] holds vacuously in the remaining
degrees, and off it both sides vanish. Such a pair $a\leq b$ is therefore a
finite Tor amplitude interval for $K$.
