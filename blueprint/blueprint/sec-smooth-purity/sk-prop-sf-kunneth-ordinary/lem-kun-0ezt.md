+++
id = "lem-kun-0ezt"
kind = "lemma"
title = "Higher direct images along limits of cartesian squares"
order = 1657
uses = ["def-weil-pbc-cartesian-square", "def-weil-pbc-scheme-conventions"]
+++
Let $I$ be directed and let

$$
\begin{array}{ccc}
X_i&\xleftarrow{\;h_i\;}&Y_i\\
\Big\downarrow{\scriptstyle f_i}&&\Big\downarrow{\scriptstyle e_i}\\
S_i&\xleftarrow{\;g_i\;}&T_i
\end{array}
\qquad(i\in I)
$$

be an inverse system of
cartesian squares with affine
transition morphisms, where every $g_i$ is
quasi-compact and
quasi-separated. Write

$$
\begin{array}{ccc}
X&\xleftarrow{\;h\;}&Y\\
\Big\downarrow{\scriptstyle f}&&\Big\downarrow{\scriptstyle e}\\
S&\xleftarrow{\;g\;}&T
\end{array}
$$

If $(F_i)$ is a compatible system of torsion abelian sheaves on
$T_i$, $F=\varinjlim_ip_i^{-1}F_i$, and if for a fixed $q\ge0$ every
base-change map

$$
f_i^{-1}R^qg_{i,*}F_i\longrightarrow R^qh_{i,*}e_i^{-1}F_i
$$

is an isomorphism, then so is

$$
f^{-1}R^qg_*F\longrightarrow R^qh_*e^{-1}F.
$$

(*Source:* Stacks Project,
[Tag `0EZT`](https://stacks.math.columbia.edu/tag/0EZT), second
assertion; the first assertion of that tag, for sheaves of sets, is not used
in this chapter.) In the Stacks Project this assertion is deduced from Lemma 59.51.8,
[Tag `0EYM`](https://stacks.math.columbia.edu/tag/0EYM)
(higher direct images commute with filtered colimits along an inverse
system whose transition morphisms are affine), applied to the two sides
of the base-change map.
The torsion hypothesis recorded here is the case used in this chapter, whose
coefficients are $\kunZn$-module sheaves.

## Proof

This is the recorded classical input named in the statement, Stacks Project, Tag [0EZT](https://stacks.math.columbia.edu/tag/0EZT), second assertion: a base-change isomorphism for a fixed cohomological degree passes to the inverse limit of an inverse system of cartesian squares with affine transition morphisms. In the Stacks Project it is deduced from Lemma 59.51.8 ([Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)), higher direct images commuting with filtered colimits along such a system. The blueprint records the torsion case used in this chapter; no separate proof is given.
