+++
id = "def-weil-pbc-completed-pullback"
kind = "definition"
title = "Completed pullback"
order = 1261
uses = ["def-weil-pbc-adic-coefficient-datum", "def-weil-pbc-complete-coefficient-datum", "def-weil-pbc-derived-inverse-limit", "def-weil-pbc-proetale-operations"]
+++
For $g:Y'\to Y$ define

$$
Lg^*_{\mathrm{comp}}K:=
R\varprojlim_n\bigl(Lg^*K\otimes^L_\Lambda\Lambda/I^n\bigr).
$$

The comparison from ordinary pullback is the completion map of $Lg^*K$.

## Detailed form

For $g:T'\to T$, levelwise inverse image on strict tower complexes has a
total left derived functor

$$
 Lg^*_{\operatorname{Tow}}:
 D(\operatorname{Tow}_{A}(T))
 \longrightarrow D(\operatorname{Tow}_{A}(T')).
$$

Its $n$-th evaluation on the reduction tower $K_\bullet$ of
[def-weil-pbc-adic-coefficient-datum] is $Lg_n^*K_n$. For a derived complete
$K$, define

$$
 Lg^*_{\mathrm{comp}}K
   =\Rlim\bigl(Lg^*_{\operatorname{Tow}}K_\bullet\bigr)
 \quad\text{in }D(T'_{\Proet},A).
$$

The object $Lg^*_{\mathrm{comp}}K$ is the $Lf^*_{comp}$ of Stacks Project,
Lemma 61.20.2 (2) and (5) (Tag
[099N](https://stacks.math.columbia.edu/tag/099N), Section 61.20, Tag
[099L](https://stacks.math.columbia.edu/tag/099L)), namely $Lf^*$ followed by
derived completion, computed as
$R\lim Lf^*(M\otimes^L_\Lambda\underline{\Lambda/I^n})$: the Stacks entry
assumes a Noetherian ring $\Lambda$, an ideal $I$ and a morphism of topoi,
and characterizes $Lf^*_{comp}$ as the left adjoint of $Rf_*$ on derived
complete objects, while the form used here defines it by the derived limit of
the levelwise pullback tower of [def-weil-pbc-adic-coefficient-datum].
