+++
id = "lem-trf-fixed-map-proper"
kind = "lemma"
title = "The induced map of fixed schemes is proper"
order = 2327
uses = ["def-trf-borel-moore-pushforward", "def-trf-coefficient-pushforward", "def-trf-fixed-scheme", "def-trf-trace-class", "def-weil-scheme-morphism-properties", "lem-kun-proper-stability", "lem-weil-pbc-closed-immersion-proper"]
+++
Let $(f,g):(C,c)\to(D,b)$ be a proper pushforward diagram of
[def-trf-coefficient-pushforward], with induced map
$h:F_c=\operatorname{Fix}(c)\to F_b=\operatorname{Fix}(b)$. Then:

1. $h$ factors as
$$
h:\ F_c\xrightarrow{\ \kappa\ }C\times_DF_b\xrightarrow{\ \pi\ }F_b,
$$
where $\pi$ is the base change of $g$ along $i_b:F_b\to D$, and
$\kappa$ is a base change of the relative diagonal
$\Delta_{X/Y}:X\to X\times_YX$, hence a closed immersion;
1. $h$ and $q=f\times f:X\times_sX\to Y\times_sY$ are proper.

Consequently, for a correspondence $u$ on $(X,K)$ supported on $c$, with
the exceptional admissibility of $h$ and of the structure morphisms of
$F_c,F_b$, the *proper pushforward of the trace class*

$$
h_*\operatorname{Tr}_c(u):A_{F_b}\longrightarrow\omega_{F_b}
$$

is defined: it is the Borel–Moore pushforward of
[def-trf-borel-moore-pushforward] of the Borel–Moore section
$\operatorname{Tr}_c(u)$ of [def-trf-trace-class].

## Proof

Put $G=C\times_DF_b$, with projections $\pi:G\to F_b$ and
$j:G\to C$. By [def-trf-fixed-scheme],
$F_b=D\times_{Y\times_sY,\Delta_Y}Y$, so a $T$-point of $G$ is a pair
$(t,y)$ of $t\in C(T)$ and $y\in Y(T)$ with $b(g(t))=(y,y)$, i.e. with
$fc_1(t)=y=fc_2(t)$. Hence $(c_1,c_2)\circ j$ factors through
$X\times_YX\subset X\times_sX$, giving a morphism $\lambda:G\to X\times_YX$.
The morphism $X\times_YX\to X\times_sX$ is a monomorphism (it is the base
change of the monomorphism $\Delta_Y$). Therefore a $T$-point of
$G\times_{X\times_YX,\lambda,\Delta_{X/Y}}X$ is a pair $((t,y),x)$ with
$(c_1t,c_2t)=(x,x)$, and then $y=fx$ is determined; that is, exactly a
pair $(t,x)$ with $c(t)=\Delta_X(x)$, which is a $T$-point of
$F_c=C\times_{X\times_sX,c,\Delta_X}X$. These identifications are natural
in $T$, so

$$
F_c\cong G\times_{X\times_YX,\Delta_{X/Y}}X,
$$

and the first projection $\kappa:F_c\to G$, $\kappa=(i_c,f d_c)$, is the
base change of $\Delta_{X/Y}$. Since $\pi\kappa=(g i_c,fd_c)$ as a map to
$D\times_{Y\times_sY}Y$, the identities $i_bh=gi_c$, $d_bh=fd_c$ of
[def-trf-coefficient-pushforward] give $\pi\kappa=h$. This is (1),
except for the closed immersion claim.

The proper $f$ is separated, so $\Delta_{X/Y}$ is a closed immersion
([def-weil-scheme-morphism-properties]), and so is its base change
$\kappa$. Closed immersions are proper
([lem-weil-pbc-closed-immersion-proper]); $\pi$ is proper as a base change
of the proper $g$, and $h=\pi\kappa$ is proper as a composite
([lem-kun-proper-stability]). Finally
$q=(f\times\operatorname{id}_Y)\circ(\operatorname{id}_X\times f)$ is a
composite of base changes of $f$, hence proper by
[lem-kun-proper-stability]. This proves (2). The last assertion is the
definition of [def-trf-borel-moore-pushforward] applied to the proper $h$,
$T=F_c$, $T'=F_b$ and $\alpha=\operatorname{Tr}_c(u)$.
