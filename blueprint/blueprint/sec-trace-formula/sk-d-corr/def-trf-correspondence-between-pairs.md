+++
id = "def-trf-correspondence-between-pairs"
kind = "definition"
title = "Correspondences between pairs and opposite correspondences"
order = 2276
uses = ["def-trf-admissibility", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-fixed-scheme", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-scheme-morphism-properties"]
+++
Fix the global finite-field datum
and the coefficient
conventions, $A=A_{E,n}$, put $s=\Spec k$, and let $X,Y,C,D$ be
separated finite-type $k$-schemes, with $K\in D^b_{ctf}(X,A)$ and
$L\in D^b_{ctf}(Y,A)$. Products are taken over $s$.

1. A *correspondence from $(X,K)$ to $(Y,L)$* consists of a morphism
$$
c=(c_1,c_2):C\longrightarrow Y\times_sX
$$
and a morphism
$$
u:Lc_2^*K\longrightarrow Rc_1^!L
$$
in $D(C,A)$, where $Lc_2^*$ is the derived pullback and $Rc_1^!$ the
exceptional inverse image of [def-trf-admissibility]. The
ordinary-pullback leg is $c_2$ and the exceptional leg is $c_1$; the
correspondence is *admissible* if $c_1$ and every base change of $c_1$
used below are exceptionally admissible at $A$. An
*endocorrespondence* of $(X,K)$ is the case $Y=X$, $L=K$; it is exactly
a cohomological correspondence of [def-trf-correspondence].
1. An *opposite correspondence* is a correspondence from $(Y,L)$ to
$(X,K)$, i.e. a morphism $d=(d_1,d_2):D\to X\times_sY$ together with
$v:Ld_2^*L\to Rd_1^!K$ in $D(D,A)$.
1. For such a pair put
$$
Z=Y\times_sX,\qquad \bar d=\tau d:D\longrightarrow Z,\qquad
E(C,D)=C\times_{Z,c,\bar d}D,
$$
where $\tau:X\times_sY\xrightarrow{\sim}Y\times_sX$ exchanges the
factors, so that $\bar d=(d_2,d_1)$. Write $p_1:Z\to Y$ and
$p_2:Z\to X$ for the two projections, so that $c_1=p_1c$ and
$c_2=p_2c$.

All supports $C,D,E(C,D)$ and all structure maps $c,d,\bar d$ and the
projections of $E(C,D)$ remain specified data; nothing is identified
up to non-specified isomorphism.

For an endocorrespondence $c$ of $(X,K)$ and the identity
correspondence $d=\Delta_X:X\to X\times_sX$, $v=1_K$ (here $d_1=d_2=\operatorname{id}_X$, so $Rd_1^!K=K=Ld_2^*K$), one has
$\bar d=\tau\Delta_X=\Delta_X$, hence
$E(C,X)=C\times_{X\times_sX,c,\Delta_X}X=\operatorname{Fix}(c)$ is the
fixed scheme of [def-trf-fixed-scheme].
