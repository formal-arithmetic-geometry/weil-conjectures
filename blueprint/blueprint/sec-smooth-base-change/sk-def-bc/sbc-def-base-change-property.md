+++
id = "sbc-def-base-change-property"
kind = "definition"
title = "The recorded base-change property $BC(f,n,q)$"
order = 1368
uses = ["def-weil-pbc-scheme-conventions", "sbc-def-base-change-map", "sbc-def-base-change-square", "sbc-def-coefficient-conventions"]
+++
Let $f:X\to S$ be a
morphism of schemes (conventions of [def-weil-pbc-scheme-conventions]),
let $n\geq1$ be an integer invertible on $S$, let $q\geq0$, and put
$\Lambda=\mathbf Z/n\mathbf Z$ (a coefficient ring as in
[sbc-def-coefficient-conventions]).
We say that *$BC(f,n,q)$ holds*, or that *the recorded
base-change property holds for $f$, $n$ and $q$*, if for every
base-change square of
[sbc-def-base-change-square] whose horizontal side $g:T\to S$ is
quasi-compact and
quasi-separated, and every abelian sheaf $\mathcal F$ on $T_{\Et}$
annihilated by $n$ (that is, every sheaf of
$\mathbf Z/n\mathbf Z$-modules on $T_{\Et}$), the base-change map
of [sbc-def-base-change-map] in degree $q$,

$$
\operatorname{BC}^q_{f,g}(\mathcal F):
f^{-1}R^qg_*\mathcal F\longrightarrow R^qh_*e^{-1}\mathcal F,
$$

is an isomorphism. This is a condition in the single degree $q$ only;
the cumulative form used in the induction on $q$ is
"$BC(f,n,q')$ for all $q'\leq q$", which says that the derived
base-change map $\operatorname{BC}_{f,g}(\mathcal F)$ of
[sbc-def-base-change-map] is an isomorphism on $q'$-th cohomology
sheaves for all $q'\leq q$. We say that *$BC(f,n,q)$ holds
universally* if $BC(f',n,q)$ holds for every base change
$f':X'=X\times_SS'\to S'$ of $f$ along every morphism of schemes
$S'\to S$ (here $n$ is invertible on $S'$ because it is invertible on
$S$); this is the form in which the property is used, since the
arguments below apply it to base changes of $f$, and to horizontal
sides $T\to S'$ whose composite with $S'\to S$ need not be
quasi-compact and quasi-separated. We write $\mathrm{UBC}^{\le q}(f,n)$
for the cumulative universal property "$BC(f,n,q')$ holds universally
for all $q'\leq q$"; it is the property $BC(f,n,q)$ of the Stacks
Project, Tag 0F02, and it is the hypothesis of the reduction lemmas of
this chapter. The fixed-base property does not imply the universal one:
there are flat, finitely presented $f$ with geometrically connected
fibres for which $BC(f,n,0)$ holds but $BC(f_{\mathbf A^1_S},n,0)$
fails, so the quantifier over $S'\to S$ cannot be dropped from the
hypotheses. The smooth-base-change theorem of
this chapter is the assertion $BC(f,n,q)$ for every $q$ and every
smooth $f$; since smoothness is stable under base change, it gives
$BC(f,n,q)$ universally for every smooth $f$ and every $q$.
