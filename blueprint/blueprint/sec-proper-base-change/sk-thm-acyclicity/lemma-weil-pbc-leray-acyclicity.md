+++
id = "lemma-weil-pbc-leray-acyclicity"
kind = "lemma"
title = "Leray acyclicity criterion"
order = 1066
uses = ["def-sp-acyclic", "def-sp-injective-resolutions", "def-sp-kinjective-bridge", "def-sp-left-exact-additive", "def-weil-pbc-direct-image", "def-weil-pbc-injective-acyclicity-property", "def-weil-pbc-kinjective-resolutions", "lem-sp-derived-well-defined", "lem-sp-kinjective-computes", "thm-sp-if-e1"]
+++
Let $v:\mathcal A\to\mathcal B$ be a left exact additive functor
[def-sp-left-exact-additive] between abelian categories with enough
injectives, with right derived functors $R^qv$.

1. Injective objects of $\mathcal A$ are $v$-acyclic [def-sp-acyclic].
2. **(Acyclicity criterion.)** If $F\to I^\bullet$ is a resolution of an
   object $F\in\mathcal A$ by $v$-acyclic objects (i.e. $I^m=0$ for $m<0$,
   the augmented complex $0\to F\to I^0\to I^1\to\cdots$ is exact, and
   $R^qvI^m=0$ for $q>0$), then the natural map is an isomorphism

   $$
    \mathcal H^q(vI^\bullet)\xrightarrow{\ \sim\ }R^qvF\qquad(q\geq0):
   $$

   the cohomology of a termwise-acyclic resolution computes the derived
   functor. Here the natural map is the one induced by any morphism of
   complexes $I^\bullet\to J^\bullet$ over $\mathrm{id}_F$ into an injective
   resolution [def-sp-injective-resolutions] $F\to J^\bullet$.
3. **(Complexes.)** If moreover $\mathcal A$ is Grothendieck abelian, so that
   $Rv$ is defined on $\operatorname{Ch}^+(\mathcal A)$ by
   [def-sp-kinjective-bridge], and $K\to I^\bullet$ is a quasi-isomorphism
   from a bounded-below complex $K$ to a bounded-below complex $I^\bullet$ of
   $v$-acyclic objects, then the natural map
   $\mathcal H^q(vI^\bullet)\to R^qvK$ is an isomorphism for every $q$.

In particular, for the etale direct image $v=f'_*$ [def-weil-pbc-direct-image]
on sheaves of $\mathbf F_\ell$-modules: a (bounded-below) complex $I^\bullet$
of $f'_*$-acyclic sheaves quasi-isomorphic to $K$ satisfies
$\mathcal H^q(f'_*I^\bullet)\cong R^qf'_*K$, computed with the K-injective
resolutions of [def-weil-pbc-kinjective-resolutions]. This is the form in
which the injective-acyclicity property [def-weil-pbc-injective-acyclicity-property]
is consumed: under $\mathrm{IA}(f)$ the sheaves $g'^{-1}I^m$ of an injective
resolution $E\to I^\bullet$ are $f'_*$-acyclic, so $f'_*g'^{-1}I^\bullet$
computes $Rf'_*g'^{-1}E$.

## Proof

*Step 0: the long exact sequence.* Let $0\to A\to B\to C\to0$ be exact in
$\mathcal A$. Choose injective resolutions $A\to I_A^\bullet$ and
$C\to I_C^\bullet$. By the horseshoe construction (extend $A\to I_A^0$ to
$B\to I_A^0$ using injectivity of $I_A^0$, and inductively in each degree)
$I_A^\bullet\oplus I_C^\bullet$ carries a differential making it an injective
resolution of $B$ and making
$0\to I_A^\bullet\to I_A^\bullet\oplus I_C^\bullet\to I_C^\bullet\to0$ a
short exact sequence of complexes that is split in each degree. The additive
functor $v$ preserves termwise split exact sequences, so
$0\to vI_A^\bullet\to v(I_A^\bullet\oplus I_C^\bullet)\to vI_C^\bullet\to0$
is a short exact sequence of complexes in $\mathcal B$, and its long exact
cohomology sequence is, by the definition of $R^qv$ in
[def-sp-left-exact-additive] and its independence of the resolutions
[lem-sp-derived-well-defined],

$$
 0\to vA\to vB\to vC\to R^1vA\to R^1vB\to R^1vC\to R^2vA\to\cdots.
$$

*Step 1: item 1.* If $I$ is injective, $I\to I[0]$ is an injective resolution,
so $R^qvI=\mathcal H^q(vI[0])=0$ for $q>0$.

*Step 2: exact complexes of acyclics.* Let $C^\bullet$ be an exact complex in
$\mathcal A$ with $C^m=0$ for $m<m_0$ and every $C^m$ $v$-acyclic. We claim
$vC^\bullet$ is exact. Put $Z^m=\ker(C^m\to C^{m+1})$, so $Z^m=0$ for
$m\leq m_0$ (exactness at $C^{m_0}$, whose predecessor is $0$) and, by
exactness, $0\to Z^m\to C^m\to Z^{m+1}\to0$ is exact for every $m$. Their
long exact sequences (Step 0) and $R^qvC^m=0$ for $q>0$ give
$R^qvZ^{m+1}\cong R^{q+1}vZ^m$ for $q\geq1$ and an exact sequence
$vC^m\to vZ^{m+1}\to R^1vZ^m\to0$. By induction on $m$, starting from
$Z^{m_0}=0$, every $Z^m$ is $v$-acyclic: if $Z^m$ is, then
$R^qvZ^{m+1}\cong R^{q+1}vZ^m=0$ for $q\geq1$. Hence every sequence
$0\to vZ^m\to vC^m\to vZ^{m+1}\to0$ is exact. Since $v$ is left exact and
$Z^{m+1}\to C^{m+1}$ is a monomorphism, $vZ^{m+1}\to vC^{m+1}$ is a
monomorphism, so $vZ^m=\ker(vC^m\to vC^{m+1})$ and the image of
$vC^{m-1}\to vC^m$ is the image of $vC^{m-1}\to vZ^m$, which is all of
$vZ^m$. Thus $vC^\bullet$ is exact in every degree.

*Step 3: item 2.* Let $F\to J^\bullet$ be an injective resolution. Because the
augmented complex of $I^\bullet$ is exact and the $J^m$ are injective, the
identity of $F$ extends to a morphism of complexes
$\varphi:I^\bullet\to J^\bullet$, unique up to homotopy (the comparison
argument of [lem-sp-derived-well-defined], Step 2, which uses only exactness
of the source and injectivity of the target). Its cone
$C^\bullet=\operatorname{cone}(\varphi)$, with $C^m=I^{m+1}\oplus J^m$, is
bounded below, and it is exact because $\varphi$ is a quasi-isomorphism (both
complexes have cohomology $F$ in degree $0$ and $0$ elsewhere, compatibly with
the augmentations). Its terms are $v$-acyclic: the $I^{m+1}$ by hypothesis,
the $J^m$ by item 1, and $R^qv$ commutes with finite direct sums, $v$ being
additive. By Step 2, $vC^\bullet$ is exact. Since $v$ is additive,
$vC^\bullet=\operatorname{cone}(v\varphi)$, so $v\varphi:vI^\bullet\to
vJ^\bullet$ is a quasi-isomorphism and

$$
 \mathcal H^q(vI^\bullet)\xrightarrow{\ \sim\ }\mathcal H^q(vJ^\bullet)
 =R^qvF .
$$

The map does not depend on $\varphi$ (homotopic maps induce the same map on
cohomology after applying the additive functor $v$) nor, by
[lem-sp-derived-well-defined], on $J^\bullet$. Unwinding Step 2 for the
single resolution $I^\bullet$ recovers the dimension-shifting description:
$\mathcal H^q(vI^\bullet)=\operatorname{coker}(vI^{q-1}\to vZ^q)\cong
R^1vZ^{q-1}\cong R^2vZ^{q-2}\cong\cdots\cong R^qvZ^0=R^qvF$ for $q\geq1$, and
$\mathcal H^0(vI^\bullet)=vZ^0=vF$; no spectral sequence is needed.

*Step 4: item 3.* Choose a Cartan--Eilenberg resolution
$I^\bullet\to\operatorname{Tot}(A^{\bullet,\bullet})=:J^\bullet$ of the
bounded-below complex $I^\bullet$, as in [thm-sp-if-e1]: $J^\bullet$ is a
bounded-below complex of injectives and $I^\bullet\to J^\bullet$ is a
quasi-isomorphism, so by part (2) of [lem-sp-kinjective-computes] the
composite $K\to I^\bullet\to J^\bullet$ is a K-injective resolution of $K$ and
$RvK=vJ^\bullet$ [def-sp-kinjective-bridge]. The cone of
$I^\bullet\to J^\bullet$ is a bounded-below exact complex of $v$-acyclic
objects (item 1 for the $J^m$), so by Step 2 and additivity of $v$ the map
$vI^\bullet\to vJ^\bullet$ is a quasi-isomorphism, i.e.
$\mathcal H^q(vI^\bullet)\xrightarrow{\sim}R^qvK$. By part (1) of
[lem-sp-kinjective-computes] this is independent of the chosen K-injective
resolution.

The sheaf statement is items 2 and 3 for $v=f'_*$ on the Grothendieck abelian
category of sheaves of $\mathbf F_\ell$-modules on the etale site, where
$R^qf'_*$ are the higher direct images of [def-weil-pbc-direct-image] and the
K-injective resolutions are those of [def-weil-pbc-kinjective-resolutions].
(*Compare Stacks Project Lemmas 21.14.5/21.14.6 (Tags
[0732](https://stacks.math.columbia.edu/tag/0732)/[0733](https://stacks.math.columbia.edu/tag/0733))
for the topoi form, and Lemmas 20.13.4/20.13.8 (Tags
[01F2](https://stacks.math.columbia.edu/tag/01F2)/[01F6](https://stacks.math.columbia.edu/tag/01F6))
for ringed spaces.*)
