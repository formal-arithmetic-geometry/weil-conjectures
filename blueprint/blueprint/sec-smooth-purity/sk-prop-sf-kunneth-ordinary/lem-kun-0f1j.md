+++
id = "lem-kun-0f1j"
kind = "lemma"
title = "Base change for pushforward tensored with a bounded-below complex of finite tor amplitude"
order = 1778
uses = ["def-kun-derived-tensor", "def-kun-tor-amplitude", "def-kun-truncations", "def-kun-unbounded-exchange", "def-weil-pbc-direct-image", "def-weil-pbc-inverse-image", "lem-kun-03sa", "lem-kun-095r", "lem-kun-0f0g", "lem-kun-0f1i", "lem-kun-0f1m", "lem-kun-bc-base-change", "lem-kun-change-of-rings-tensor", "lem-kun-constant-constructible", "lem-kun-derived-tensor-t-est", "lem-kun-derived-tensor-triangulated", "lem-kun-leray-finite", "lem-kun-proj-formula-natural", "lem-kun-stalk-faithful-derived", "lem-kun-tensor-t-est", "lem-kun-zn-sheaf-invertible-orders", "lemma-weil-pbc-constructible-finite-pushforward", "lemma-weil-pbc-direct-image-filtered-colimit", "lemma-weil-pbc-finite-direct-image-exact", "lemma-weil-pbc-finite-exchange", "thm-constructible-serre"]
+++
Let $K$ be a field and $n\ge1$ an integer invertible in $K$.
Consider a commutative diagram

$$
\begin{array}{ccccc}
X&\xleftarrow{\;p\;}&X'&\xleftarrow{\;h\;}&Y\\
\Big\downarrow{}&&\Big\downarrow{\scriptstyle f'}&&\Big\downarrow{\scriptstyle e}\\
\Spec(K)&\longleftarrow&S'&\xleftarrow{\;g\;}&T
\end{array}
$$

of schemes with $X'=X\times_{\Spec(K)}S'$ and
$Y=X'\times_{S'}T$ and with $g$ quasi-compact and
quasi-separated. The canonical map

$$
p^{-1}E\kunotimes{\kunZn}(f')^{-1}Rg_*F
\longrightarrow
Rh_*\bigl(h^{-1}p^{-1}E\kunotimes{\kunZn}e^{-1}F\bigr)
$$

(adjoint to the map
$h^{-1}p^{-1}E\kunotimes{\kunZn}e^{-1}g^{-1}Rg_*F\to h^{-1}p^{-1}E\kunotimes{\kunZn}e^{-1}F$
induced by the counit of [def-weil-pbc-inverse-image]) is an
isomorphism for every $E\in\Dplus(X_{\Et},\kunZn)$ of
tor amplitude in $[a,\infty)$ for
some $a\in\mathbf Z$ and every $F\in\Dplus(T_{\Et},\kunZn)$.
(*Source:* Stacks Project, Tag
[0F1J](https://stacks.math.columbia.edu/tag/0F1J).)

## Proof

*Reduction to a single flat module.* By [lem-kun-0f1m]
(the tor-amplitude criterion of [def-kun-tor-amplitude]) we may
represent $E$ by a bounded-below K-flat complex
$\mathcal E^\bullet$ of flat $\kunZn$-module sheaves, with
$\mathcal E^i=0$ for $i<a$. Choose an integer $b$ such that
$\mathcal H^i(F)=0$ for $i<b$. Choose a large integer $N$ and
consider the short exact sequence

$$
0\to\sigma_{\ge N+1}\mathcal E^\bullet\to\mathcal E^\bullet\to
\sigma_{\le N}\mathcal E^\bullet\to0
$$

of stupid truncations ([def-kun-truncations]). This produces a
distinguished triangle $E''\to E\to E'\to E''[1]$ in
$D(X_{\Et},\kunZn)$. For fixed $F$, both sides of the arrow in
the statement of the lemma are triangulated functors in $E$
([lem-kun-derived-tensor-triangulated],
[def-kun-derived-tensor],
[def-weil-pbc-direct-image]). By
[lem-kun-derived-tensor-t-est] (and
[lem-kun-tensor-t-est] for the right hand side), the objects

$$
p^{-1}E''\kunotimes{\kunZn}(f')^{-1}Rg_*F
\quad\text{and}\quad
Rh_*\bigl(h^{-1}p^{-1}E''\kunotimes{\kunZn}e^{-1}F\bigr)
$$

are sitting in degrees $\ge N+b$. Hence, if we can prove the lemma
for the object $E'$, then comparing the two distinguished triangles
(five lemma on the long exact cohomology sequences) shows that the
lemma holds for $E$ in degrees $\le N+b$, and letting
$N\to\infty$ we conclude. Thus we may assume $E$ is represented
by a bounded complex of flat $\kunZn$-module sheaves. Doing another
argument of the same nature (decomposing the bounded complex through
its stupid truncation triangles, using that both sides are
triangulated functors in $E$), we may assume $E$ is given by a
single flat $\kunZn$-module sheaf $\mathcal E$.

*Reduction of $F$.* Next, we use the same arguments for the
variable $F$ to reduce to the case where $F$ is given by a single
sheaf of $\kunZn$-modules $\mathcal F$: truncate $F$ with
$\tau_{\le M}$ ([def-kun-truncations]) and compare degrees,
then represent the bounded complex $\tau_{\le M}F$ by a bounded
complex and split it into its single sheaves through stupid
truncation triangles.

*Reduction to prime torsion.* Say $\mathcal F$ is annihilated
by an integer $m\mid n$. If $\ell$ is a prime number dividing
$m$ and $m>\ell$, then we can look at the short exact sequence
$0\to\mathcal F[\ell]\to\mathcal F\to\mathcal F/\mathcal F[\ell]\to0$
and reduce to smaller $m$ (both sides of the asserted map are
triangulated functors in $F$, and $\mathcal F[\ell]$ is
annihilated by $\ell$ while $\mathcal F/\mathcal F[\ell]$ is
annihilated by $m/\ell$). This finally reduces us to the case
where $\mathcal F$ is annihilated by a prime $\ell\mid n$,
i.e. $\mathcal F$ is a sheaf of $\kunFl$-vector spaces. In this
case observe that

$$
p^{-1}\mathcal E\kunotimes{\kunZn}(f')^{-1}Rg_*\mathcal F
\;\cong\;
p^{-1}(\mathcal E/\ell\mathcal E)\kunotimes{\kunFl}
(f')^{-1}Rg_*\mathcal F
$$

by the flatness of $\mathcal E$ and
[lem-kun-change-of-rings-tensor], and similarly for the other
term. This reduces us to the case where we work with sheaves of
$\kunFl$-vector spaces, which we now discuss.

*The $\kunFl$-vector space case.* Assume $\ell$ is a prime
invertible in $K$ and $\mathcal E$, $\mathcal F$ are sheaves of
$\kunFl$-vector spaces on $X_{\Et}$ and $T_{\Et}$. We want to
show that

$$
p^{-1}\mathcal E\kunotimes{\kunFl}(f')^{-1}R^qg_*\mathcal F
\longrightarrow
R^qh_*\bigl(h^{-1}p^{-1}\mathcal E\kunotimes{\kunFl}e^{-1}\mathcal F\bigr)
$$

is an isomorphism for every $q\ge0$ (the map induced on $\mathcal H^q$ by the asserted map, see [def-kun-unbounded-exchange] and
[lem-kun-bc-base-change]; the tensor product is underived
because $\kunFl$-vector spaces are flat).

This question is local on $X$ ([lem-kun-stalk-faithful-derived]),
hence we may assume $X$ is affine. We can write
$\mathcal E$ as a filtered colimit of constructible sheaves of
$\kunFl$-vector spaces on $X_{\Et}$
([lem-kun-03sa], with the Noetherian ring
$\Lambda=\kunFl$). Since tensor products commute with filtered
colimits and since higher direct images do too
([lemma-weil-pbc-direct-image-filtered-colimit]), we may assume
$\mathcal E$ is a constructible sheaf of $\kunFl$-vector spaces
on $X_{\Et}$. Then [lemma-weil-pbc-constructible-finite-pushforward],
with $\Lambda=\kunFl$, gives an integer $m$, finite and finitely
presented morphisms $\pi_i:X_i\to X$, and a monomorphism

$$
\mathcal E\longrightarrow P:=\bigoplus_{i=1}^m\pi_{i,*}\underline{\kunFl}.
$$

Each summand is constructible by
[lem-kun-095r] and [lem-kun-constant-constructible]; hence
$P$ and the cokernel of $\mathcal E\to P$ are constructible by
[thm-constructible-serre]. We first prove the assertion for each
$\pi_{i,*}\underline{\kunFl}$; finite additivity gives it for
$P$, after which the dimension-shifting argument recovers the
assertion for $\mathcal E$.

To prove this case we extend the diagram of the lemma to

$$
\begin{array}{ccccc}
X_i&\longleftarrow&X'_i&\longleftarrow&Y_i\\
\Big\uparrow{\scriptstyle \pi_i}&&\Big\uparrow{\scriptstyle \pi'_i}&&\Big\uparrow{\scriptstyle \rho_i}\\
X&\longleftarrow&X'&\longleftarrow&Y\\
\Big\downarrow{}&&\Big\downarrow{\scriptstyle f'}&&\Big\downarrow{\scriptstyle e}\\
\Spec(K)&\longleftarrow&S'&\xleftarrow{\;g\;}&T
\end{array}
$$

with all squares cartesian (so $X'_i=X_i\times_XX'$ and
$Y_i=X'_i\times_{X'}Y$; here $\rho_i:Y_i\to Y$ and the unlabelled
maps are the projections). In the equations below we use that
$R\pi_{i,*}=\pi_{i,*}$ and similarly for $\pi'_i$ and $\rho_i$
(finite morphisms, [lemma-weil-pbc-finite-direct-image-exact]);
we use the Leray spectral sequence through the finite morphisms
([lem-kun-leray-finite]); we use
[lemma-weil-pbc-finite-exchange] and [lem-kun-0f0g] (the
projection formula, almost trivial for finite morphisms) for
$\pi_i$, $\pi'_i$, $\rho_i$. Doing so we see that

$$
\begin{aligned}
&p^{-1}\pi_{i,*}\underline{\kunFl}\kunotimes{\kunFl}
(f')^{-1}R^qg_*\mathcal F\\
&\qquad=\pi'_{i,*}\underline{\kunFl}\kunotimes{\kunFl}
(f')^{-1}R^qg_*\mathcal F\bigr)\qquad(\text{\Cref{lemma-weil-pbc-finite-exchange}})\\
&\qquad=\pi'_{i,*}\bigl((\pi'_i)^{-1}(f')^{-1}R^qg_*\mathcal F\bigr)
\qquad(\text{\Cref{lem-kun-0f0g}}).
\end{aligned}
$$

Similarly,

$$
\begin{aligned}
&R^qh_*\bigl(h^{-1}p^{-1}\pi_{i,*}\underline{\kunFl}
\kunotimes{\kunFl}e^{-1}\mathcal F\bigr)\\
&\qquad=R^qh_*\bigl(\rho_{i,*}\underline{\kunFl}
\kunotimes{\kunFl}e^{-1}\mathcal F\bigr)
\qquad(\text{\Cref{lemma-weil-pbc-finite-exchange}})\\
&\qquad=R^qh_*\bigl(\rho_{i,*}\rho_i^{-1}e^{-1}\mathcal F\bigr)
\qquad(\text{\Cref{lem-kun-0f0g}})\\
&\qquad=\pi'_{i,*}R^qh_{i,*}\rho_i^{-1}e^{-1}\mathcal F
\qquad(\text{\Cref{lem-kun-leray-finite}}).
\end{aligned}
$$

Since
$R^qh_{i,*}\rho_i^{-1}e^{-1}\mathcal F=(\pi'_i)^{-1}(f')^{-1}R^qg_*\mathcal F$
by [lem-kun-0f1i] (applied to the upper square, with base
scheme $X_i$ of finite type over $K$ and the sheaf
$\mathcal F$, a sheaf of $\kunFl$-vector spaces whose stalks are
$\ell$-torsion with $\ell\mid n$
invertible in $K$, hence of orders invertible in $K$ by
[lem-kun-zn-sheaf-invertible-orders]), we conclude by
[lem-kun-proj-formula-natural], which identifies the asserted
map with the identity under the displayed isomorphisms.
