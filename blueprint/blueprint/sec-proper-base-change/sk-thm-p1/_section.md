+++
id = "sk-thm-p1"
kind = "section"
title = "Curve calculations $\\Rightarrow$ PBC($\\Pone$)"
order = 1107
lean = ["AlgebraicGeometry.Etale.hasTorsionBaseChange_projectiveLine"]
uses = ["sk-def-br", "sk-def-conv", "sk-def-ia", "sk-def-pbc", "sk-thm-curveestimate", "sk-thm-iff"]
+++
*Theorem (sketch).*

For every scheme $S$, the projection $\Pone_S\to S$ satisfies
$\mathrm{PBC}$.

## Proof

It suffices ([sk-thm-iff]) to prove $\mathrm{IA}_r$ for the
projection, i.e. the vanishings of [sk-def-ia]. The proof depends
on the *curve calculations*, which we now exhibit.

*(i) The curve calculations.* For $C$ separated of finite type
over an algebraically closed $k$ with $\dim C\le1$ and $F$ torsion,
they are the eight assertions on
$(C_1)\ H^q(C_{\Et},F)=0\ (q>2);$  
$(C_2)\ C\ \text{affine}\ \Rightarrow\ H^q=0\ (q>1);$  
$(C_3)\ \operatorname{char}k=p,\ F\ p\text{-primary}\ \Rightarrow\ H^q=0\ (q>1);$  
$(C_4)\ F\ \text{constructible, prime to }p\ \Rightarrow\ H^q(C,F)\ \text{finite};$  
$(C_5)\ C\ \text{proper},\ F\ \text{constructible}\ \Rightarrow\ H^q(C,F)\ \text{finite};$  
$(C_6)\ k\subset k'\ \text{algebraically closed},\ F\ \text{prime to }p \Rightarrow\ H^q(C,F)\cong H^q(C_{k'},F);$  
$(C_7)\ C\ \text{proper}\ \Rightarrow\ H^q(C,F)\cong H^q(C_{k'},F) \text{ for all torsion }F;$  
$(C_8)\ a:U\hookrightarrow C\ \text{open}\ \Rightarrow\ a^*:H^2(C,F)\twoheadrightarrow H^2(U,a^{-1}F).$
(**Uses Thm [sk-thm-curveestimate]**) For the constant sheaf
$\Fq=\Z/n$ of order $n$ prime to $\operatorname{char}k$ on a smooth
proper connected curve $C$ of genus $g$ these are explicit
computations (the ``Kummer route'': a primitive $n$-th root of unity
identifies $\Z/n\simeq\mu_n$, and the Kummer sequence reads $H^1$ and
$H^2$ off $\Pic(C)$): $H^0(C,\Z/n)=\Z/n$,
$H^1(C,\Z/n)=\Pic(C)[n]\simeq(\Z/n)^{2g}$,
$H^2(C,\Z/n)=\Pic(C)/n\simeq\Z/n$ (via the degree), and
$H^q(C,\Z/n)=0$ for $q\ge3$; this is [sk-thm-curveestimate]. For
an affine open $j:U\hookrightarrow C$ one has $H^q(U,\Z/n)=0$ for
$q\ge2$ (the étale cohomological dimension of an *affine*
curve is $1$; that of the proper $C$ is $2$), and $H^q(C,j_!\Z/n)=0$
for $q\ge3$ with $H^2(C,j_!\Z/n)\to H^2(C,\Z/n)$ surjective (its
cokernel injects into $H^2$ of the finite set $C\setminus U$, which
is $0$); these are $(C_2)$ and $(C_8)$ for the constant sheaf. In
characteristic $p$ the analogues for $\Fp$ come from the
Artin–Schreier sequence
$0\to\Fp\to\mathcal O_C\xrightarrow{F-1}\mathcal O_C\to0$:
$H^0(C,\Fp)=\Fp$, $H^1(C,\Fp)=\ker(F-1\mid H^1(C,\mathcal O_C))$ is
finite of $\Fp$-dimension the $p$-rank of $C$ (at most $g$, not
$2g$), $H^2(C,\Fp)=\operatorname{coker}(F-1\mid H^1(C,\mathcal O_C))=0$
($F-1$ is surjective on a finite-dimensional vector space over the
algebraically closed $k$), and $H^q(C,\Fp)=0$ for $q\ge3$; on an
affine $U$ one has $H^q(U,\Fp)=0$ for $q\ge2$ because $\mathcal O_U$
has no higher cohomology.  
From these,
by finiteness of the normalization, constructible and dense-open
reduction
($0\to j_!j^{-1}F\to F\to i_*i^{-1}F\to0$), locally constant
reduction (finite $r$-group filtration + trace splitting) and
dévissage, $(C_1)$–$(C_8)$ hold for every torsion $F$ and every
such $C$. In particular $(C_6)$/$(C_7)$ give the *invariance*
$H^q(C,F)\cong H^q(C_{k'},F)$ under algebraically closed extension
of the base field, and hence — passing to algebraic closures and
using that universal homeomorphisms do not change the étale site
— under *separably closed* extension $k\subset k'$.

*(ii) Strictly henselian base.* For $A$ strictly henselian
with closed point $s$, the degree-zero comparison
$\Gamma(Z,F)\cong\Gamma(Z_s,F|_{Z_s})$ ($Z$ proper over $A$; Stein's
connectedness), applied through the Mayer–Vietoris sequence to the
two affine opens of $\Pone_A$, kills $H^q$ of an injective for
$q\ge2$; the remaining class in $H^1$ is killed by the
constructible/finite-étale machinery (Gabber's affine comparison +
torsor lifting over a proper henselian pair). Hence
$H^q(\Pone_A,F)\cong H^q(\Pone_s,F|)$ for every torsion $F$. (This
comparison is where the curve calculations of (i) enter for the
constant sheaf on the closed fibre $\Pone_s$.)

*(iii) Arbitrary $S$.* The stalk of the exchange morphism at a
geometric point $\bar t\to T$ (over $\bar s\to S$) is the canonical
pullback $H^q(\Pone_{\kappa(\bar s)},F)\to H^q(\Pone_{\kappa(\bar t)},F)$ between separably closed fields, an
isomorphism by the invariance obtained in (i) (the curve
calculations). So the exchange map is an isomorphism at every
geometric stalk: $\mathrm{IA}_r$ holds for the projection (geometric
stalks are conservative), and [sk-thm-iff] converts it into
$\mathrm{PBC}$.

Uses: [sk-def-conv], [sk-def-ia], [sk-def-pbc], [sk-thm-curveestimate], [sk-thm-iff]
