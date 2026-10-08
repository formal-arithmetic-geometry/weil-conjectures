+++
id = "sk-prop-an"
kind = "section"
title = "$\\Aaf^1\\Rightarrow\\Aaf^n$: the model purity"
order = 1962
uses = ["sk-def-purity-conv", "sk-lem-sf-mate", "sk-prop-a1", "sk-prop-a1-inv", "sk-prop-a1-kummer", "sk-prop-cd", "sk-prop-h2", "sk-prop-sf-cbc", "sk-prop-sf-open-closed-triangle", "sk-thm-properbasechange"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpaceZero"]
+++
*Proposition (sketch).*

In the conventions of [sk-def-purity-conv], let $B$ be separated finite
type, $\pi=p_c:\Aaf^c_B\to B$ the projection and $z:B\hookrightarrow\Aaf^c_B$
the zero section.

- **(i)** *The $Rz^{!}$-form: the Thom class.*

$$
Rz^{!}\Lambda_{\Aaf^c_B}(c)[2c]\ \cong\ \Lambda_B,
$$

i.e. $Rz^{!}\Lambda_{\Aaf^c_B}\cong\Lambda_B(-c)[-2c]$, by a canonical
base-change compatible isomorphism whose generator is the fundamental class
of the zero section, the cup product with supports
$\partial\kappa(t_1)\cup\cdots\cup\partial\kappa(t_c)$ of the Kummer
boundaries of the coordinates. More generally, for a vector bundle
$\pi:E\to Z$ of rank $c$ with zero section $z$ there is a *Thom class*

$$
\mathrm{th}_E:\ \Lambda_Z\ \xrightarrow{\ \sim\ }\ Rz^{!}\Lambda_E(c)[2c],
$$

which restricts to the previous one in any étale trivialization of $E$.
- **(ii)** *The $R\pi^{!}$-form: affine-space and vector-bundle
purity.* For every $K\in D^b_{ctf}(B,\Lambda)$ there is a canonical
isomorphism

$$
\gamma_{\pi,K}:\ L\pi^{*}K(c)[2c]\ \xrightarrow{\ \sim\ }\ R\pi^{!}K,
$$

natural in $K$ and compatible with arbitrary base change in $B$; in
particular $\omega_\pi=R\pi^{!}\Lambda_B\cong\Lambda_{\Aaf^c_B}(c)[2c]$.
It is the transpose under $R\pi_!\dashv R\pi^{!}$ of the *integration
map*

$$
R\pi_!L\pi^{*}K(c)[2c]\ \cong\ K\otimes^{\mathbb L}R\pi_!\Lambda_{\Aaf^c_B}(c)[2c]
\ \xrightarrow{\ 1_K\otimes\int_\pi\ }\ K,
$$

where $\int_\pi:R\pi_!\Lambda_{\Aaf^c_B}(c)[2c]\xrightarrow{\sim}\Lambda_B$ is
the affine-space trace of Step 5 below and the first map is the projection
formula. Under $\Aaf^{c+e}_B=\Aaf^c_{\Aaf^e_B}$ it satisfies the composition
law
$\gamma_{p_{c+e},K}=c_{p_e,p_c}^{-1}\circ\gamma_{p_c,Rp_e^{!}K}\circ
Lp_c^{*}(\gamma_{p_e,K})(c)[2c]$, with $c_{g,f}:R(gf)^{!}\cong Rf^{!}Rg^{!}$
the composition isomorphism, and it is symmetric under permutations of the
coordinates (every Koszul sign is $+1$, all shifts being even). More
generally, for a vector bundle $\pi:E\to Z$ of rank $c$ there is a canonical
isomorphism $\gamma_{\pi,K}:L\pi^{*}K(c)[2c]\xrightarrow{\sim}R\pi^{!}K$,
compatible with base change, which is the affine-space one on every étale
trivialization of $E$; in particular $\omega_\pi\cong\Lambda_E(c)[2c]$
(*vector-bundle purity*).
- **(iii)** *Normalization: the two forms agree along the zero
section.* Since $\pi z=\mathrm{id}$, the composition isomorphism gives
$Rz^{!}R\pi^{!}\cong\mathrm{id}$, and for every vector bundle $\pi:E\to Z$
(with $Z=B$ for $E=\Aaf^c_B$) the composite

$$
\Lambda_Z\ \xrightarrow{\ \mathrm{th}_E\ }\ Rz^{!}\Lambda_E(c)[2c]
\ \xrightarrow{\ Rz^{!}(\gamma_{\pi,\Lambda})\ }\ Rz^{!}R\pi^{!}\Lambda_Z
\ \cong\ \Lambda_Z
$$

is the identity. Equivalently, $\int_\pi$ sends the *class of the zero
section* — the image of $\mathrm{th}_E$ under
$H^0(Z,Rz^{!}\Lambda_E(c)[2c])=H^{2c}_{z(Z)}(E,\Lambda(c))\to
H^0(Z,R\pi_!\Lambda_E(c)[2c])$, which for $E=\Aaf^c_B$ is
$\partial\kappa(t_1)\cup\cdots\cup\partial\kappa(t_c)$ — to $1$. Thus (i)
is what (ii) becomes along the zero section, and the generator of (i) is the
normalization of (ii).

Clause (ii) is the model case of [sk-prop-cohsm] (Step 1),
[sk-lem-geometry] (4) and [sk-thm-smooth-purity] (Step 3); clause (iii)
is what [sk-thm-regular] (Step 4) and [sk-cor-trace] use.
(Detailed: cor:pur-affine-space-purity,
prop:pur-affine-space-purity-compatibilities,
cor:pur-vector-bundle-purity for (ii);
cor:pur-affine-space-zero-section-purity, thm:pur-vector-bundle-thom
for (i) and (iii).)

## Proof

Steps 1–4 prove the $Rz^{!}$-form (i); Steps 5–7 prove the $R\pi^{!}$-form
(ii) directly from the affine-line computation, together with the
normalization (iii).

*Step 1: the model case, by iterating the affine line.* Write
$\Aaf^c_B=\Aaf^1_{B'}$ with $B'=\Aaf^{c-1}_B$, let $p':\Aaf^1_{B'}\to B'$ be
the last-coordinate projection with zero section
$s':B'\hookrightarrow\Aaf^1_{B'}$, and let $z_{c-1}:B\hookrightarrow B'$ be
the zero section of $\Aaf^{c-1}_B$, so that $z=s'\circ z_{c-1}$ and, by the
composition law ([sk-lem-sf-mate], for closed immersions),
$Rz^{!}\cong Rz_{c-1}^{!}Rs'^{!}$. No Künneth formula for $Rz^{!}$ of
general constructible inputs is used: the relative identity
$Rz^{!}(K_1\boxtimes_BK_2)\simeq Rs^{!}K_1\otimes^{\mathrm L}Rs^{!}K_2$ is
*false* in general (for $B=\Aaf^1_k$, $K_1=K_2=i_*\Lambda_B$ with $i$ the
graph $x=b$, and $e:\{0\}\hookrightarrow B$, the two sides are
$e_*\Lambda(-1)[-2]$ and $e_*\Lambda(-2)[-4]$); only constant coefficients
enter, and for them the calculation is the following. A twist pulled back
from $B'$ passes through $Rs'^{!}$ (the projection formula for $Rs'_!=Rs'_*$,
transposed; $\Lambda(1)$ is invertible), so with
$\Lambda_{\Aaf^c_B}(c)[2c]=\Lambda_{\Aaf^1_{B'}}(1)[2]\otimes Lp'^{*}\Lambda_{B'}(c-1)[2c-2]$ and [sk-prop-a1] over the base $B'$,

$$
Rs'^{!}\Lambda_{\Aaf^c_B}(c)[2c]\ \cong\
Rs'^{!}\Lambda_{\Aaf^1_{B'}}(1)[2]\otimes\Lambda_{B'}(c-1)[2c-2]
\ \xrightarrow{\ \mathrm{pur}_{s'}^{-1}\otimes1\ }\
\Lambda_{B'}(c-1)[2c-2],
$$

and then, by induction on $c$ (the case $c=1$ being [sk-prop-a1]),
$Rz^{!}\Lambda_{\Aaf^c_B}(c)[2c]\cong Rz_{c-1}^{!}\Lambda_{B'}(c-1)[2c-2] \cong\Lambda_B$. The isomorphism is canonical and compatible with base
change, each step being so ([sk-prop-a1], and the compatibility of the
composition law with base change), and its generator is

$$
\mathrm{th}_c:=Rz_{c-1}^{!}\bigl(\mathrm{pur}_{s'}\otimes1\bigr)\circ
\mathrm{th}_{c-1}:\ \Lambda_B\longrightarrow Rz^{!}\Lambda_{\Aaf^c_B}(c)[2c],
\qquad \mathrm{th}_1=\mathrm{pur}_s,
$$

the iterated Kummer boundary with supports. It is the cup product with
supports $\partial\kappa(t_1)\cup\cdots\cup\partial\kappa(t_c)$ of the
pulled-back rank-one classes $\partial\kappa(t_i)\in H^2_{\{t_i=0\}}$: the
boundary with supports along the last coordinate, applied to a class
supported on $\{t_1=\cdots=t_{c-1}=0\}$, is the cup product with
$\partial\kappa(t_c)$, and the factors commute (all degrees are even).

*Step 2: the sheaf of orientations.* Let $\pi:E\to Z$ have rank $c$ and
choose an étale cover $\{U_\alpha\to Z\}$ trivializing $E$. Formation of
$Rz^{!}$ commutes with the base changes involved, so by Step 1 the complex
$Rz^{!}\Lambda_E(c)[2c]$ restricted to each $U_\alpha$ is concentrated in
degree zero with $\mathcal H^0$ free of rank one. Hence
$\mathcal L_E:=\mathcal H^0\bigl(Rz^{!}\Lambda_E(c)[2c]\bigr)$ is a lisse
rank-one sheaf on $Z$, and giving $\mathrm{th}_E$ amounts to giving a global
section of $\mathcal L_E$ generating every stalk. This is the mechanism
inherited from [sk-prop-a1]: what is glued below are *sections of a
lisse sheaf on $Z_{\Et}$*, for which the sheaf axiom suffices, not objects or
morphisms of $D^b$, for which étale descent is unavailable in the ordinary
derived category.

*Step 3: independence of the frame.* On $U_\alpha$ a frame
$f_1,\dots,f_c$ of the ideal of the zero section gives the section
$\partial\kappa(f_1)\cup\cdots\cup\partial\kappa(f_c)$ of Step 1. Two frames
differ by some $g\in GL_c(\mathcal O(U_\alpha))$, and after refining the cover
$g$ is a product of diagonal, permutation and elementary matrices; the
section is unchanged under each. Diagonal:
$\kappa(uf_i)=\kappa(u)+\kappa(f_i)$ and $\kappa(u)$ extends across the zero
locus, so it dies under the boundary. Permutation: each $\kappa(f_i)$
contributes total degree $2$, so a transposition carries sign $+1$.
Elementary: the family $f(t)$ over $\Aaf^1_{U_\alpha}$ gives a section of a
lisse sheaf on the line, constant along it by [sk-prop-a1-inv] (i), so the
classes at $t=0$ and $t=1$ agree.

*Step 4: gluing.* By Step 3 the local sections of Step 1 agree on
overlaps, so by the sheaf axiom for $\mathcal L_E$ they glue to a unique
global section $\mathrm{th}_E$, generating every stalk. A generating section
of a lisse rank-one sheaf is an isomorphism, which is the assertion. Base-change
compatibility is inherited from [sk-prop-a1].

*Step 5: the $R\pi^{!}$-form for $c=1$ (affine-line purity).* Let
$p:\Aaf^1_Y\to Y$, let $\bar\jmath:\Aaf^1_Y\hookrightarrow\mathbf P^1_Y$ be
the standard compactification, $q:\mathbf P^1_Y\to Y$ its projection and
$\infty:Y\hookrightarrow\mathbf P^1_Y$ the section at infinity.
*(a) The projective line.* On a geometric fibre $\mathbf P^1_k$ the
Kummer sequence gives, exactly as in the proof of [sk-prop-a1-kummer],
$H^0(\mathbf P^1_k,\mu_{\ell^N})=\mu_{\ell^N}(k)$,
$H^1(\mathbf P^1_k,\mu_{\ell^N})=0$ ($\Pic\mathbf P^1_k=\Z$ is torsion free
and $k^\times$ is divisible),
$H^2(\mathbf P^1_k,\mu_{\ell^N})=\Pic(\mathbf P^1_k)/\ell^N\cong\Z/\ell^N$ on
the class of a point ([sk-prop-h2]), and $H^q=0$ for $q\ge3$
([sk-prop-cd]); the dévissage of that proof passes to
$\Lambda(1)$-coefficients. By proper base change
([sk-thm-properbasechange]) this computes $Rq_*$: with
$h=c_1(\mathcal O(1))\in H^2(\mathbf P^1_Y,\Lambda(1))$ the Kummer first Chern
class, which restricts to the class of a point on every fibre,

$$
(1,h):\ \Lambda_Y(1)[2]\oplus\Lambda_Y\ \xrightarrow{\ \sim\ }\ Rq_*\Lambda(1)[2]
$$

is an isomorphism compatible with base change. Let
$t_q:Rq_*\Lambda(1)[2]\to\Lambda_Y$ be the projection onto the second
summand, the *trace*, normalized by $t_q(h)=1$. Since the first summand
$\Lambda_Y(1)[2]$ has no $\mathcal H^0$, $t_q$ is the truncation
$Rq_*\Lambda(1)[2]\to\mathcal H^0=R^2q_*\Lambda(1)\cong\Lambda_Y$ onto the top
cohomology sheaf, the identification being "fibrewise degree" (the class of
a point of a fibre $\mapsto1$); so $t_q$ does not depend on the choice of
$h$, kills the base summand $q^{*}H^2(Y,\Lambda(1))$, and is invariant under
automorphisms of $\mathbf P^1_Y$ over $Y$, which preserve fibrewise degree.
A section $\sigma$ of $q$ has divisor $\sigma(Y)$ of fibrewise degree one,
so its class is $h+q^{*}c$ for some $c\in H^2(Y,\Lambda(1))$ — not
necessarily $h$ itself: for $Y=\mathbf P^1$ the diagonal section has class
$h_{\mathrm{fibre}}+h_{\mathrm{base}}$ — and $t_q$ sends the class of every
section to $1$, the base summand dying under $t_q$.
*(b) The affine-line trace.* Put

$$
\int_p:\ Rp_!\Lambda(1)[2]=Rq_*\bar\jmath_!\Lambda(1)[2]
\longrightarrow Rq_*\Lambda(1)[2]\xrightarrow{\ t_q\ }\Lambda_Y .
$$

The open–closed triangle ([sk-prop-sf-open-closed-triangle]) for
$(\bar\jmath,\infty)$ gives after $Rq_*$ the triangle
$Rp_!\Lambda(1)[2]\to Rq_*\Lambda(1)[2]\to\Lambda_Y(1)[2]\xrightarrow{+1}$,
whose second map is $(1,0)$ in the decomposition of (a) (restriction to
$\infty$ kills $h$, as $\infty^{*}\mathcal O(1)$ is trivial); hence $\int_p$
is an isomorphism, compatible with base change ([sk-prop-sf-cbc]).
*(c) The comparison and its isomorphy.* For $K\in D^b_{ctf}(Y,\Lambda)$
let $\gamma_{p,K}:Lp^{*}K(1)[2]\to Rp^{!}K$ be the transpose under
$Rp_!\dashv Rp^{!}$ of
$Rp_!Lp^{*}K(1)[2]\cong K\otimes^{\mathbb L}Rp_!\Lambda(1)[2]
\xrightarrow{1\otimes\int_p}K$, the first map being the projection formula
$\mathrm{PF}$ of [sk-def-sf-exchanges] (an isomorphism by
[sk-thm-sf-pf-finite]). That it is an isomorphism is the explicit
projective-line adjunction $Rq_*\dashv q^{*}(1)[2]$ (detailed:
thm:amb-p1-adjunction, cor:amb-affine-space-adjunction,
thm:pur-affine-line-purity): its counit is $(1\otimes t_q)\circ\mathrm{PF}$,
its unit $M\to q^{*}Rq_*M(1)[2]$ is induced by the supported class
$c_\Delta:\Delta_*\Lambda\to\Lambda(1)[2]$ of the diagonal divisor
$\Delta\subset\mathbf P^1_Y\times_Y\mathbf P^1_Y$ (the Kummer boundary of its
local equation, with supports) via
$M=R\mathrm{pr}_{2*}(\Delta_*\Lambda\otimes\mathrm{pr}_1^{*}M)\to
R\mathrm{pr}_{2*}\mathrm{pr}_1^{*}M(1)[2]\cong q^{*}Rq_*M(1)[2]$ (proper base
change), and the two triangle identities reduce, by (a) and proper base
change, to $t_q(h)=1$ on the fibres of $\mathrm{pr}_1$ and $\mathrm{pr}_2$.
Uniqueness of right adjoints then identifies $q^{*}K(1)[2]\cong Rq^{!}K$ as
the transpose of this counit; restricting along the open $\bar\jmath$
($Rp^{!}=\bar\jmath^{*}Rq^{!}$ and $Rp_!=Rq_*\bar\jmath_!$ with
$\bar\jmath_!\dashv\bar\jmath^{*}$) shows that $\gamma_{p,K}$ is the
transpose of the composite adjunction, hence an isomorphism. Naturality in
$K$ is that of the adjunction, and base-change compatibility —
$Lg'^{*}\gamma_{p,K}$ corresponds to $\gamma_{p',Lg^{*}K}$ under the
base-change mate $Lg'^{*}Rp^{!}\to Rp'^{!}Lg^{*}$, which is therefore an
isomorphism — follows from that of $\int_p$ and of $\mathrm{Ex}_!$
([sk-prop-sf-cbc]).
*(d) Normalization.* Transposing under $Rs_*\dashv Rs^{!}$ and
$Rp_!\dashv Rp^{!}$ ($ps=\mathrm{id}$, so $Rp_!Rs_*=\mathrm{id}$), the composite
$\Lambda_Y\xrightarrow{\mathrm{pur}_s}Rs^{!}\Lambda(1)[2]
\xrightarrow{Rs^{!}\gamma_{p,\Lambda}}Rs^{!}Rp^{!}\Lambda_Y\cong\Lambda_Y$ is
$\int_p$ evaluated at the image of $\partial\kappa(t)\in
H^2_{s(Y)}(\Aaf^1_Y,\Lambda(1))$ in $H^0(Y,Rp_!\Lambda(1)[2])$, i.e. $t_q$ of
the image of $\partial\kappa(t)$ in $H^2(\mathbf P^1_Y,\Lambda(1))$.
Forgetting the support, the Kummer boundary of the local equation $t$ of the
zero-section divisor $D_0$ is the Kummer first Chern class
$c_1(\mathcal O(D_0))=c_1(\mathcal O(1))=h$, so the composite is $t_q(h)=1$.
This is (iii) for $c=1$: $Rs^{!}\gamma_{p,\Lambda}$ is the inverse of
$\mathrm{pur}_s$.

*Step 6: induction on $c$.* Write $\Aaf^c_B=\Aaf^1_{B'}$ with
$B'=\Aaf^{c-1}_B$ and $p_c=p_{c-1}\circ p'$, $p':\Aaf^1_{B'}\to B'$ the
last-coordinate projection, and put
$\gamma_{p_c,K}:=c_{p_{c-1},p'}^{-1}\circ\gamma_{p',Rp_{c-1}^{!}K}\circ
Lp'^{*}(\gamma_{p_{c-1},K})(1)[2]$: an isomorphism by induction and Step 5,
natural in $K$ and base-change compatible since each factor is; its
transpose is the iterated trace
$\int_{p_c}=\int_{p_{c-1}}\circ Rp_{c-1!}(\int_{p'})$, an isomorphism
$Rp_{c!}\Lambda(c)[2c]\cong\Lambda_B$ by the projection formula. The
composition law of (ii) is the associativity of the $c_{g,f}$ and of the
twist-additivity isomorphisms, and a permutation of the coordinates permutes
the factors of this composite, all shifts being even, so no Koszul sign
appears (detailed: prop:pur-affine-space-composition-law,
cor:pur-affine-space-purity,
prop:pur-affine-space-purity-compatibilities). Normalization:
$z=s'\circ z_{c-1}$ with $z_{c-1}:B\hookrightarrow B'$ the zero section of
$p_{c-1}$ and $s'$ that of $p'$. Tate twists pulled back from the base pass
through $R(-)^{!}$ (the projection formula for $R(-)_!$, transposed), so for
$M=Rp_{c-1}^{!}\Lambda_B\cong\Lambda_{B'}(c-1)[2c-2]$ the map
$Rs'^{!}\gamma_{p',M}$ is $M\otimes Rs'^{!}\gamma_{p',\Lambda}$; with Step 5(d)
over the base $B'$ and the iterative identification of Step 1
($\mathrm{th}_c=Rz_{c-1}^{!}(\mathrm{pur}_{s'}\otimes1)\circ\mathrm{th}_{c-1}$,
the last factor along $s'$) this gives

$$
Rz^{!}\gamma_{p_c,\Lambda}\circ\mathrm{th}_c
=Rz_{c-1}^{!}\Bigl(\gamma_{p_{c-1},\Lambda}\otimes
\bigl(Rs'^{!}\gamma_{p',\Lambda}\circ\mathrm{pur}_{s'}\bigr)\Bigr)\circ
\mathrm{th}_{c-1}
=Rz_{c-1}^{!}\gamma_{p_{c-1},\Lambda}\circ\mathrm{th}_{c-1}=\mathrm{id},
$$

which is (iii) for $\Aaf^c_B$; equivalently $\int_{p_c}$ sends
$\partial\kappa(t_1)\cup\cdots\cup\partial\kappa(t_c)$ to $1$.

*Step 7: vector bundles.* Let $\pi:E\to Z$ have rank $c$ and let
$\{U_\alpha\to Z\}$ be an étale cover trivializing $E$. Formation of
$R\pi_!$ commutes with these base changes ([sk-prop-sf-cbc]), so by Step 6
$R\pi_!\Lambda_E(c)[2c]$ is a lisse rank-one sheaf on $Z$ placed in degree
zero, and the local traces $\int_{\pi_{U_\alpha}}$ are local trivializations
of it. Each sends the class of the zero section — the image of the global
section $\mathrm{th}_E$ of Step 4 under
$Rz^{!}\Lambda_E(c)[2c]=R\pi_!Rz_*Rz^{!}\Lambda_E(c)[2c]\to R\pi_!\Lambda_E(c)[2c]$,
which on $U_\alpha$ is the coordinate frame class — to $1$ by Step 6, so
they agree on overlaps (two trivializations of a lisse rank-one sheaf that
agree on a generating section agree) and glue by the sheaf axiom to a global
trace $\int_\pi:R\pi_!\Lambda_E(c)[2c]\xrightarrow{\sim}\Lambda_Z$ (detailed:
def:amb-vector-integration, lem:amb-linear-trace-invariance).
Define $\gamma_{\pi,K}$ as its transpose, as in Step 5(c). For étale
$u:U_\alpha\to Z$ with $u':E_{U_\alpha}\to E$, the composition law and
$Ru^{!}=u^{*}$ give $u'^{*}R\pi^{!}=R\pi_{U_\alpha}^{!}u^{*}$, under which
$u'^{*}\gamma_{\pi,K}$ is the affine-space comparison
$\gamma_{\pi_{U_\alpha},u^{*}K}$ of Step 6; the cone of $\gamma_{\pi,K}$ thus
has vanishing cohomology sheaves at every geometric point of $E$, hence is
zero, so $\gamma_{\pi,K}$ is an isomorphism. Base change and the
normalization (iii) are inherited from Step 6 in the same way (detailed:
cor:pur-vector-bundle-purity).

Uses: [sk-def-purity-conv], [sk-prop-a1-inv], [sk-prop-a1], [sk-prop-a1-kummer], [sk-prop-cd], [sk-prop-h2], [sk-prop-sf-cbc], [sk-prop-sf-open-closed-triangle], [sk-thm-properbasechange], [sk-lem-sf-mate]
