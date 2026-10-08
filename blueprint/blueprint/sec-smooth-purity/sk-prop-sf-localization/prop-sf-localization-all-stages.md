+++
id = "prop-sf-localization-all-stages"
kind = "theorem"
title = "The closed-support triangle at every coefficient stage"
order = 1868
tags = ["latex:proposition"]
uses = ["def-sc-etale-torsion-cd", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-tor-amplitude", "def-weil-pbc-proetale-operations", "def-weil-rationalization-karoubi", "def-weil-weil-sheaf-complex", "lem-exc-proetale-closed-essential-image", "lem-exc-proetale-closed-exact", "lem-exc-proetale-closed-support", "lem-exc-proetale-support-triangle", "lem-exc-residue-tor-test", "lem-sf-etale-direct-image-vanishing", "lem-sf-proetale-constructible-origin", "lem-sf-proetale-residue-tor-test", "lem-sf-triangle-two-out-of-three", "lemma-weil-pbc-completed-pullback-reduction", "prop-sf-closed-immersion-unit", "prop-sf-closed-unit-all-stages", "prop-sf-open-closed-triangle-all-stages", "prop-weil-pbc-comparison-direct-image", "prop-weil-pbc-descent-functors", "prop-weil-pbc-direct-image-limits", "prop-weil-pbc-proetale-constant-ring-map", "prop-weil-pbc-rational-transport", "prop-weil-pbc-roos-triangle", "prop-weil-pbc-scalar-extension", "thm-constructible-serre", "thm-fin-open-immersion", "thm-sc-finite-type-torsion-cd", "thm-sp-truncation-e2", "thm-weil-pbc-site-comparison", "thm-weil-pbc-verdier-axioms"]
+++
Let $X$ be a separated finite-type $k$-scheme, let $i:Z\hookrightarrow X$ be
a closed immersion and $j:U\hookrightarrow X$ the complementary open
immersion. Let $\Lambda$ be one of the coefficient stages
$A_{E,n},\mathcal O_E,E,\Qlb$, with the categories $D^b_c(-,\Lambda)$ of
[def-weil-derived-complete-integral-detailed],
[def-weil-rationalization-karoubi],
[def-weil-algebraically-closed-coefficients], the pullbacks of
[def-weil-derived-pullback-tensor-hom] and the direct images $i_*$, $Rj_*$
of [def-weil-derived-direct-image].

1. $Rj_*$ carries $D^b_c(U,\Lambda)$ into $D^b_c(X,\Lambda)$.
2. $i_*:D^b_c(Z,\Lambda)\to D^b_c(X,\Lambda)$ has a right adjoint $Ri^!$;
   it is the exceptional inverse image of
   [def-weil-exceptional-inverse-image] (at $\mathcal O_E$ it is
   $R\varprojlim_n\operatorname{Res}_nRi_n^!K_n$, with reductions
   $Ri_n^!K_n$).
3. For $K\in D^b_c(X,\Lambda)$ the closed exceptional counit and the open
   unit extend to a distinguished triangle
   $$
   i_*Ri^!K\longrightarrow K\longrightarrow Rj_*j^*K
   \longrightarrow i_*Ri^!K[1],
   $$
   with $\operatorname{Hom}(i_*Ri^!K[m],Rj_*j^*K)=0$ for all $m$, so the
   third arrow is unique and the triangle is functorial in $K$.
4. $Ri^!Rj_*G=0$ for $G\in D^b_c(U,\Lambda)$, and the unit
   $Q\to Ri^!i_*Q$ is an isomorphism for $Q\in D^b_c(Z,\Lambda)$.

The same holds on the finite-Tor subcategories $D^b_{ctf}(-,\Lambda)$ of
[def-weil-finite-tor-amplitude]. Let $d=\dim U$ and assume
$c=\operatorname{cd}_{\rm tor}(k)$ ([def-sc-etale-torsion-cd]) is finite
($c=0$ for $k$ algebraically closed).

- (1') $Rj_*$ carries $D^b_{ctf}(U,\Lambda)$ into $D^b_{ctf}(X,\Lambda)$;
   at $\Lambda=A_{E,n}$ Tor amplitude in $[a,b]$ goes to Tor amplitude in
   $[a,b+2d+c]$, and at $\mathcal O_E$ the same holds for the uniform
   interval of the reductions.
- (2') $Ri^!$ carries $D^b_{ctf}(X,\Lambda)$ into $D^b_{ctf}(Z,\Lambda)$,
   with Tor amplitude $[a,b]$ going to $[a,b+2d+c+1]$ (at $A_{E,n}$, and
   uniformly in the reductions at $\mathcal O_E$).
- (3') $i_*$, $i^*$ and $j^*$ preserve $D^b_{ctf}$ and Tor amplitude
   intervals; hence for $K\in D^b_{ctf}(X,\Lambda)$ all three vertices of
   the triangle of (3) lie in $D^b_{ctf}$.
- (4') For $G\in D^b_{ctf}(U,\Lambda)$ and $Q\in D^b_{ctf}(Z,\Lambda)$,
   $Ri^!Rj_*G=0$ and $Q\xrightarrow{\sim}Ri^!i_*Q$ inside $D^b_{ctf}$.

At $E$ and $\Qlb$ these are (1)–(4), since there $D^b_{ctf}=D^b_c$.

If $X,Z,U$ come from $k_0$-schemes and $\Lambda\in\{E,\Qlb\}$, then $Ri^!$
carries Weil structures ([def-weil-weil-sheaf-complex]) for which the
adjunction is equivariant, and for Weil complexes the three arrows of the
triangle and the unit are Weil-equivariant.

## Proof

*Vanishing.* At every stage $\operatorname{Hom}(i_*P[m],Rj_*N)=0$ for
$P\in D^b_c(Z,\Lambda)$ and $N\in D^b_c(U,\Lambda)$. At a finite stage this
is $\operatorname{Hom}(j^*i_*P[m],N)$ by $j^*\dashv Rj_*$
([def-weil-pbc-proetale-operations]), and $j^*i_*=0$ by
[lem-exc-proetale-closed-essential-image] and the exactness of $i_*$
([lem-exc-proetale-closed-exact]). At $\mathcal O_E$ it follows from the
finite case by the Roos triangle of [prop-weil-pbc-roos-triangle] (as in
[prop-sf-open-closed-triangle-all-stages]), since
$Rj_*N=R\varprojlim_n\operatorname{Res}_nRj_*N_n$ by
[def-weil-derived-direct-image], [prop-weil-pbc-direct-image-limits]. At $E$
and $\Qlb$ the groups are $\otimes E$, resp. filtered colimits, of these.

*Finite stage.* Let $A=A_{E,n}$. For (1), write $G=\nu_U^*G'$ with $G'$
étale bounded constructible ([lem-sf-proetale-constructible-origin]); then
$Rj_*G\cong\nu_X^*Rj_*G'$ by [prop-weil-pbc-comparison-direct-image], and
$Rj_*G'$ is bounded constructible by [thm-fin-open-immersion] and dévissage
over the finitely many cohomology sheaves ([thm-constructible-serre]). The
right adjoint $Ri^!$ of $i_*$ on the ambient categories is
[lem-exc-proetale-closed-support], and the triangle of (3) is
[lem-exc-proetale-support-triangle]. Its outer vertices $K$ and
$Rj_*j^*K$ are in $D^b_c$, hence so is $i_*Ri^!K$, and
$Ri^!K\cong i^*i_*Ri^!K$ lies in $D^b_c(Z,A)$. So $Ri^!$ restricts to
$D^b_c$, and by uniqueness of right adjoints it is the finite exceptional
inverse image of [def-weil-exceptional-inverse-image], as in
[prop-sf-closed-immersion-unit].

*Integral stage.* Put $R=\mathcal O_E$, $A_n=R/\varpi_E^n$ and
$K_n=K\otimes^L_RA_n$. For (1): $M=Rj_*G$ is derived complete with
$M_n\cong Rj_*G_n$ ([prop-weil-pbc-direct-image-limits]), and these are
bounded constructible by the finite stage. The triangles
$M_1\to M_n\to M_{n-1}\to$ induced by
$0\to A_1\xrightarrow{\varpi_E^{n-1}}A_n\to A_{n-1}\to0$ show inductively
that all $M_n$ lie in the cohomological interval of $M_1$ and are
constructible ([thm-constructible-serre]), so $M\in D^b_c(X,R)$.

For (2) and (3), let $K\in D^b_c(X,R)$, let $K\to Rj_*j^*K$ be the derived
limit of the finite units (its reductions are the finite units, by
[lemma-weil-pbc-completed-pullback-reduction] and
[prop-weil-pbc-direct-image-limits]), and let $F$ be its fibre, an object of
$D^b_c(X,R)$ by (1). By TR3 and the finite triangles, the induced map of
triangles is an isomorphism on two terms, hence on the third
([lem-sf-triangle-two-out-of-three]):
$F_n\cong i_*Ri_n^!K_n$. Put $Q=i^*F\in D^b_c(Z,R)$. The unit
$F\to i_*i^*F$, taken as the derived limit of the finite units, reduces to
the finite units, which are isomorphisms because $F_n$ lies in the image of
$i_*$ ([lem-exc-proetale-closed-essential-image]). Its cone is derived
complete with zero reductions, hence zero by [def-weil-derived-complete]; so
$F\cong i_*Q$ and $Q_n\cong Ri_n^!K_n$. For $P\in D^b_c(Z,R)$ the vanishing
above and the full faithfulness of [prop-sf-closed-unit-all-stages] give,
naturally in $P$,
$$
\operatorname{Hom}(P,Q)\cong\operatorname{Hom}(i_*P,i_*Q)
=\operatorname{Hom}(i_*P,F)\xrightarrow{\sim}\operatorname{Hom}(i_*P,K).
$$
Thus $Ri^!K:=Q$ is right adjoint to $i_*$, with counit $F\to K$; since $Q$
is derived complete with reductions $Ri_n^!K_n$, it is the derived limit of
[def-weil-exceptional-inverse-image]. The triangle of (3) is
$F\to K\to Rj_*j^*K\to$.

*Rational stage.* The exact $R$-linear functor $Ri^!$, the adjunction data
and the maps of the triangle rationalize by
[prop-weil-pbc-rational-transport]; Hom groups become
$\operatorname{Hom}\otimes_RE$, so the adjunction persists, and triangles
remain distinguished.

*Algebraically closed stage.* Since $Ri^!K\cong i^*\operatorname{fib}(K\to
Rj_*j^*K)$ with a fibre unique up to unique isomorphism (by the vanishing),
the scalar-extension compatibilities of $i^*,j^*,Rj_*$
([prop-weil-pbc-scalar-extension]) induce coherent ones for $Ri^!$. So
$Ri^!$, its adjunction and the triangle descend by
[prop-weil-pbc-descent-functors], triangles remain distinguished by
[thm-weil-pbc-verdier-axioms], and the Hom bijections pass to the filtered
colimits.

*Consequences.* For (4): $\operatorname{Hom}(N[m],Ri^!Rj_*G)
=\operatorname{Hom}(i_*N[m],Rj_*G)=0$ for all $N$ and $m$, so
$Ri^!Rj_*G=0$; the unit is an isomorphism by
[prop-sf-closed-unit-all-stages].

*Finite Tor amplitude.* Let $A=A_{E,n}$ and $\kappa=A/(\varpi_E)$, the
constant sheaf on each site.

*Residue criterion.* On any of the pro-étale sites, a bounded constructible
complex $K$ has Tor amplitude in $[a,b]$ if and only if $K\otimes^L_A\kappa$
has cohomology in $[a,b]$, by [lem-sf-proetale-residue-tor-test], the
pro-étale form of the étale criterion [lem-exc-residue-tor-test]; it is
applied below only to bounded constructible complexes, by (1) and (2). The pullbacks
$i^*,j^*,\nu^*$ commute with $-\otimes^L_A\kappa$, being monoidal with
$\kappa$ pulling back to $\kappa$ ([def-weil-derived-pullback-tensor-hom],
[prop-weil-pbc-proetale-constant-ring-map]); being exact they preserve
cohomological intervals. Conversely $\nu^*$ reflects them: if
$\nu^*C$ has cohomology in $[a,b]$ for $C\in\Dplus$, then
$\nu^*\tau_{>b}C=\tau_{>b}\nu^*C=0$, hence $\tau_{>b}C=0$ by
[thm-weil-pbc-site-comparison], and likewise below $a$.

*(3') for $i^*,j^*,i_*$.* For $i^*$ and $j^*$ this is the criterion and
the commutation just stated. For $P\in D^b_{ctf}(Z,A)$ with amplitude
$[a,b]$, $j^*(i_*P\otimes^L_A\kappa)\cong j^*i_*P\otimes^L_A\kappa=0$, so
each cohomology sheaf of $i_*P\otimes^L_A\kappa$ is in the image of $i_*$
([lem-exc-proetale-closed-essential-image]) and equals
$i_*i^*\mathcal H^r(i_*P\otimes^L_A\kappa)\cong
i_*\mathcal H^r(P\otimes^L_A\kappa)$, using exactness of $i^*$ and
$i^*i_*\cong\operatorname{id}$; it vanishes outside $[a,b]$.

*(1') at the finite stage.* Let $G\in D^b_{ctf}(U,A)$ have amplitude
$[a,b]$ and write $G=\nu_U^*G'$ as in the proof of (1). Then
$\nu_U^*(G'\otimes^L_A\kappa)\cong G\otimes^L_A\kappa$ has cohomology in
$[a,b]$, hence so has $G'\otimes^L_A\kappa$. The higher direct images
$R^qj_*$ on the small étale site vanish on sheaves of $A$-modules for
$q>2d+c$: for $k$ algebraically closed this is
[lem-sf-etale-direct-image-vanishing]; in general its proof applies
verbatim, with [thm-sc-finite-type-torsion-cd] at the given $c$. By the
truncation spectral sequence [thm-sp-truncation-e2],
$Rj_*(G'\otimes^L_A\kappa)$ has cohomology in $[a,b+2d+c]$.

*Projection formula for $\kappa$.* The canonical map
$Rj_*G'\otimes^L_A\kappa\to Rj_*(G'\otimes^L_A\kappa)$ is an isomorphism.
Choose a bounded-above resolution $P\to\kappa$ by finite free $A$-modules;
tensoring with the constant complex $P$ computes $-\otimes^L_A\kappa$. For
the finite stupid truncations $\sigma_{\ge-t}P$ the comparison is an
isomorphism: it is the identity for $A$ and is preserved by finite sums,
shifts and cones. Let $G'$ and $Rj_*G'$ have cohomology in degrees $\le e$.
The quotients $\sigma_{<-t}P$ live in degrees $\le-t-1$, so
$G'\otimes\sigma_{<-t}P$ has cohomology in degrees $\le e-t-1$, and
$Rj_*$ of it in degrees $\le e-t-1+2d+c$ (the vanishing above), while
$Rj_*G'\otimes\sigma_{<-t}P$ has cohomology in degrees $\le e-t-1$.
For fixed $r$ and $t$ large, the long exact sequences of the two
triangles attached to $\sigma_{\ge-t}P\to P\to\sigma_{<-t}P$ therefore
identify both sides with the finite-free comparison in degree $r$.

Hence $Rj_*G'\otimes^L_A\kappa$ has cohomology in $[a,b+2d+c]$. Applying
$\nu_X^*$ and [prop-weil-pbc-comparison-direct-image],
$Rj_*G\otimes^L_A\kappa\cong\nu_X^*(Rj_*G'\otimes^L_A\kappa)$ has
cohomology in the same interval; with (1), the residue criterion gives
$Rj_*G\in D^b_{ctf}(X,A)$ with amplitude $[a,b+2d+c]$.

*(2') at the finite stage.* Let $K$ have amplitude $[a,b]$. Then $j^*K$
has amplitude $[a,b]$ and $Rj_*j^*K$ amplitude $[a,b+2d+c]$. Tensoring the
triangle of (3) with $\kappa$ and taking the long exact sequence,
$\mathcal H^r(i_*Ri^!K\otimes^L_A\kappa)$ lies between
$\mathcal H^{r-1}(Rj_*j^*K\otimes^L_A\kappa)$ and
$\mathcal H^r(K\otimes^L_A\kappa)$, so it vanishes outside
$[a,b+2d+c+1]$. Since $Ri^!K\cong i^*i_*Ri^!K$, the commutation of $i^*$
with $-\otimes^L_A\kappa$ and the residue criterion give amplitude
$[a,b+2d+c+1]$ for $Ri^!K$.

*Other stages.* At $\mathcal O_E$, the reductions are
$(Rj_*G)_m\cong Rj_*G_m$ ([prop-weil-pbc-direct-image-limits]) and
$(Ri^!K)_m\cong Ri_m^!K_m$ (integral stage above), and similarly for
$i^*,j^*,i_*$; the finite-stage bounds hold with intervals depending only on
the uniform interval of the reductions of $G$, resp. $K$. At $E$ and $\Qlb$,
$D^b_{ctf}=D^b_c$ by [def-weil-finite-tor-amplitude]. Clauses (3') and (4')
are then (3) and (4) read inside the full subcategories $D^b_{ctf}$.

*Weil structures.* The Weil structures of $i^*,j^*,Rj_*$ and the
equivariance of the open unit are those of
[prop-sf-open-closed-triangle-all-stages]. For a Weil complex $K$, the
fibre $F$ therefore carries a unique Weil structure making $F\to K$
equivariant (uniqueness from the vanishing), and $Ri^!K=i^*F$ inherits it;
under the adjunction bijection above this is the mate of the Weil structure
of $i_*$, so the adjunction, its counit and unit are equivariant. The third
arrow is equivariant by the uniqueness in (3).
