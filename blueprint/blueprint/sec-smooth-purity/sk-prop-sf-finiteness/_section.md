+++
id = "sk-prop-sf-finiteness"
kind = "section"
title = "Finiteness and constructibility"
order = 1652
lean = ["AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerStar", "AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek"]
+++
*Proposition (sketch).*

Let $\Lambda$ be a finite ring annihilated by an integer invertible on the
schemes in question and let $f:X\to Y$ be a morphism of finite-type
$k$-schemes. Then $Rf_*$ carries $\Dbc(X,\Lambda)$ into $\Dbc(Y,\Lambda)$
(*separatedness of $f$ is not needed*); if $e$ bounds the dimensions of
the geometric fibres and $f$ is separated, then $Rf_!$ carries
$\Dbc(X,\Lambda)$ into $\Dbc(Y,\Lambda)$ and $R^qf_!\mathcal F=0$ for $q>2e$.
Moreover the torsion cohomological dimension of a finite-type $k$-scheme of
dimension $d$ over a field $k$ with $\mathrm{cd}_{\mathrm{tor}}(k)\le c$ is
bounded by $2d+c$; in particular $\mathrm{cd}_{\mathrm{tor}}(\Spec K)=0$ for
$K$ separably closed.
Chapter 15 (finiteness and constructibility of direct images):
thm:dg-finite-type-constructibility for ordinary direct images and
sbc-thm-finiteness-finite-type for compact support; Chapter 4 for the
proper case thm:weil-pbc-direct-image-finiteness-proper; Chapter 12
(`06c`) for thm:sc-finite-type-torsion-cd; Chapter 16 for
lem:kun-cd-sep-closed-point.

## Proof

*The engine: generic constructibility for an open immersion*
(thm:fin-deligne-generic-open). Let $S$ be integral of finite type over
$k$ and $j:X\hookrightarrow Y$ an open immersion of finite-type $S$-schemes.
Replacing $Y$ by the scheme-theoretic closure of $X$ — closed direct image
is exact, preserves constructibility and commutes with base change — one may
assume $X$ dense. Induct on $n=\dim X_{k(S)}$, the case $n=0$ being the
observation that a closed subscheme with empty generic fibre becomes empty
after inverting one element of the base. *First*, viewing
$X\cap Y_\alpha\hookrightarrow Y_\alpha$ over the base $\mathbf A^1_S$ for
each affine chart and each coordinate drops the generic source dimension by
one, so the induction hypothesis gives a dense open $G\subseteq Y$ over which
$Rj_*F$ is bounded constructible and commutes with base change, with
$Z=Y\setminus G$ finite over $S$ after shrinking $S$. *Second*, for
smooth $X\to S$ and locally constant $F$, compactify to $b:Y\to S$
projective, put $K=Rj_*F$ and $a=bj$: the first step gives $K|_G\in\Dbc(G)$,
generic smooth direct image gives $Ra_*F=Rb_*K\in\Dbc(S)$ after a further
shrinking, and finite-boundary reconstruction over $Z$ gives $K\in\Dbc(Y)$;
the exchange morphism is an isomorphism on $G_T$, hence after $Rb_{T,*}$ by
proper base change, hence everywhere by finite-boundary comparison.
*Third*, for arbitrary constructible $F$, a finite radicial surjective
base change and a shrinking produce a dense smooth open $v:V\hookrightarrow X$
on which $F$ is locally constant. The triangle
$F\to Rv_*v^*F\to\Delta\to F[1]$ has $\Delta=i_*i^*\Delta$ supported on the
reduced closed complement $i:W\hookrightarrow X$, whose generic dimension is
$<n$; the induction hypothesis applies to $ji:W\to Y$ and to the finitely many
$\mathcal H^q(i^*\Delta)$, and the long exact sequence of $Rj_*$ applied to
the triangle gives the claim, with the three exchange morphisms forming a
morphism of triangles. Radicial descent
(lem:fin-radicial-exchange-descent) returns the result to $S$. Taking
$S=\Spec k$, whose only nonempty open is $S$ itself, turns the generic
statement into the absolute one: $Rj_*F\in\Dbc(Y,\mathbf F_\ell)$ for every
open immersion of finite-type $k$-schemes
(cor:fin-deligne-open-over-field). Passing from $\mathbf F_\ell$ to a
finite ring $\Lambda$ is dévissage: split a constructible sheaf into its
primary parts, filter the $\ell$-primary part by $\ell^iF$, compute each
$\ell$-torsion quotient over $\mathbf F_\ell$
(lem:fin-coefficients-forgetful-direct-image), and assemble by the finite
sequence of long exact sequences and the truncation triangles; the $\Lambda$-action
is carried along. This gives $Rj_*:\Dbc(X,\Lambda)\to\Dbc(Y,\Lambda)$
(cor:fin-deligne-open-finite-coefficients).

*Ordinary direct image, $f$ not necessarily separated*
(thm:dg-finite-type-constructibility). The assertion is local on $Y$, so
take $Y$ affine, and cover $X$ by finitely many affine opens
$X_1,\dots,X_r$. For $\emptyset\neq I\subseteq\{1,\dots,r\}$ the intersection
$X_I=\bigcap_{i\in I}X_i$ is a quasi-compact open of an affine $X_i$, hence
locally closed in some $\mathbf P^m_Y$; in its scheme-theoretic closure it is
open and dense, giving $f_I:X_I\xrightarrow{j_I}\overline X_I \xrightarrow{p_I}Y$ with $j_I$ open and $p_I$ projective. The previous
paragraph bounds $Rj_{I,*}$ and the proper case below bounds $Rp_{I,*}$, so
each $Rf_{I,*}$ is bounded constructible. The finite alternating  Cech
resolution of the cover — exact because inserting the index of a member
containing a given point contracts the augmented complex, and termwise
injective because restriction to an open preserves injectives — yields

$$
E_1^{p,q}=\bigoplus_{|I|=p+1}\mathcal H^q\bigl(Rf_{I,*}K|_{X_I}\bigr)
\ \Longrightarrow\ \mathcal H^{p+q}(Rf_*K),
$$

concentrated in $0\le p\le r-1$ and in the finite union of the ranges just
obtained. Constructible sheaves form a Serre subcategory, so every page is
constructible and the abutment has a finite constructible filtration.
Separatedness is never used.

*Compact supports* (sbc-thm-finiteness-finite-type). For separated
$f$ write $f=rj$ by [sk-thm-nagata-compactification], so $Rf_!=Rr_*j_!$ by
[sk-def-sf-operations] (iv). Extension by zero preserves constructibility,
and $Rr_*$ is bounded constructible by the proper case; the vanishing
$R^qf_!\mathcal F=0$ for $q>2e$ is read off the *original* fibres of $f$,
no fibre-dimension bound for the compactification being needed.

*The proper case* (thm:weil-pbc-direct-image-finiteness-proper).
For proper $f$ with geometric fibres of dimension $\le e$, constructibility of
$R^qf_*F$ and its vanishing for $q>2e$ are the classical finiteness theorem
(Deligne, SGA41/2, *Théorème de finitude*, Th. 1.1,
together with 095U); the pro-étale form follows by applying
$\nu^*$ through [sk-prop-sf-comparison].

*The cohomological-dimension bound*
(thm:sc-finite-type-torsion-cd). Let
$\epsilon:X_{\Et}\to X_{\mathrm{Zar}}$ be the comparison. Its inverse image
is exact, since the geometric stalk of $\epsilon^{-1}G$ is the Zariski stalk
$G_x$, so $\epsilon_*$ preserves injectives and there is a Leray spectral
sequence $H^p(X_{\mathrm{Zar}},R^q\epsilon_*F)\Rightarrow H^{p+q}(X_{\Et},F)$.
The Zariski stalk of $R^q\epsilon_*F$ at $x$ is
$\varinjlim_{x\in V}H^q(V_{\Et},F|_V)$, computed over the cofinal affine
neighbourhoods, which have dimension $\le d$; the affine bound kills it for
$q>d+c$. Grothendieck vanishing kills the spectral sequence for $p>d$. Hence
all surviving total degrees are $\le2d+c$. For $K$ separably closed every
torsion étale sheaf on $\Spec K$ is acyclic in positive degrees, so
$\mathrm{cd}_{\mathrm{tor}}(\Spec K)=0$ (lem:kun-cd-sep-closed-point).

Uses: `lem-kun-cd-sep-closed-point`, `sbc-thm-finiteness-finite-type`, `thm-dg-finite-type-constructibility`, `thm-sc-finite-type-torsion-cd`, `thm-weil-pbc-direct-image-finiteness-proper`
