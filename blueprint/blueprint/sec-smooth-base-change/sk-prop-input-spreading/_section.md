+++
id = "sk-prop-input-spreading"
kind = "section"
title = "Spreading a finite étale Galois cover"
order = 1404
uses = ["sk-def-smooth"]
lean = ["AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre"]
+++
*Proposition (sketch).*

Let $S$ be a qcqs integral normal scheme with generic point $\eta$,
let $C\to S$ be a qcqs smooth morphism with geometrically connected
fibres, and fix a section $\sigma:S\to C$. Let $Z\to C_\eta$ be a
finite étale Galois cover with group $G$, assume $|G|$ is
invertible on $S$, and assume $Z$ carries a $\kappa(\eta)$-rational
point above $\sigma(\eta)$. Then there is a finite étale Galois
cover $\widetilde Z\to C$ with group $G$ whose restriction to
$C_\eta$ is the given cover $Z\to C_\eta$.

## Proof

This is 0EZJ; the five steps below are the argument, which the
detailed blueprint now carries in full at
sbc-thm-spreading-finite-etale-galois. The tame structure results
(0EYG, 0EYH, 0EYI) and the purity and depth-two
extension results (0EYE, 0EY6, 0EY9) are quoted
classical inputs; what is proved here is the assembly.

*Limit reduction.* For $S$ Noetherian the statement is
0EYJ. In general write the qcqs integral normal $S$ as a
cofiltered limit of Noetherian integral normal schemes; the qcqs
morphism $C\to S$ of finite presentation, the section $\sigma$, the
cover $Z\to C_\eta$ and its $G$-action all descend to a finite stage,
smoothness and geometric connectedness of the fibres hold there after
shrinking, and the cover produced at that stage pulls back to the one
wanted over $S$.

*The trait case.* Let $S=\Spec R$ with $R$ a discrete valuation
ring and closed point $s$. Then $C_s\subset C$ is an effective
Cartier divisor, regular because it is smooth over a field, and
$C_\eta=C\setminus C_s$. At a codimension-one point of $C_s$ the
local ring is a discrete valuation ring, and for a finite Galois
extension of its fraction field all ramification indices are equal to
one integer $e$ dividing $|G|$ (09EB); as $|G|$ is invertible
on $S$, so is $e$. Hence $Z$ is *tamely* ramified over $C$ in
codimension one. Let $Z'\to C$ be the normalization of $C$ in $Z$.
Tameness makes it finite locally free, with
$\pi^{-1}(C_s)_{\mathrm{red}}$ a regular effective Cartier divisor,
and étale-locally on $C$ a disjoint union of standard tame covers
$\Spec A[x]/(x^e-f)\to\Spec A$ with $f$ a nonzerodivisor, $A/fA$
regular and $e$ invertible (0EYG, 0EYH); the
$G$-action extends to $Z'$.

*Where the section is used.* Apply the trait test
0EYI to $t=\sigma:\Spec R\to C$, whose scheme-theoretic
preimage of $C_s$ is the reduced closed point. By hypothesis
$Z_{\sigma(\eta)}$ has a $\kappa(\eta)$-rational point, and the
simply transitive $G$-action then makes that whole fibre a disjoint
union of copies of $\Spec\kappa(\eta)$; so $Z'\to C$ is finite
étale over an open neighbourhood of $\sigma(s)$. As $C_s$ is
irreducible, that neighbourhood already contains its generic point,
so $Z$ is *un*ramified over $C$ in codimension one, and purity
across a regular effective Cartier divisor (0EYE) extends it
to a finite étale $\widetilde Z\to C$ with
$\widetilde Z|_{C_\eta}=Z$. One checks étale-locally that
$\widetilde Z\cong Z'$, so the $G$-action makes it Galois with group
$G$.

*From the trait to a Noetherian base: a maximal open.* Let
$U\subseteq S$ be maximal among the opens carrying a finite étale
Galois cover with group $G$ restricting to $Z$ over $C_\eta$; it
contains $\eta$. Suppose $U\neq S$ and let $s$ be a generic point of
an irreducible component of $S\setminus U$. Replace $S$ by
$\Spec\mathcal O_{S,s}=\Spec A$, so that $U$ becomes the punctured
spectrum and $Y\to C\times_SU$ is the given cover. If $\dim A=1$ the
trait case finishes it. So assume $\dim A\ge2$; normality gives
$\operatorname{depth}A\ge2$ (031S), and flatness of $C\to S$
propagates this to $\operatorname{depth}\mathcal O_{C,x}\ge2$ for
every $x$ over $s$ (0337).

*Extension in depth $\ge2$, and the local computation.* In that
depth the pushforward $\mathcal B=j_*\pi_*\mathcal O_Y$ is a
reflexive $\mathcal O_C$-algebra and $Y'=\underline\Spec_C\mathcal B$
is the unique finite $Y'\to C$ restricting to $Y$ over
$C\times_SU$ and of depth $\ge2$ along the complement; it inherits
the $G$-action, is étale exactly where it is flat, and its
formation commutes with flat base change (0EY6). Only its
étaleness is in doubt, and it suffices to check it at the generic
point of $C_s$ (0EYB). Choose an affine $\Spec B\subseteq C$
around $\sigma(s)$, so $A\to B$ is smooth with a section $\sigma$
with kernel $I$; the $I$-adic completion is
$B^\wedge\cong A[[x_1,\dots,x_d]]$ (05D5), $B\to B^\wedge$ is
flat, and the image of $\Spec B^\wedge\to C$ contains the generic
point of $C_s$. Let $V\subseteq\Spec B^\wedge$ be the preimage of
$U$ and $W=Y\times_{C\times_SU}V$. The slice
$V_0=V\cap V(x_1,\dots,x_d)$ is $\sigma(U)\cong U$, and
$W_0=W\times_VV_0$ is completely split over it — this is again the
$\kappa(\eta)$-point hypothesis, propagated by the $G$-action. Full
faithfulness of $\mathrm{F\acute Et}_V\to\mathrm{F\acute Et}_{V_0}$
for a power series ring over a local ring of depth $\ge2$
(0EY9) gives $W\cong W_0\times_UV$, so $W$ is a disjoint
union of copies of $V$; hence $Y'\times_C\Spec B^\wedge$ is split and
$Y'\to C$ is étale where it had to be. Spreading $Y'$ out over a
slightly larger open of $S$ (0BQ5, 0EY3)
contradicts the maximality of $U$, so $U=S$.

*Scope of the Lean statement.* Only the case of an abelian group
$G=M$ is used by the smooth base change proof, and only that case is
stated in Lean, as an extension of $M$-torsors in the sense of
[sk-prop-input-torsors]. Neither the uniqueness of the extension nor
connectedness of the extended cover is asserted: the torsors that
[sk-thm-vanishing] spreads are those attached to an arbitrary class in
$H^1$, which need not be connected.

Uses: [sk-def-smooth], `sbc-thm-spreading-finite-etale-galois`
