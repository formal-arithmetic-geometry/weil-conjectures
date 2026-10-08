+++
id = "sk-prop-sf-existence"
kind = "section"
title = "Existence of the exceptional right adjoint"
order = 1801
uses = ["sk-prop-sf-comparison"]
lean = ["AlgebraicGeometry.Etale.rightDerivedUpperShriekAdjunction", "AlgebraicGeometry.ProEtale.rightDerivedUpperShriekAdjunction"]
+++
*Proposition (sketch).*

(a) *On the ordinary derived categories of the small étale sites*: if
$f:X\to S$ is compactifiable between Noetherian schemes, the functor
$Rf_!=Rr_*j_!:D(X_{\Et},A)\to D(S_{\Et},A)$ has a right adjoint
$f^{\times}:D(S_{\Et},A)\to D(X_{\Et},A)$; no restriction to a constructible
subcategory is made. (b) *On the small pro-étale sites (conditional;
its hypothesis is false in general, and it is not used)*:
if $\operatorname{FullCD}(p,A;c)$ holds for the proper part $p$ of a
compactification of a separated finite-type $f$, then
$Rf_{!,n}:D(X_{\Proet},A)\to D(Y_{\Proet},A)$ preserves
coproducts and therefore has a right adjoint
$Rf_n^{\times}:D(Y_{\Proet},A)\to D(X_{\Proet},A)$, and the
adjunction is independent of the compactification. The hypothesis
$\operatorname{FullCD}(p,A;c)$ is *false* for a general proper $p$ —
already for an elliptic curve over $\overline{\mathbf F}_p$ with
$A=\mathbf F_r$, $r\ne p$ — and for that $p$ the conclusion fails as well:
$Rp_*$ does not preserve coproducts and has no right adjoint on
$D(E_{\Proet},A)$ or on $D^+(E_{\Proet},A)$
([sk-rem-sf-fullcd-scope]). So (b) is a conditional implication
whose hypothesis is not a theorem; it is recorded for comparison only and is
used nowhere in this blueprint.
(c) *The constructible exceptional adjoint (unconditional)*: let
$f:X\to Y$ be a separated finite-type morphism of finite-type $k$-schemes,
$k=\overline{\mathbf F}_q$, and $A=A_{E,n}$. With $f^{\times}$ the étale
right adjoint of (a), the functor
$$
Rf^!:=\nu_X^*\,f^{\times}\,R\nu_{Y,*}:
D^+(Y_{\Proet},A)\longrightarrow D^+(X_{\Proet},A)
$$
satisfies $\operatorname{Hom}_Y(Rf_{!,n}K,L)\cong\operatorname{Hom}_X(K,Rf^!L)$,
naturally, for every bounded-below $K$ of étale origin and every
bounded-below $L$; its units and counits are compatible with refinements of
the compactification, and on $\Dctf(Y,A)=\nu_Y^*\Dctf(Y_{\Et},A)$ it is
$Rf^!(\nu_Y^*G)=\nu_X^*f^{\times}G$. This is the functor $Rf^!$ of
[sk-def-sf-operations] (vi); that it carries $\Dctf(Y,A)$ into
$\Dctf(X,A)$ is [sk-prop-sf-rf-shriek-preservation].
Chapter 14 (smooth duality on the ordinary derived category):
thm:amb-etale-exceptional-adjoint, by Brown representability (Stacks
`0F5Y`) applied to the exact coproduct-preserving $Rf_!$; Chapter 30
for (b), prop:ambient-exceptional-adjoint; for (c),
thm:sf-ambient-adjoint-class, through the compact-support comparison
lem:sf-class-compact-support-comparison and the full faithfulness of
$\nu^*$ on $D^+$ (thm:weil-pbc-site-comparison).
part (b) only, which is conditional on $\operatorname{FullCD}$, i.e. on
clause (1) of [sk-def-sf-admissible]; that clause is false in general
([sk-rem-sf-fullcd-scope]), so (b)
is not a theorem and is not used. Parts (a) and (c) are unconditional: on
the étale-origin class the bound
$\operatorname{FullCD}(p,A;2\dim\overline X)$ is
[sk-prop-sf-fullcd-etale-origin], a consequence of
[sk-prop-sf-finiteness] and [sk-prop-sf-comparison], and (c) needs only
it and (a).
*Note: clause (b), the ambient adjoint on all of $D(X_{\Proet},A)$, is
never used later and has no detailed counterpart in the blueprint; downstream
uses only (c), the adjunction relative to the class of étale origin, whose
detailed counterpart is thm:sf-ambient-adjoint-class.*

## Proof

Write $K=\nu_X^*G$ with $G\in D^+(X_{\Et},A)$. The compact-support
comparison ([sk-prop-sf-comparison] applied to the proper part and the
extension by zero) gives $Rf_{!,n}K\cong\nu_Y^*Rf^{\Et}_!G$; then
$$
\operatorname{Hom}_Y(\nu_Y^*Rf^{\Et}_!G,L)
\cong\operatorname{Hom}_{Y_{\Et}}(Rf^{\Et}_!G,R\nu_{Y,*}L)
\cong\operatorname{Hom}_{X_{\Et}}(G,f^{\times}R\nu_{Y,*}L)
\cong\operatorname{Hom}_X(\nu_X^*G,\nu_X^*f^{\times}R\nu_{Y,*}L),
$$
the first by the adjunction $\nu_Y^*\dashv R\nu_{Y,*}$, the second by (a),
the third by the full faithfulness of $\nu_X^*$ on bounded-below complexes
([sk-prop-sf-comparison]; $f^{\times}$ preserves $D^+$ because $Rf^{\Et}_!$
has finite cohomological amplitude, so $f^{\times}R\nu_{Y,*}L$ is bounded
below). Compactification independence follows from that of $Rf^{\Et}_!$
by uniqueness of adjoints. Every object of $\Dctf(X,A)$ is of étale origin
([09AK](https://stacks.math.columbia.edu/tag/09AK)), so the adjunction holds on the small categories.


Uses: `def-weil-full-cohomological-dimension`, `thm-amb-etale-exceptional-adjoint`, [sk-prop-sf-comparison], `thm-sf-ambient-adjoint-class`
