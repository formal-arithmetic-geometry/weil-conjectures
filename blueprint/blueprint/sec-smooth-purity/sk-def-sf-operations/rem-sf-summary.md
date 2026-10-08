+++
id = "rem-sf-summary"
kind = "remark"
title = "What a six-functor formalism is"
order = 1497
+++
A *six-functor formalism* on a category of schemes (here: finite-type
$k$-schemes, with the small pro-étale sites and a fixed coefficient ring)
consists of the following data.

1. **Two adjoint pairs per morphism.** For every separated
finite-type $f:X\to Y$ a pair $Lf^*\dashv Rf_*$ and, when $f$ is
exceptional-adjoint
admissible, a pair $Rf_!\dashv Rf^!$; the four functors are
$Lf^*,Rf_*,Rf_!,Rf^!$ — the ``six'' operations counting the tensor
product and the internal Hom.
1. **A monoidal structure.** The derived tensor product
$-\otimes^L_\Lambda-$ is symmetric monoidal on the coefficient categories
and $Lf^*$ is monoidal.
1. **Base change.** For a Cartesian square, $Lg^*Rf_!\cong Rf'_!Lg'^*$ always, and $Lg^*Rf_*\cong Rf'_*Lg'^*$ when $f$ is proper or
$g$ is smooth.
1. **The projection formula.** $Rf_!K\otimes^L_\Lambda L\cong Rf_!(K\otimes^L_\Lambda Lf^*L)$.
1. **Proper and smooth compatibility.** $Rf_!\cong Rf_*$ for
proper $f$; and for smooth $f$ the *orientation* $Rf^!\Lambda\cong Lf^*\Lambda(d)[2d]$ (relative dimension $d$) — the one datum that is not
a formal consequence of the rest.

Items 1–4 are the axioms; item 5 splits into a formal half (properness)
and the geometric input (smoothness, i.e. purity). The tensor–adjunction form of Verdier exchange is formal from items
1–4. General Verdier biduality requires its separate geometric theorem;
after that theorem and the orientation are supplied, the trace and the
Poincare pairing follow by the stated formal constructions. What is *not* formal is (i) the verification of the
axioms for the concrete coefficient system — for this blueprint,
proper, smooth and compact-support base change, the compactification
comparison, and the coefficient transports — and (ii) the orientation of
item 5. In the compiled blueprint these are exactly where the open
obligations live: the interface [fix-prop-projection-formula] (discharged in [thm-sf-pf-finite], [prop-sf-pf-reduction], [thm-sf-pf-adic], [thm-sf-pf-field], [thm-sf-pf-proetale] and [prop-sf-pf-coherence]), the base-change chapters, and the
purity chapter. In this chapter the framework is axiomatized once, the
formal core is proved once, and the two non-formal inputs are supplied.
