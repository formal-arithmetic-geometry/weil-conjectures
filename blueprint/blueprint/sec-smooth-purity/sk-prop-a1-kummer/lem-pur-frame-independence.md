+++
id = "lem-pur-frame-independence"
kind = "lemma"
title = "Independence of the frame"
order = 1943
uses = ["def-pur-frame-class", "def-pur-support-cohomology", "lem-pur-kunneth-supported"]
+++
In the situation of [def-pur-frame-class], the class
$\operatorname{cl}(f)$ of [def-pur-frame-class] depends only on
the ideal of $Z$, i.e. only on the pair, not on the frame.

## Proof

The class $\operatorname{cl}(f)$ of [def-pur-frame-class] is a
section of the sheaf $\mathcal H^{2c}_{Z\cap U}(\Lambda(c))$ on the
étale site of $U$: it is built from the boundary maps and the supported
cup products of [def-pur-support-cohomology], both of which are defined
sheaf-theoretically. Two sections of a sheaf which agree after an étale
base change agree, so we may replace $U$ by an affine strictly local
étale neighbourhood of a geometric point of $U$. There
$\mathcal O(U)=R$ is a local ring, the two frames are defined over $R$,
and $f'=Mf$ for an invertible $M\in\mathrm{GL}_c(R)$. Over a local ring
an invertible matrix has Smith normal form with unit diagonal entries:
there are elementary matrices $E_1,E_2$ and an invertible diagonal $D$
with

$$
M=E_1DE_2 ,
$$

because row and column operations bring $M$ to a diagonal matrix whose
entries are the invariant factors, and these are units as soon as
$\det M$ is. Applying the frame change in the order $E_2$, then $D$,
then $E_1$, it suffices to check the invariance of
$\operatorname{cl}$ under each of the three kinds of operation.
*Unit multiples*: for
$f_1'=uf_1$, $\kappa(uf_1)=\kappa(u)+\kappa(f_1)$ and the Kummer
class of the unit $u$ extends over all of $U$, hence vanishes under
the boundary of the support long exact sequence (the exactness of
[def-pur-support-cohomology]), so the class does not change.
*Permutations*: the exterior products sit in even degree, so the
Künneth symmetry has sign $+1$. *Elementary shears*: for
$f_1'=f_1+uf_2$, consider the family of frames
$f(t)=(f_1+tuf_2,f_2,\dots,f_c)$ over $T=\mathbf A^1_U$. The pair
$(T\times_UV,T\times_UZ)$ is the pullback of the constant family, so by
[lem-pur-kunneth-supported] and the base change of the localization
triangle ([lem-pur-kunneth-supported], the support long exact
sequence of [def-pur-support-cohomology]) the sheaf
$H^{2c}_{T\times_UZ}(T\times_UV,\Lambda(c))$ is the constant sheaf
$\Lambda_T$ on the connected scheme $T$ (the affine line over the local
ring $R$ is connected). The classes
$\operatorname{cl}(f(t))$ assemble into a global section
$\widetilde{\operatorname{cl}}$ of this constant sheaf (the boundary
of the cup product of the Kummer classes of the family of frames, each
$\kappa(f_j(t))$ living on the complement of $V(f_j(t))$); a global
section of a constant sheaf on a connected scheme is constant, so all
its stalks coincide, and the stalks at $t=0$ and $t=1$ are
$\operatorname{cl}(f)$ and $\operatorname{cl}(f')$.
This proves $\operatorname{cl}(Mf)=\operatorname{cl}(f)$ for every
invertible $M$, first over the strictly local $U$, and then over the
original $U$ by the sheaf property. Hence $\operatorname{cl}(f)$
depends only on the ideal of $Z$.
