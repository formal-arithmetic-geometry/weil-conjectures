/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.CategoryTheory.DgAbcData
import Sheaf.CategoryTheory.DgAbcConeHomotopy
import Sheaf.SixFunctors.DgAbcAdmissibleReplacement

/-!
# Triangulation from the dg axioms A, B and C

Source: Stacks Project, `dga.tex`, section-review, Tags 09QJ, 09P6, 09QU and 09QY
(blueprint: lem-coef-dg-abc-homotopy-category-triangulated).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.IntegralDGCategory.ABC

/-- A small cochain dg category satisfying (A), (B) and (C) has exactly the asserted triangulated H⁰
category.

Source: Stacks Project, dga.tex, Tags 09QJ, 09P6, 09QU and 09QY.

(blueprint: lem-coef-dg-abc-homotopy-category-triangulated).

Proof step 1. The Leibniz identity makes boundaries an ideal among closed degree-zero maps: if
$\partial a=\partial b=0$ and $h$ has degree $-1$, then $b\partial h=\partial(bh)$ and
$(\partial h)a=\partial(ha)$. Thus composition descends to the abelian-group quotients
$H^0\mathcal A(x,y)$. The closed inclusions and projections in (A) retain their biproduct
equations in this quotient, so it is additive with zero object. The dg functors in (B) act
additively on these quotients and have strict inverses $[-n]$.

Proof step 2. For an admissible sequence $(a,b,\pi,s)$, differentiating $bs=1$, $\pi a=1$, and
$a\pi+sb=1$ gives $b\partial s=0$, $(\partial\pi)a=0$, and $a\partial\pi+(\partial s)b=0$.
Multiplying by $a\pi+sb$ gives $\partial s=a\pi\partial s$ and $\partial\pi=(\partial\pi)sb$.
Differentiating $\pi s=0$ gives $\delta=\pi\partial s=-(\partial\pi)s$. Hence $a\delta=\partial
s$, $\delta b=-\partial\pi$; also $a\partial\delta=\partial(a\delta)=0$, whence
$\partial\delta=\pi a\partial\delta=0$. These are precisely the closed boundary and the null
composite classes required for the associated triangle, with the shift identifications of (B).

Proof step 3. The class of the boundary does not depend on the graded splitting. For another
splitting $(\pi\prime,s\prime)$ of the same closed sequence, $s\prime-s=a\pi s\prime$ and
$\pi\prime a=1$. Since $\partial s=a\delta$, we have $\pi\prime\partial s=\delta$. Consequently
$\delta\prime=\pi\prime\partial(s+a\pi s\prime)=\delta+\pi\prime a\partial(\pi
s\prime)=\delta+\partial(\pi s\prime)$. Under (B), the last term is a boundary in the complex
defining the arrow $z\to x[1]$, so both splittings define the same arrow in $H^0\mathcal A$.

Proof step 4. For an admissible sequence $x\xrightarrow{a}y\xrightarrow{b}z$, part (i) of the
cone-comparison lemma gives an isomorphism, with identities on $x,y$, from
$(x,y,c(a),a,i_a,-p_a)$ to its associated triangle. Conversely, for a closed $f:x\to y$, apply
admissible replacement with $N=2$ to obtain $x\xrightarrow{j}\widetilde y$ admissible and a
homotopy equivalence $r:\widetilde y\to y$ with $rj=f$. Choose its admissible quotient $q$. Part
(i) compares $c(j)$ with $q$; part (ii), on the strictly commuting square $(1_x,r)$, compares
$c(j)$ with $c(f)$ by a homotopy equivalence. Composing these diagram isomorphisms exhibits the
cone triangle of $f$ as isomorphic to the triangle of the admissible sequence $x\to\widetilde
y\to q$. Thus the two classes of distinguished triangles coincide. Since every $H^0$-morphism
has a closed representative, this also proves the cone-existence clause of TR1. More precisely,
every distinguished triangle $T=(x,y,z,f,i,d)$ admits this cone normal form with identities on
$x,y$: choose an isomorphism from $T$ to an admissible-sequence triangle and then use (i) to
reach a cone triangle of $f':x'\to y'$. Represent its first two isomorphisms by closed homotopy
equivalences $a:x\to x'$, $b:y\to y'$. Their square commutes in $H^0$, so (ii) gives an
isomorphism from the cone triangle of a closed representative of $f$ to that cone triangle of
$f'$, with first two components $[a],[b]$. Composing with the inverse of the chosen isomorphism
to $T$ gives identity components on $x,y$. This uses no triangulated-category axiom.

Uses: lem-coef-dg-abc-cone-homotopy, lem-coef-dg-abc-admissible-replacement.

Proof step 5. Isomorphism invariance is built into the definition of distinguished triangles.
The sequence $x\xrightarrow{1}x\to0$ is admissible with $\pi=1$, $s=0$, so its boundary is zero.
This supplies the identity triangle and finishes TR1. For forward rotation, reduce to a cone
triangle using step 4. Its rotation $(y,c(f),x[1],i_f,-p_f,-f[1])$ is isomorphic, by $(1,1,-1)$,
to the admissible-sequence triangle $(y,c(f),x[1],i_f,p_f,f[1])$ supplied by (C). Thus forward
rotation preserves distinguishedness.

Proof step 6. For inverse rotation, take an admissible sequence
$x\xrightarrow{a}y\xrightarrow{b}z$ with splitting $(\pi,s)$ and boundary $\delta$. Put
$D=\delta[-1]:z[-1]\to x$ and choose the cone sequence $x\xrightarrow{i}c(D)\xrightarrow{p}z$,
with graded splitting $(\rho,t)$. Write $\widehat D=\pi\partial s\in\mathcal A(z,x)^1$ for the
degree-one version of $D$ under (B). The boundary identities give $\partial\pi=-\widehat D b$,
$\partial s=a\widehat D$, $\partial t=i\widehat D$, and $\partial\rho=-\widehat D p$. Define
degree-zero maps $E=i\pi+tb:y\to c(D)$ and $F=a\rho+sp:c(D)\to y$. Their differentials vanish
because $\partial E=-i\widehat D b+i\widehat D b=0$ and $\partial F=-a\widehat D p+a\widehat D
p=0$. The splitting identities give $FE=a\pi+sb=1_y$ and $EF=i\rho+tp=1_{c(D)}$, with the cross
terms zero by $\rho t=0$, $pi=0$, $\pi s=0$, and $ba=0$; they also give $Ea=i$ and $pE=b$. Thus
$(-1_{z[-1]},1_x,E)$ identifies the inverse rotation $(z[-1],x,y,-D,a,b)$ with the cone triangle
$(z[-1],x,c(D),D,i,-p)$: the first square is $1_x(-D)=D(-1)$, the second is $Ea=i$, and the last
is $(-1_z)b=(-p)E$. This cone triangle is distinguished by step 4. Rotation and inverse rotation
are inverse on triangle diagrams, so both directions of TR2 follow using isomorphism invariance.

Proof step 7. For TR3, use the identity-on-first-two-objects comparison of step 4 to put both
distinguished triangles in cone form, without changing the specified first square in $H^0$.
Choose closed representatives $a:x_1\to x_2$, $b:y_1\to y_2$ and degree-$-1$ $h$ with $\partial
h=bf_1-f_2a$. Write the two cone splittings $(\pi_i,s_i)$ and closed inclusions/projections
$(i_i,p_i)$. In shifted Hom notation define $c=i_2b\pi_1+s_2a[1]p_1+i_2hp_1$. The Leibniz rule
and the boundary identities give $\partial c=-i_2bf_1p_1+i_2f_2ap_1+i_2(bf_1-f_2a)p_1=0$, while
$ci_1=i_2b$ and $p_2c=a[1]p_1$. Thus $(a,b,c)$ is a morphism of the cone triangles (including
their negative projections); undoing the two isomorphisms gives the required morphism of the
original triangles. Steps 1 and 4-7 give every pre-triangulated axiom in
[def-weil-triangulated-category].

Uses: def-weil-triangulated-category.

Proof step 8. For TR4, start with any composable pair in $H^0\mathcal A$ and choose closed
representatives $f:x\to y$ and $g:y\to z$. Apply the finite admissible replacement lemma with
$N=3$ to $(x,y,z;f,g)$. Its strict commuting equalities $r_2j_1=fr_1$ and $r_3j_2=gr_2$ make
this pair isomorphic in $H^0$ to the pair of admissible monomorphisms $j_1:y_1\to y_2$,
$j_2:y_2\to y_3$. Each $[r_i]$ is invertible by the lemma's homotopy-equivalence assertion.

Uses: lem-coef-dg-abc-admissible-replacement.

Proof step 9. Apply the admissible flag quotient lemma to $\alpha=j_1$, $\beta=j_2$. Its three
admissible quotient sequences give distinguished triangles of $\alpha$, $\beta\alpha$, and
$\beta$, by the definition already justified in steps 2-3. The closed maps $u:q_1\to q_2$,
$v:q_2\to q_3$ satisfy the four equations $up_1=p_2\beta$, $\delta_2u=\delta_1$, $vp_2=p_3$,
$\delta_3v=\alpha[1]\delta_2$ in $H^0$. These are the four octahedral squares. Its fourth
admissible sequence $q_1\xrightarrow{u}q_2\xrightarrow{v}q_3$ gives a distinguished triangle
with last arrow $p_1[1]\delta_3$, exactly the composite required by TR4. Hence some choice of
triangles over this isomorphic replacement pair admits an octahedron.

Uses: lem-coef-dg-abc-admissible-flag-quotients.

Proof step 10. Apply the isomorphic-octahedron criterion to the pre-triangulated category
established in step 7, using the replacement isomorphisms from step 8 and the three triangles
and fourth distinguished triangle from step 9. All its hypotheses hold for every composable
pair; no triangulatedness was assumed in the dg constructions. The criterion yields TR4 for
every prescribed triple of distinguished triangles, not just the quotient choices. Therefore
$H^0\mathcal A$ is triangulated with precisely the distinguished cone triangles identified in
step 4.

Uses: lem-coef-triangulated-octahedron-iso-criterion. -/
theorem abc_homotopy_category_triangulated (A : IntegralDGCategory.{u, v})
    (hA : AxiomA A) (S : Shifts A)
    (hC : ∀ (x y : A.Obj) (f : Closed A x y), Nonempty (Cone S f)) :
    Nonempty (TriangulatedRealization A S) := by
  sorry

end CategoryTheory.IntegralDGCategory.ABC
