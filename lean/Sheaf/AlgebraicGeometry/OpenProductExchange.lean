/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.AlgebraicGeometry.OpenExchangeSeparableClosureReduction
public import Sheaf.AlgebraicGeometry.InvertibleTorsionOrders
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Point.Basic
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import Sheaf.Paper.KunBcMapOnCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Sheaf.AlgebraicGeometry.InvertibleOrdersColimit
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.AlgebraicGeometry.EtaleSheafClopenProduct
import Sheaf.AlgebraicGeometry.EtaleBaseChangeOpenClosed
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.AlgebraicGeometry.SmoothBaseChangeLimit
import Sheaf.Paper.KunBaseChange
import Sheaf.AlgebraicGeometry.StalkFaithfulDerived
import Sheaf.AlgebraicGeometry.StrictHenselization
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.StrictHenselizationLimit
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.CategoryTheory.KunDescentLimit
import Sheaf.AlgebraicGeometry.OpenImmersionRestriction
import Sheaf.AlgebraicGeometry.DimensionExtension
import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits
import Sheaf.AlgebraicGeometry.FieldExtensionExchange
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.AlgebraicGeometry.ClosedPointsProduct
import Sheaf.AlgebraicGeometry.AffineProjectiveCompactification
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import Sheaf.AlgebraicGeometry.ProperKunnethGlobalSections
import Sheaf.Paper.KunBcKunnethCompat
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.DerivedModuleUnderlyingComparison
import Sheaf.AlgebraicGeometry.ClosedPointSupportDetection
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Open-immersion exchange over a field

Source: Stacks Project, Tag 0F1H, lemma-kunneth-localize-on-X
(blueprint: lem-kun-0f1h).

The canonical map `openProductExchange` uses `Y ×_K X` and its pullback along `j`
as the chosen model of `Y ×_K U`. The coefficient sheaf is placed in degree zero.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Open-product exchange is invertible for abelian sheaves with stalkwise torsion
orders invertible in the field, without a uniform annihilator.
Source: Stacks Project, Tag 0F1H, lemma-kunneth-localize-on-X
(blueprint: lem-kun-0f1h).

Proof, following all ten steps of the node:
1. Write $Z=Y\times_KX$, $V=Y\times_KU$, and $\beta_F:q^{-1}Rj_*F\to Rh_*p^{-1}F$. A field is
Noetherian since its only ideals are $0$ and $K$. Thus $U,X,Y$ are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian], and are quasi-separated by
[lem-weil-pbc-locally-noetherian-quasi-separated]. Clause (1) of
[lem-weil-pbc-qcqs-morphism-permanence] makes $j$ quasi-compact and quasi-separated, and clause
(3) makes its base change $h$ so. We will also use those clauses for other indicated base changes.
Inverse image for constant coefficients is exact and a left adjoint by
[prop-weil-pbc-inverse-image-modules-exact]; it therefore preserves colimits, since maps out of
the image of a colimit correspond under the adjunction to compatible maps out of its terms. For a
sheaf in degree zero all our exchange maps lie in $D^+$: [lem-kun-unbounded-exchange-agrees]
identifies the abelian unbounded map in the statement with the bounded-below map. The inclusion is
full and faithful, so it reflects invertibility (an inverse and its two identities lift by
fullness and faithfulness). By [lem-kun-bc-map-on-cohomology] its degree-$r$ cohomology map is
$q^{-1}R^rj_*F\to R^rh_*p^{-1}F$, and for $r<0$ both sides vanish. By
[lem-weil-pbc-derived-plus-iso-on-cohomology] it is enough to prove these maps are isomorphisms
for all $r\ge0$.

2. The stalk torsion hypothesis makes $F$ a locally torsion sheaf by
[lem-weil-pbc-torsion-sheaf-characterizations], implication (3) to (2). By
[lem-kun-invertible-orders-colimit], $F=\varinjlim_{n\in I_K}F[n]$, with $I_K$ the positive
integers invertible in $K$, ordered by divisibility. This index is nonempty and directed: $1\in
I_K$ and $nm$ is an upper bound for $n,m$. Each $F[n]$ has its canonical $\mathbf Z/n\mathbf
Z$-module structure, since multiplication of sections by integers factors through this quotient.
The stalk hypothesis on $F$ is exactly the invertible-order condition of
[def-kun-torsion-invertible]. For fixed $r\ge0$, [lemma-weil-pbc-direct-image-filtered-colimit]
applies to $j,h$ from Step 1, and inverse images commute with colimits by Step 1. Naturality of
exchange in its coefficient sheaf, as in [def-kun-unbounded-exchange], identifies the degree-$r$
map for $F$ with the colimit of those for $F[n]$. A colimit of a natural family of isomorphisms is
an isomorphism, since the compatible inverses induce its inverse. Hence it suffices to prove the
assertion for sheaves annihilated by one $n\in I_K$. Such sheaves, and all inverse images of them,
are still killed by $n$, so [lem-kun-zn-sheaf-invertible-orders] verifies every coefficient
hypothesis below. No unbounded derived-colimit theorem is being inferred from a sheaf-colimit
theorem.

3. For all fields $K$ and all $n$ invertible in $K$ simultaneously, induct on $N=\dim X+\dim Y$
when $X,Y$ are nonempty; it is a nonnegative integer by [lem-kun-dimension-finite-type]. If either
factor is empty then $Z,V$ are empty and both objects are zero: an abelian sheaf on the empty
scheme has only its zero section, by the empty-cover sheaf condition. Assume the assertion at all
smaller sums. If $\dim X=0$, [lem-weil-pbc-finite-type-dim-zero-artinian] makes $X$ finite
discrete, so $U$ is open and closed. In the decomposition $X=U\amalg(X\setminus U)$,
[lem-weil-pbc-etale-sheaf-clopen-product] identifies restriction with projection onto the $U$
factor; its right adjoint $j_*$ inserts the zero sheaf on the other factor, because morphisms to
that inserted object are precisely morphisms on $U$. Kernels and cokernels are componentwise in a
product, so this insertion is exact. The same reasoning holds for $h$, which is again open and
closed after base change. Consequently their higher direct images in positive degrees vanish,
while degree zero exchange is an isomorphism by [lem-kun-base-change-open-closed]. Step 1 finishes
this case. This includes the base $N=0$; the remaining argument is the induction step with $\dim
X>0$.

4. The problem is local on the two factors. An open immersion is etale by
[lem-weil-pbc-open-immersion-etale] and smooth by
[lem-weil-pbc-etale-smooth-zero-dimensional-fibres]; its base changes remain open immersions by
[lem-weil-pbc-open-immersion-base-change]. For an affine open $X_0\subset X$, use [lem-kun-0f09]
with the constant one-term smooth system $X_0\to X$, first for $j$ with coefficient $F$, then for
$h$ with coefficient $p^{-1}F$ and the base change $Y\times_KX_0\to Z$. These maps are qcqs by
Step 1's permanence facts. The comparison diagram in clause (2) of [lem-kun-bc-base-change] has
both vertical maps invertible, so it identifies the restriction of $\beta_F$ with the exchange for
$U\times_XX_0\to X_0$ and $Y$. For an affine open $Y_0\subset Y$, apply the same smooth comparison
to $h$ along $Y_0\times_KX\to Z$. Clause (1) of [lem-kun-bc-base-change], with $u:Y_0\times_KX\to
Z$ and original square $(j,h,q,p)$, then identifies the product exchange for $Y_0$ with
$\operatorname{Ex}_{h,u}\circ u^{-1}\beta_F$, under inverse-image composition. Thus restriction
detects a failure at any specified geometric point, by [lem-kun-stalk-faithful-derived]. Affine
opens and their inverse images here remain finite type: on a finite-type affine chart the
quasi-compact open has a finite cover by principal opens $\operatorname{Spec}A_f$, and $A_f$ is
finitely generated over $K$ by adjoining $f^{-1}$ to generators of $A$. Dimension cannot increase
on an open: closure in $X$ of a strict chain of irreducible closed subsets in the open is still
strict, since intersection with the open recovers the chain. Therefore a restriction with smaller
dimension sum is handled by induction, and otherwise we may use affine $X,Y$ of the same sum when
analyzing any point.

5. Take affine $X,Y$ as in Step 4, a geometric point $\bar z$ of $Z$ with image $x\in X$, and
assume $\operatorname{trdeg}_K\kappa(x)>0$. Set $X'=\operatorname{Spec}\mathcal
O^{\mathrm{sh}}_{X,\bar x}$, $U'=U\times_XX'$, and $r_Z:Y\times_KX'\to Z$. By
[def-weil-pbc-strict-henselization-limit] this is the inverse limit of a small cofiltered system
of affine pointed etale neighborhoods of $\bar x$; it is an inverse limit, not a colimit of
schemes. [lem-weil-pbc-cofiltered-limit-directed-reindex] permits a directed index. The transition
maps are affine by [lem-weil-pbc-morphism-affine-schemes-affine]. The neighborhood maps to $X$ are
qcqs by Step 1 and smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres]. Their base
changes to $Z$ have affine transitions by [lem-weil-pbc-affine-morphism-permanence], and their
limit is $Y\times_KX'$ by [lem-kun-fibre-product-limits]. Apply [lem-kun-0f09] to $j$ with $F$,
and to $h$ with $p^{-1}F$; it yields canonical comparison isomorphisms $a:r_X^{-1}Rj_*F\to
Rj'_*F'$ and $b:r_Z^{-1}Rh_*p^{-1}F\to Rh'_*p'^{-1}F'$. Here primes denote the product square over
$X'$ and $F'=F|_{U'}$. Clause (2) of [lem-kun-bc-base-change] gives $b\circ
r_Z^{-1}\beta_F=\beta_{F'}\circ q'^{-1}a$, after its specified inverse-image composition
isomorphisms. Notice that the first direct-image leg is $j$, not $q$. The chosen $\bar z$ lifts to
$Y\times_KX'$ by the pointed strict-localization map $\bar x\to X'$ and the fibre-product
universal property. By [lem-kun-stalk-as-pullback], proving $\beta_{F'}$ invertible will therefore
prove invertibility at $\bar z$.

6. By [lem-kun-0f0u], write $X'=\varprojlim_iX_i$ with affine finite-type $L$-schemes $X_i$,
affine transitions, $L/K$ separably closed, and $\dim X_i<\dim X$. Reindex by a directed set as
above if necessary. The open $U'\subset X'$ is quasi-compact since $j'$ is a qc base change of
$j$. [lem-kun-descent-limit-open] gives a stage $i_0$ and a quasi-compact open $U_{i_0}\subset
X_{i_0}$ inducing $U'$. For $i\ge i_0$ put $U_i=U_{i_0}\times_{X_{i_0}}X_i$ and $j_i:U_i\to X_i$;
transitions are affine by [lem-weil-pbc-affine-morphism-permanence], and $U'=\varprojlim U_i$ by
[lem-kun-fibre-product-limits]. Each $U_i$ is finite type over $L$ by the principal-open argument
of Step 4. To reconstruct coefficients without assuming $U'$ affine, put $G=j'_*F'$ on the affine
scheme $X'$, $G_i=\pi_{i,*}G$, and $F_i=j_i^{-1}G_i$. These sheaves are annihilated by $n$, as
seen sectionwise for direct images and by additivity for inverse images. [lem-kun-descent-limit]
applies on $X'$ to give $G=\varinjlim_i\pi_i^{-1}G_i$. Restrict this equality to $U'$ using the
colimit-preserving inverse image of Step 1; the counit isomorphism of
[lem-kun-open-immersion-restriction] gives $F'=\varinjlim_i(\pi_i|_{U'})^{-1}F_i$. The transition
maps are the canonical ones from this reconstruction and remain compatible after restriction.
Apply the induction hypothesis over $L$ to $j_i$, $Y_L$, and $F_i$: [lem-kun-dimension-extension]
gives $\dim Y_L=\dim Y$, so each sum is smaller. For each $r\ge0$, [lem-kun-0ezt] now applies with
its corners $(X_i,Y_i,S_i,T_i)=(Y_L\times_LX_i,Y_L\times_LU_i,X_i,U_i)$ and coefficient $F_i$ on
$T_i=U_i$; its direct-image leg is $g_i=j_i$, which is qcqs. All transitions are affine, all
limits have just been identified, and its limit coefficient is precisely $F'$. Thus every
degree-$r$ exchange is invertible at the limit. Step 1 proves $\beta_{F'}$ invertible, completing
the case of Step 5.

7. If instead $\bar z$ maps to $y\in Y$ with $\operatorname{trdeg}_K\kappa(y)>0$, put
$Y'=\operatorname{Spec}\mathcal O^{\mathrm{sh}}_{Y,\bar y}$. The construction of Step 5, now using
neighborhoods over $Y$, makes $f:Y'\times_KX\to Z$ a limit of smooth qcqs maps with affine
transitions. Apply [lem-kun-0f09] to $h$ and $p^{-1}F$; clause (1) of [lem-kun-bc-base-change]
identifies the exchange for the outer product square over $X$ with $\operatorname{Ex}_{h,f}\circ
f^{-1}\beta_F$. By [lem-kun-0f0u], $Y'=\varprojlim_iY_i$ with affine finite-type schemes over a
separably closed extension $L/K$ and $\dim Y_i<\dim Y$. The identifications
$Y'\times_KX=Y'\times_LX_L$ and similarly for $U$ follow directly from the fibre-product universal
properties. Apply the canonical field-extension exchange theorem [lem-kun-0f1c-exchange] to
$j,F,L/K$. Its hypotheses hold by Step 1 and $nF=0$, and it gives an isomorphism
$a:r_X^{-1}Rj_*F\to Rj_{L,*}F_L$. With $q':Y'\times_LX_L\to X_L$, clause (1) of
[lem-kun-bc-base-change], this time factoring the outer base map as $r_Xq'$, gives
$\beta_{\mathrm{outer}}=\beta'\circ q'^{-1}a$. Consequently it suffices to prove $\beta'$
invertible. For each $i$, induction applies over $L$ to $j_L$, $Y_i$, and $F_L$, because $\dim
X_L=\dim X$ by [lem-kun-dimension-extension]. Apply [lem-kun-0ezt] degreewise with corners
$(Y_i\times_LX_L,Y_i\times_LU_L,X_L,U_L)$; the two bottom systems and coefficient $F_L$ are
constant, the direct-image leg is $j_L$, and the limit square follows from
[lem-kun-fibre-product-limits]. This proves $\beta'$ invertible by Step 1. Pull back to the
geometric lift of $\bar z$ as in Step 5 to conclude. By [lem-kun-closed-point-field] and
[lem-kun-closed-points-of-product], every nonclosed point of $Z$ has at least one of these two
positive-transcendence-degree images. Together with Step 4, we have proved invertibility at all
nonclosed points for all data of dimension sum $N$, over every field.

8. Suppose a counterexample of sum $N$ remains. Step 7 makes its failures closed-point failures,
and Step 4 allows an affine neighborhood in each factor retaining a failure; a smaller resulting
sum is impossible by induction. For affine $Y$, [lem-kun-compactification-affine] gives an open
dense embedding $Y\hookrightarrow\overline Y$ with $\overline Y$ projective over $K$, and
[lem-kun-dimension-extension] gives $\dim\overline Y=\dim Y$. Step 4's open-restriction comparison
in the second factor identifies the original map with the restriction of the map for $\overline
Y$. Thus the latter is still a counterexample with the same sum. It suffices to rule out this
projective case. By [lem-kun-0f1h-sep-reduction], it suffices to prove its scalar-extended map
over $K^{\mathrm{sep}}$ invertible. Dimension is unchanged by [lem-kun-dimension-extension].
Projectivity is unchanged by scalar extension by [lem-pc-projective-base-change]. Step 7 applies
to this new data over the extended field and again gives invertibility at all nonclosed points.
This last application is needed: no claim that arbitrary scalar extension carries the old closed
support to closed support is being used. We may now work over separably closed $K$ with projective
$Y$ and a map invertible at every nonclosed point.

9. Put $A=\mathbf Z/n\mathbf Z$ and retain the canonical $A$-module structure on $F$. Form the
$A$-coefficient exchange $\beta_A$. By [lem-kun-unbounded-abelian-exchange-comparison], forgetting
coefficients is exact and conservative, commutes with inverse/direct images by its endpoint
isomorphisms, and carries $\beta_A$ to the original abelian exchange. Thus it is enough to prove
$\beta_A$ invertible. The projective factor $Y$ is proper by [lem-kun-projective-implies-proper].
Apply [lem-kun-0f14b] to the ordered pairs $(Y,X)$ with $(\underline A_Y,Rj_*F)$ and $(Y,U)$ with
$(\underline A_Y,F)$. In the notation of [lem-kun-bc-kunneth-compat], these give $k_Z$ and $k_W$,
and that node supplies the canonical module-valued Leray isomorphisms $\lambda_j,\lambda_h$ and
the precise equation $$\lambda_h\,R\Gamma(Z,\beta_A)\,k_Z=k_W(1\otimes_A^{\mathbf L}\lambda_j).$$
Every map on the right is invertible: tensoring an isomorphism sends its inverse to an inverse.
Hence $R\Gamma(Z,\beta_A)$ is invertible. This uses the canonical exchange compatibility, not
merely isomorphisms between the two cohomology objects.

10. Complete $\beta_A$ to a distinguished triangle $q^{-1}Rj_*F\to Rh_*p^{-1}F\to
Q_A\to(q^{-1}Rj_*F)[1]$. Its endpoints are bounded below, so $Q_A$ is bounded below too, by the
long exact cohomology sequence [lem-sf-derived-homology-long-exact]. Let $Q$ be its underlying
abelian derived object. Exactness and cohomology compatibility of
[lem-kun-unbounded-abelian-exchange-comparison], together with exact inverse image from Step 1,
identify $Q$ with a cone of $\beta_F$ and identify its geometric stalks with the cones of the
stalk maps. Hence Step 7 gives $Q_{\bar z}=0$ at every nonclosed point. Derived global sections
preserve distinguished triangles by [lem-pc-right-derived-functor-triangulated] applied to the
additive global-sections functor. Step 9 and the long exact sequence therefore give $H^r(Z,Q_A)=0$
for every $r$. Apply [lem-weil-pbc-derived-module-underlying-comparison] to the bounded-below
coefficient complex $Q_A$, base $T=Z$, and $p=\mathrm{id}_Z$: it identifies the underlying abelian
group of $H^r(Z,Q_A)$ with $H^r(Z,Q)$, so the latter is zero for every $r$ as well. The scheme $Z$
is finite type over the separably closed field $K$: by
[lem-weil-pbc-fibre-product-affine-spectra], products of finite-type affine charts have
tensor-product coordinate rings, generated over $K$ by the images of the two finite sets of
generators, and these charts form a finite cover. All hypotheses of [lem-kun-0f1g] now hold, so
$Q=0$. The long exact sequence and [lem-weil-pbc-derived-plus-iso-on-cohomology] make $\beta_F$
invertible. By the conservative coefficient comparison $\beta_A$ is also invertible. This
contradicts the projective counterexample, completes the induction, and Step 2 proves the
assertion for the original sheaf without a uniform annihilator. -/
theorem isIso_openProductExchange
    (K : Type u) [Field K] (U X Y : Over (Spec (.of K))) (j : U ⟶ X)
    [IsOpenImmersion j.left]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (F : Sheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsTorsionOfInvertibleOrder K U F) :
    IsIso (openProductExchange j Y F) := by
  sorry

end AlgebraicGeometry.Etale
