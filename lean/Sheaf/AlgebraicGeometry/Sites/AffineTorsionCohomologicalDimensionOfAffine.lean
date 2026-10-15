/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.AffineScheme

import Mathlib.RingTheory.NoetherNormalization
import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
import Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimensionGroundField
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension
import Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel
import Sheaf.RingTheory.FiniteTypeDomainDimensionTrdeg
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
import Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit
import Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import Sheaf.CategoryTheory.GrothendieckSpectralSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.SupportDimensionUnion
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
import Sheaf.AlgebraicGeometry.TorsionFilteredUnion
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
import WeilConjectures.AlgebraicGeometry.Sites.FieldCohomologicalDimension

/-!
# The affine torsion cohomological dimension bound

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md,
statement and proof (blueprint: thm-sc-affine-torsion-cd).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An affine finite-type scheme over a field of torsion cohomological dimension at most `c`
has torsion cohomological dimension at most its dimension plus `c` when nonempty.
For an empty scheme all nonnegative cohomology groups vanish, including degree zero.
Finite-type schemes over a field have finite Krull dimension, so `unbotD 0` followed by
`toNat` recovers the dimension in the nonempty clause.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.md,
statement and proof (blueprint: thm-sc-affine-torsion-cd).

Proof (the node's twelve steps):

1. Throughout, torsion means that every local section is locally killed by some positive integer;
no single integer need annihilate the sheaf. The cohomology is ordinary derived-section cohomology
on the small etale site, and a field bound is the corresponding bound on its affine spectrum. We
prove, by strong induction on the nonnegative integer $d$, the asserted bound for every nonempty
affine finite-type scheme of dimension at most $d$, simultaneously over all fields and all
available field bounds $c$. The empty scheme has zero section functor and hence zero cohomology.
Finite dimension follows from Noether normalization and its dimension assertion. Algebraic
extension of the ground field preserves the dimension of each affine coordinate ring. Thus after
establishing the bound $d$ over algebraically closed fields in dimension $d$, the ground-field
comparison gives $d+c$ over every field; this descent is made at each induction stage, before
advancing to $d+1$. An algebraically closed field is separably closed and has torsion bound zero.
Inputs: def-sc-etale-torsion-cd, lem-zl-noether-normalization-field,
lem-zl-noether-normalization-dimension, lem-weil-pbc-dimension-preserved-field-extension,
lem-sc-cd-ground-field, lem-sf-separably-closed-torsion-cd.

2. We will repeatedly use the following consequence for a finite morphism $u:T\to S$. Apply $u_*$
to an injective resolution of an abelian sheaf $A$. Exactness makes this a resolution of $u_*A$,
and preservation of injectives makes it an injective resolution. Since
$\Gamma(S,u_*I)=\Gamma(T,I)$ termwise, $H^r(T,A)=H^r(S,u_*A)$ for every $r$. The finite-stalk
product formula shows that $u_*A$ is torsion when $A$ is torsion, and is killed by $n$ when $A$ is
killed by $n$: a finite tuple of torsion elements has a common annihilator. Inputs:
lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-direct-image-preserves-injectives,
lemma-weil-pbc-finite-stalk-formula, def-weil-pbc-etale-cohomology.

3. For $d=0$, Noether normalization makes the structure morphism to $\operatorname{Spec}K$ finite,
so the preceding finite comparison proves the bound $c$. For $d=1$ over an algebraically closed
field the arbitrary-curve bound gives bound one, since the scheme is affine and therefore
separated; the descent in step 1 proves the bound over all fields. Now fix $d>1$ and suppose all
smaller dimensions have been proved over every field. If $\dim X<d$, the induction hypothesis
already gives the required bound; hence assume $\dim X=d$. Work first over algebraically closed
$K$. Noether normalization supplies a finite morphism $X\to\mathbf A_K^d$. The finite comparison
reduces the problem to an arbitrary torsion sheaf $M$ on $\mathbf A_K^d$. Initially suppose $nM=0$
for one positive integer $n$. Inputs: lem-zl-noether-normalization-field,
lem-zl-noether-normalization-dimension, lem-sc-arbitrary-curve-cd, lem-sc-cd-ground-field.

4. Let $Y$ be smooth integral and finite type of dimension $d$ over $K$, let $D$ be an effective
Cartier divisor (its ideal is locally generated by a nonzerodivisor,
[def-nagata-effective-cartier-ideal]), and write $j:Y\setminus D\to Y$. At $y\in D$ put
$a=\operatorname{trdeg}_K\kappa(y)$, $R=\mathcal O^{\rm sh}_{Y,\bar y}$, and choose the field
$F\subset R$ supplied by the smooth strict-local field-model lemma. A local equation $h$ of $D$ is
nonzero in the domain $R$ and belongs to its maximal ideal. For $P(T)\ne0$ in $F[T]$, write
$P(T)=T^m(b+TQ(T))$ with $b\in F^\times$. Then $b+hQ(h)$ has nonzero residue, hence is a unit of
$R$. Thus $P(h)$ is invertible in $R[1/h]$, and evaluation embeds $F(T)$ in $R[1/h]$. In
particular $h$ is transcendental over $F$. If $z_1,\ldots,z_s$ are independent over $F(h)$, a
purported nonzero relation $Q(h,z_1,\ldots,z_s)=0$ with $Q\in F[T,Z_1,\ldots,Z_s]$ can be written
$\sum_{\alpha}Q_{\alpha}(h)z^{\alpha}=0$. At least one $Q_{\alpha}$ is a nonzero polynomial, so
transcendence of $h$ makes its coefficient $Q_{\alpha}(h)$ nonzero. This is a nonzero polynomial
relation over $F(h)$, a contradiction. Thus $h,z_1,\ldots,z_s$ are independent over $F$.
Consequently $s+1\le d-a$. For every finitely generated $F(h)$-subalgebra $A\subset R[1/h]$, its
fraction field is a subfield of $\operatorname{Frac}(R)$, so the finite-type domain dimension
formula gives $\dim A\le d-a-1<d$. Inputs: lem-sc-smooth-strict-local-field-model,
lem-weil-pbc-finite-type-domain-dimension-trdeg, def-kun-transcendence-degree,
def-nagata-effective-cartier-ideal.

5. The finitely generated $F(h)$-subalgebras of $R[1/h]$ form a small filtered poset (the algebra
generated by two of them dominates both), and their union is $R[1/h]$. Taking spectra gives an
affine inverse-limit presentation with affine transition maps. The bound on $F(h)$ is one by the
one-variable field lemma. The induction hypothesis, applicable over every field and in dimensions
at most $d-a-1$, gives bound $d-a$ for each model. The affine-limit lemma therefore gives
$\operatorname{cd}_{\rm tor}(\operatorname{Spec}R[1/h])\le d-a$. The strict-henselization stalk
formula, applied to $j$, which is quasi-compact and quasi-separated: locally on the target, an
affine open where the Cartier ideal has generator $h$ has preimage the principal affine open
$D(h)$, and an open immersion is separated, gives $(R^qj_*M)_{\bar y}=0$ whenever $q>d-a$. Inputs:
lem-sc-one-variable-field-cd, lem-sc-cd-affine-limit,
prop-weil-pbc-strict-henselization-stalk-formula.

6. Put $B=\mathbf A_K^{d-1}$, $Y=\mathbf P^1_K\times B$, $D=\{\infty\}\times B$, and let
$j:\mathbf A_K^d\to Y$, $i:D\to Y$, $g:Y\to B$, and $f=gj$. These are the usual two polynomial
charts of the projective line; in the chart at infinity $D$ has equation the last coordinate. Both
polynomial charts of $Y$, and $B$ itself, are smooth over $K$ by [sbc-lem-affine-space-smooth];
smoothness is local on the source. The chart coordinate rings are domains and their nonempty
overlap is dense in each, so $Y$ is integral. In particular $Y$ has dimension $d$, and $\dim
B=d-1$ (apply the finite-type domain dimension formula to the polynomial coordinate charts, whose
variables are a transcendence basis). The projection $g$ is proper by properness of projective
space. Etale restriction preserves injective resolutions, so restriction of $R^qj_*M$ to the open
$\mathbf A^d$ is $R^q\mathrm{id}_*M=0$ for $q>0$. For any abelian etale sheaf $A$ supported on
$D$, the unit $A\to i_*i^{-1}A$ is an isomorphism: off $D$ both stalks are zero, and on $D$ the
finite-stalk formula and inverse-image stalk formula identify its stalk with the identity of
$A_{\bar y}$. Geometric stalks detect isomorphisms. Apply this to write $R^qj_*M=i_*N_q$ for
$q>0$. Inputs: lem-weil-pbc-finite-type-domain-dimension-trdeg,
lemma-nagata-projective-space-base-change-proper, lem-weil-pbc-etale-restriction-injectives,
lemma-weil-pbc-finite-stalk-formula, lemma-openclosed-stalk-upperstar,
lemma-weil-pbc-geometric-stalk-conservative, def-weil-pbc-inverse-image,
sbc-lem-affine-space-smooth.

7. For $N$ on $D$, an injective resolution $N\to I^\bullet$ stays an injective resolution under
the exact functor $i_*$, which preserves injectives. Thus $R^pg_*(i_*N)$ is computed by
$g_*i_*I^\bullet=(gi)_*I^\bullet$. Since $gi:D\to B$ is an isomorphism, this complex has no
positive cohomology. Hence $R^pg_*R^qj_*M=0$ for $p>0,q>0$. All the sheaves here are killed by
$n$: multiplication by $n$ on each derived functor value is the derived functor of
$n\mathrm{id}_M=0$, by additivity. Inputs: lemma-weil-pbc-finite-direct-image-exact,
lem-weil-pbc-direct-image-preserves-injectives.

8. View $j_*M$ as a sheaf of $\Lambda=\mathbf Z/n$-modules. Apply the first, derived, assertion of
finite-coefficient proper base change to $g$ and $(j_*M)[0]$; it applies to every object of $D^+$,
with no finiteness or constructibility condition on the stalks. Forgetting coefficients commutes
with derived direct image, including the structure morphism of each fibre. Its geometric fibres
are projective lines over algebraically closed fields. The projective-line dimension bound and the
arbitrary-curve lemma give zero fibre cohomology for $p>2$. The base-change isomorphism and
geometric stalk conservativity imply $R^pg_*j_*M=0$ for $p>2$. Inputs:
cor-weil-pbc-geometric-fiber-finite, lem-weil-pbc-exchange-forget-coefficients,
lem-weil-pbc-p1-field-dimension-one, lem-sc-arbitrary-curve-cd,
lemma-weil-pbc-geometric-stalk-conservative.

9. Direct images preserve injectives, so the Grothendieck spectral sequence applies to $j_*$
followed by $g_*$. On its $E_2$ page the only possibly nonzero positions are the column $p=0$ and
the row $q=0$ with $p\le2$. In total degree $r>2$, the term $(0,r)$ survives and is the only
graded piece of the abutment: for $2\le\ell\le r$ the outgoing differential $d_{\ell}$ targets
$(\ell,r-\ell+1)$, where both coordinates are positive; for $\ell=r+1$ it targets the zero term
$(r+1,0)$; later targets have negative second coordinate. Incoming differentials would start in a
negative first coordinate. Thus $R^rf_*M\cong g_*R^rj_*M$ for $r>2$. Write
$v=gi:D\xrightarrow{\sim}B$. The boundary identification of step 6 gives
$g_*R^rj_*M=g_*i_*N_r=v_*N_r$. At a geometric point $\bar z$ of $B$, the finite-stalk formula for
the isomorphism $v$ identifies $(v_*N_r)_{\bar z}$ with $(N_r)_{v^{-1}\bar z}$. The inverse-image
stalk formula identifies this with $(R^rj_*M)_{i v^{-1}\bar z}$. For $z\in B$ with
$a=\operatorname{trdeg}_K\kappa(z)>d-r$, the local calculation at the corresponding point of $D$
gives a zero stalk. Hence $R^rf_*M$ has zero stalks at those points. Inputs: thm-sp-grothendieck,
lem-weil-pbc-direct-image-preserves-injectives, lemma-weil-pbc-finite-stalk-formula,
lemma-openclosed-stalk-upperstar.

10. For $r=2$, let $\eta$ be the generic point of $B$. The field-model lemma applied to $B$, where
$a=\dim B=d-1$, says that its strict henselization is a regular local domain of dimension zero,
with residue field $\kappa(\eta)^{\rm sep}$. A zero-dimensional regular local ring has maximal
ideal generated by zero elements, and so is that residue field. The strict-henselization stalk
formula for the affine projection $f$ therefore identifies the generic stalk of $R^2f_*M$ with
$H^2(\mathbf A^1_{\kappa(\eta)^{\rm sep}},M|)$. By the dimension-one case, already established
over every field, and torsion cohomological dimension zero of a separably closed field, this is
zero. In the polynomial scheme $B$, the only point of residue transcendence degree $>d-2$ is its
generic point: a nonzero prime gives a nonzero polynomial relation between the $d-1$ coordinate
residues. Thus the same support bound holds for $r=2$. Inputs:
lem-sc-smooth-strict-local-field-model, prop-weil-pbc-strict-henselization-stalk-formula,
lem-sf-separably-closed-torsion-cd, def-weil-regular-scheme, def-kun-transcendence-degree.

11. Let $N$ be a torsion sheaf on $B$ with zero stalks above transcendence degree $a\ge0$. The
support-dimension-union lemma writes $N=\varinjlim_ZN_Z$ over closed $Z\subset B$ of dimension at
most $a$. Equip $Z$ with its reduced closed subscheme structure. By the stalk argument in step 6,
$N_Z=i_*i^{-1}N_Z$; by the finite comparison in step 2, $H^p(B,N_Z)=H^p(Z,i^{-1}N_Z)$. The scheme
$Z$ is affine of finite type of dimension at most $a$. When $a<d$, induction over $K$ gives zero
for $p>a$. Cohomology commutes with this filtered colimit on the qcqs scheme $B$, hence
$H^p(B,N)=0$ for $p>a$. Apply this with $N=R^qf_*M$ and $a=d-q$ for $q\ge2$ and $a\ge0$. If $a<0$,
steps 5 and 9 show every stalk vanishes, hence $N=0$. For $q=0,1$, induction on $B$ gives
$H^p(B,R^qf_*M)=0$ for $p>d-1$. Inputs: lem-sc-support-dimension-union,
lemma-weil-pbc-finite-stalk-formula, lemma-openclosed-stalk-upperstar,
lemma-weil-pbc-geometric-stalk-conservative, lemma-weil-pbc-finite-direct-image-exact,
lem-weil-pbc-direct-image-preserves-injectives, lem-weil-pbc-cohomology-filtered-colimit.

12. Apply the Grothendieck spectral sequence to $f_*$ and $\Gamma(B,-)$; direct images preserve
injectives, so the acyclicity hypothesis is satisfied. Its terms $H^p(B,R^qf_*M)$ vanish for
$p+q>d$: for $q=0,1$ use $p\le d-1$, and for $q\ge2$ use $p\le d-q$. A first-quadrant convergent
spectral sequence gives a finite filtration in each total degree, so the zero graded pieces force
$H^r(\mathbf A^d,M)=0$ for $r>d$. Finally an arbitrary locally torsion $M$, without a uniform
annihilator, is the filtered union of its subsheaves $M[n]$; each has just been treated, and
cohomology commutes with this union. The finite comparison handles the original $X$, and the
descent of step 1 completes the induction over all fields with bound $d+c$. Inputs:
thm-sp-grothendieck, lem-weil-pbc-direct-image-preserves-injectives,
lemma-weil-pbc-torsion-filtered-union, lem-weil-pbc-cohomology-filtered-colimit.
-/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_isAffine
    (K : Type u) [Field K] (c : ℕ)
    (hK : HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) c)
    (X : Scheme.{u}) [X.Over (Spec (.of K))] [IsAffine X]
    [LocallyOfFiniteType (X ↘ Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] :
    (Nonempty X → HasTorsionEtaleCohomologicalDimensionLE X
      (((topologicalKrullDim X).unbotD 0).toNat + c)) ∧
    (IsEmpty X → ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      F.IsTorsion → ∀ q : ℕ,
        Subsingleton ((AlgebraicGeometry.Etale.cohomology AddCommGrpCat.{u + 1} X q).obj
          ((DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Scheme

end
