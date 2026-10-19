/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.MonoidAlgebra.Basic

import Sheaf.AlgebraicGeometry.FsChartFreeFactorization
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Sheaf.TraceFormula.SmoothGeometricStalkAlgebra
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import Sheaf.RingTheory.StrictHenselizationNoetherian
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.RingTheory.FormalMonoidRingDimension
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.CompletionRegularLocal
import WeilConjectures.RingTheory.CompletionDimension
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian
import Sheaf.RingTheory.StrictHenselizationRegular
import Sheaf.RingTheory.StrictHenselizationDimension
import Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance
import Sheaf.TraceFormula.LogRegularDivisorialStructure
import Sheaf.AlgebraicGeometry.LogRegularPair
import Sheaf.RingTheory.FormalMonoidExtensionModel
import Sheaf.TraceFormula.FsFaceSharpening

/-!
# Log-smooth preservation of log regularity

Source: Illusie--Laszlo--Orgogozo, Exposé VI, §§1.4, 1.8--1.9
(blueprint: lem-trf-log-smooth-log-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An étale-local injective fs chart and its scheme comparison. Source: ILO VI 1.8--1.9
(blueprint: lem-trf-log-smooth-log-regular). -/
structure InjectiveFSLogChart (X Y : FineSaturatedLogScheme.{u})
    (f : EtaleLogHom X Y) where
  W : Y.scheme.Etale
  V : X.scheme.Etale
  P : Type u
  Q : Type u
  instP : CommMonoid P
  instQ : CommMonoid Q
  fineP : @IsFineSaturatedMonoid P instP
  fineQ : @IsFineSaturatedMonoid Q instQ
  chartY : P →* Y.logStructure.monoidSheaf.obj.obj (op W)
  chartX : Q →* X.logStructure.monoidSheaf.obj.obj (op V)
  g : P →* Q
  chartY_isChart : Y.logStructure.IsChart W chartY
  chartX_isChart : X.logStructure.IsChart V chartX
  map : V.left ⟶ W.left
  map_over : map ≫ W.hom = V.hom ≫ f.base
  chart_compatibility : ∀ p : P,
    f.sectionMap W V map map_over (chartY p) = chartX (g p)
  y : W.left ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of (MonoidAlgebra ℤ P)))
  x : V.left ⟶ Scheme.Spec.obj (Opposite.op (CommRingCat.of (MonoidAlgebra ℤ Q)))
  y_chart : ∀ p : P,
    y.appTop ((Scheme.ΓSpecIso
      (CommRingCat.of (MonoidAlgebra ℤ P))).inv (MonoidAlgebra.single p 1)) =
      Y.logStructure.alpha.app (op W) (chartY p)
  x_chart : ∀ q : Q,
    x.appTop ((Scheme.ΓSpecIso
      (CommRingCat.of (MonoidAlgebra ℤ Q))).inv (MonoidAlgebra.single q 1)) =
      X.logStructure.alpha.app (op V) (chartX q)
  comparison : V.left ⟶
    pullback y (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op)
  comparison_fst : comparison ≫ pullback.fst y
      (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op) = map
  comparison_snd : comparison ≫ pullback.snd y
      (Scheme.Spec.map (CommRingCat.ofHom (MonoidAlgebra.mapDomainRingHom ℤ g)).op) = x
  gp_injective :
    Function.Injective
      (Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp g))
  cokernel_torsion_free : ∀ (z : Algebra.GrothendieckGroup Q) (n : ℕ),
    0 < n → (∃ y : Algebra.GrothendieckGroup P,
      (Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp g) y) = z ^ n) →
      ∃ y : Algebra.GrothendieckGroup P,
        Algebra.GrothendieckGroup.lift ((Algebra.GrothendieckGroup.of (M := Q)).comp g) y = z

/-- An injective chart with torsion-free group cokernel and smooth or étale comparison
preserves log regularity and recovers the divisorial structure. Source: ILO VI 1.4,
1.8--1.9 (blueprint: lem-trf-log-smooth-log-regular).

Proof (the nine steps of the DAG node):

1. Work on any of the etale chart neighbourhoods in the hypothesis. If the comparison is etale, it
is smooth by [lem-weil-pbc-etale-smooth-zero-dimensional-fibres]. Apply
[lem-trf-fs-chart-free-factorization] to $g:P\to Q$, obtaining $R=P\oplus\mathbf N^r$ and an
injective $h:R\to Q$ with $h^{\rm gp}$ an isomorphism. Both $R$ and $Q$ are fs: for $R$ the finite
generation, cancellation and saturation conditions hold componentwise. This reduces the monoid
change to adjoining coordinate generators followed by extending a monoid inside its own group
completion. No injectivity on sharp characteristic monoids is asserted or needed.
Uses: lem-trf-fs-chart-free-factorization, lem-weil-pbc-etale-smooth-zero-dimensional-fibres,
def-trf-fs-log-blowup.

2. Take an affine chart $Y_0=\operatorname{Spec}C$ on the chosen base neighbourhood and put
$W=\operatorname{Spec}C[t_1,\ldots,t_r]$, with associated log chart $R=P\oplus\mathbf N^r\to C[t]$
sending $(p,(n_i))$ to $\alpha(p)\prod_i t_i^{n_i}$. This is an fs log structure by
[def-trf-fs-log-blowup]. The polynomial algebra is finite type over the Noetherian ring $C$, so
[lem-weil-pbc-finite-type-algebra-noetherian] makes $W$ locally Noetherian. Expanding finite sums
of monomials gives $\mathbf Z[R]=\mathbf Z[P][t_1,\ldots,t_r]$, and hence
$$W\times_{\operatorname{Spec}\mathbf Z[R]}\operatorname{Spec}\mathbf Z[Q]
=Y_0\times_{\operatorname{Spec}\mathbf Z[P]}\operatorname{Spec}\mathbf Z[Q]=:Z.$$ On rings the
identification sends $c\otimes[q]$ to itself, and evaluates $t_i$ as $[q_i]$; these maps are
inverse because the tensor relations already impose $t_i=[q_i]$.
Uses: def-trf-fs-log-blowup, lem-weil-pbc-finite-type-algebra-noetherian.

3. We check that $W$ is log regular. At a geometric point $\bar w$ over $\bar y$, put $A=\mathcal
O_{Y_0,\bar y}$, $B=\mathcal O_{W,\bar w}$, and let $I\subset A$ be the ideal of the nonunit base
log sections. Set $K=\{i:t_i\in\mathfrak m_B\}$, $k=|K|$, and $\rho=\operatorname{rank}\overline
M_{Y_0,\bar y}^{\rm gp}$. The associated-chart pushout in [def-trf-fs-log-blowup] shows directly
that the characteristic at $\bar w$ is $\overline M_{Y_0,\bar y}\oplus\mathbf N^K$: the other
coordinates map to units, whereas a product involving a nonunit factor cannot be a unit in a local
ring. Thus its nonunit ideal is $J=IB+(t_i:i\in K)$ and its rank is $\rho+k$. The coordinate
assertion of [lem-trf-smooth-geometric-stalk-algebra] gives flat local maps $A\to B$ and $A/I\to
B/J$ with regular closed fibres $F$ and $F_K$, where $\dim F=\dim F_K+k$. Since $A/I$ is regular,
[lem-weil-pbc-flat-over-regular-with-regular-fibre] makes $B/J$ regular. Applying
[lem-weil-pbc-flat-height-formula] to these two maps gives $$\dim B=\dim A+\dim
F=\dim(A/I)+\rho+\dim F_K+k=\dim(B/J)+\rho+k.$$ This is precisely the definition of log regularity
at $\bar w$.
Uses: def-trf-fs-log-blowup, lem-trf-smooth-geometric-stalk-algebra,
lem-weil-pbc-flat-over-regular-with-regular-fibre, lem-weil-pbc-flat-height-formula.

4. Fix a geometric point $\bar z$ of $Z$ and let $\bar w$ be its image in $W$. Set $A=\mathcal
O^{\rm sh}_{W,\bar w}$ and $Z_A=\operatorname{Spec}A\times_W Z$. The point lifts to $Z_A$ using
the chosen geometric base point. Let $B=(A\otimes_{\mathbf Z[R]}\mathbf Z[Q])_{\mathfrak q}$ at
this lift; this is an ordinary local ring over the strict local base $A$. The ring $A$ is
Noetherian by [lem-sc-strict-henselization-noetherian], and $B$ is Noetherian by
[lem-weil-pbc-finite-type-algebra-noetherian] and [lem-weil-pbc-localization-noetherian]. Put
$F=\{q:[q]\in B^\times\}$ and $G=h^{-1}(F)=\alpha^{-1}(A^\times)$; the equality holds because
$A\to B$ is local. These are faces. By [lem-trf-fs-face-sharpening], $S=R_G/G^{\rm gp}$ and
$T=Q_F/F^{\rm gp}$ are sharp fs with finite free group completions. Set $I=(\alpha(r):r\notin G)A$
and $J=([q]:q\notin F)B$. Inverting $F$ and killing its complementary monomials leaves precisely
$\mathbf Z[F^{\rm gp}]$; on the base it inverts $G$ and kills $R\setminus G$. Thus
$$B/J\cong\left((A/I)\otimes_{\mathbf Z[G^{\rm gp}]}\mathbf Z[F^{\rm gp}]\right)_{\mathfrak p},$$
with $[g]$ acting by $\alpha(g)$ and the induced prime $\mathfrak p$. The associated-stalk pushout
[def-trf-fs-log-blowup] identifies the characteristics with $S$ and $T$. The same characteristics
persist under strict henselization, since local maps reflect units.
Uses: lem-sc-strict-henselization-noetherian, lem-weil-pbc-finite-type-algebra-noetherian,
lem-weil-pbc-localization-noetherian, lem-trf-fs-face-sharpening, def-trf-fs-log-blowup.

5. Step 3 gives log regularity of $W$, so at its geometric point $\bar w$ the ring $A$ already
satisfies regularity of $A/I$ and $\dim A=\dim(A/I)+\operatorname{rank}S^{\rm gp}$. Apply
[lem-trf-log-regular-sharp-chart] to choose a chart $a:S\to A$ inducing this characteristic, and
then [lem-trf-log-regular-completed-chart]. Allow the latter's replacement of $a$ by another chart
inducing the same characteristic. It gives a monomial-compatible presentation of $\widehat A$ as
$k[[S]][[t]]$ or $V[[S]][[t]]/(\theta)$, with $\theta\equiv p$ modulo the nonzero monomials and
the parameters. The original localized chart $\alpha:R_G\to A$ and $a\circ(R_G\to S)$ lift the
same characteristic. In the associated integral log monoid their quotient is a unique unit; these
units multiply, by cancellation. Hence there is a character $\epsilon:R^{\rm gp}\to A^\times$ such
that $\alpha(r)=\epsilon(r)a(\bar r)$ for $r\in R_G$. Extending from $R_G$ to its group completion
gives the indicated domain $R^{\rm gp}$. This explicitly retains the possible unit twist rather
than assuming that the two chosen charts coincide.
Uses: def-trf-fs-log-blowup, lem-trf-log-regular-sharp-chart, lem-trf-log-regular-completed-chart.

6. The homomorphism $h:R\to Q$ has isomorphic group completions by step 1. Its inverse unit face
at $\mathfrak q$ is exactly $G$, as checked in step 4, and the completed presentation of $A$ is
compatible with the sharp chart $a$ and unit character $\epsilon$ constructed in step 5. Apply
[lem-trf-formal-monoid-extension-model]. It gives, with the same $T=Q_F/F^{\rm gp}$ and the
nonunit ideal $J$, a pair isomorphism $$(\widehat B,J\widehat
B)\cong(H,L)\quad\hbox{or}\quad(H/(\eta),L(H/(\eta))),\qquad H=D[[T]],$$ where $D$ is complete
regular local, $L$ is generated by the nonzero $T$-monomials, and in the second case
$\overline\eta\in D$ is a regular parameter. Apply [lem-trf-formal-monoid-ring-dimension]. Writing
$e=0$ in the first case and $e=1$ in the second gives $$\dim\widehat B=\dim
D+\operatorname{rank}T^{\rm gp}-e,\qquad\dim(\widehat B/J\widehat B)=\dim D-e.$$ The same node
makes the stratum quotient regular (it is $D$ or $D/(\overline\eta)$). These equalities give both
dimension bounds. No finiteness or flatness of $A\to B$, and no asserted chain of monomial primes,
is used.
Uses: lem-trf-formal-monoid-extension-model, lem-trf-formal-monoid-ring-dimension.

7. By [lem-weil-pbc-local-completion-quotient], $\widehat B/J\widehat B$ is the completion of
$B/J$. Both rings are Noetherian local, so [lem-weil-pbc-completion-regular-local] and
[lem-weil-pbc-completion-dimension] give regularity of $B/J$ and $$\dim
B=\dim(B/J)+\operatorname{rank}T^{\rm gp}.$$ The closed-immersion theorem
[lem-trf-closed-immersion-strict-localization-cartesian] identifies $B^{\rm sh}/JB^{\rm sh}$ with
$(B/J)^{\rm sh}$. By [lem-sc-strict-henselization-regular] and
[lem-sc-strict-henselization-dimension], the quotient is regular and the same dimension equality
holds for $B^{\rm sh}$. Finally [lem-trf-ind-etale-strict-local-invariance], explicitly including
arbitrary base change of the structural map of a strict localization, identifies the strict
localization of $Z_A$ at the lifted geometric point with that of $Z$ at $\bar z$. Thus $B^{\rm
sh}=\mathcal O_{Z,\bar z}$ canonically; the identification is over $Z$ and preserves each chart
monomial and its nonunit ideal. The characteristic remains $T$ by step 4 and
[def-trf-fs-log-blowup]. This proves log regularity of the $Q$-chart on $Z$. If the chart base
change is empty there are no points to check.
Uses: lem-weil-pbc-local-completion-quotient, lem-weil-pbc-completion-regular-local,
lem-weil-pbc-completion-dimension, lem-trf-closed-immersion-strict-localization-cartesian,
lem-sc-strict-henselization-regular, lem-sc-strict-henselization-dimension, def-trf-fs-log-blowup,
lem-trf-ind-etale-strict-local-invariance.

8. The comparison $c:X_0\to Z$ is smooth by hypothesis and step 1. Its log structure is the
pullback of the associated $Q$-chart: both structures are obtained by associating a log structure
to that same chart, and the universal pushout defining associated stalks gives the identification.
At a geometric point of $X_0$ over one of $Z$, write $A=\mathcal O_{Z,\bar z}$, $B=\mathcal
O_{X_0,\bar x}$, and $I\subset A$ for the nonunit log ideal. A local ring map has inverse image of
the units equal to the units; hence the associated-stalk pushout identifies the two
characteristics, of rank $\rho$, and the source nonunit ideal is $IB$. By
[lem-trf-smooth-geometric-stalk-algebra], $A\to B$ and $A/I\to B/IB$ are flat local maps with the
same regular closed fibre $F$. Log regularity of $Z$ gives regular $A/I$ and $\dim
A=\dim(A/I)+\rho$. Now [lem-weil-pbc-flat-over-regular-with-regular-fibre] makes $B/IB$ regular,
while two applications of [lem-weil-pbc-flat-height-formula] give $$\dim B=\dim A+\dim
F=\dim(A/I)+\rho+\dim F=\dim(B/IB)+\rho.$$ Thus $X_0$ is log regular. The charts cover the
geometric points of $X$, so the geometric-stalk definition gives log regularity of $X$ itself.
Uses: def-trf-fs-log-blowup, lem-trf-smooth-geometric-stalk-algebra,
lem-weil-pbc-flat-over-regular-with-regular-fibre, lem-weil-pbc-flat-height-formula.

9. Apply [lem-trf-log-regular-divisorial-structure] to the locally Noetherian fs log regular
scheme just obtained. Its triviality locus $U$ is open dense and the structural map identifies
$M_X$ with $\mathcal O_X\cap j_*\mathcal O_U^\times$. Put $D=X\setminus U$. This identification
gives exactly the divisorial log structure of [def-trf-log-regular-pair]; it is fs, log regular,
and has triviality locus exactly $U$. Consequently $(X,D)$ is a log regular pair, including the
empty-scheme and empty-boundary cases.
Uses: lem-trf-log-regular-divisorial-structure, def-trf-log-regular-pair.
-/
theorem logSmooth_logRegular
    (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
    (hY : Y.IsLogRegular)
    (hcharts : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ c : InjectiveFSLogChart X Y f,
        Nonempty ((Scheme.pointSmallEtale t).fiber.obj c.V) ∧
          (Smooth c.comparison ∨ Etale c.comparison)) :
    X.IsLogRegular ∧
      ∃ (U : X.scheme.Opens) (hd : DenseRange U.ι),
        X.logStructure.trivialityLocus = (U : Set X.scheme) ∧
        Presheaf.IsSheaf X.scheme.smallEtaleTopology (divisorialLogPresheaf U.ι) ∧
        (∃ e : X.logStructure.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
          e.hom ≫ divisorialStructuralMap U.ι = X.logStructure.alpha) ∧
        @IsDivisorialFineSaturatedLogRegularPair X.scheme U.toScheme U.ι
          inferInstance X.locallyNoetherian hd := by
  sorry

end AlgebraicGeometry
