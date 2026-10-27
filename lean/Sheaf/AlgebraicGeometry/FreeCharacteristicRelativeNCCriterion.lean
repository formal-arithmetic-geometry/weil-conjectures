/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.SmoothStrictNormalCrossingsDivisor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.AlgebraicGeometry.AssociatedLogUniversalStalks
import Sheaf.AlgebraicGeometry.LogDifferentialStalk
import WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale
import Sheaf.AlgebraicGeometry.LogCotangentComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.DimensionAtPointLocalRingTrdeg
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.LogSmoothLogRegular
import Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource
import Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates
import WeilConjectures.RingTheory.RegularSequenceConormal
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Free characteristic and relative normal crossings

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, VI 1.4--1.8, pp.69--70;
X Proposition 1.2, pp.136--139, and Lemma 2.2, p.149; VIII Remark 4.2.2(i), p.118
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion).

The two predicates below are the conditions of this criterion. The log-smooth condition
uses the existing fs log morphisms: it existentially presents the divisorial structure,
identified by its actual structural map, and the trivial base structure. These are
presentations of the prescribed structures, not extra hypotheses on the pair. The map
from the trivial log base is forced by compatibility with pullback of regular functions.
The chart structure records the actual coordinate morphism and divisorial chart.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Condition (a): the divisorial log structure has the specified triviality locus,
is fs and log smooth over the trivial log field, and has finite free characteristic.
The isomorphism and its structural compatibility fix the divisorial structure exactly;
triviality everywhere fixes the base log structure. Source: ILO VI 1.4--1.8; X 1.2
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion). -/
noncomputable def IsFreeCharacteristicLogSmoothDivisorialPair
    {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (.of F))
    (U : X.Opens) : Prop :=
  ∃ (hX : IsLocallyNoetherian X) (M : EtaleLogStructure X)
    (hM : M.IsFineSaturated),
    (∃ e : M.monoidSheaf.obj ≅ divisorialLogPresheaf U.ι,
      e.hom ≫ divisorialStructuralMap U.ι = M.alpha) ∧
    M.trivialityLocus = (U : Set X) ∧
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
      ∃ r : ℕ, Nonempty (M.characteristic t ≃* Multiplicative (Fin r → ℕ))) ∧
    ∃ (hF : IsLocallyNoetherian (Spec (.of F)))
      (N : EtaleLogStructure (Spec (.of F))) (hN : N.IsFineSaturated)
      (g : EtaleLogHom ⟨X, hX, M, hM⟩ ⟨Spec (.of F), hF, N, hN⟩),
      N.trivialityLocus = Set.univ ∧ g.base = f ∧ g.IsLogSmooth

/-- One pointed chart in (b). Its product equation is equality of ideal sheaves, so
it specifies the reduced induced scheme structure, not merely equality of supports.
The chart condition is tested on the prescribed divisorial geometric stalks.
Source: ILO VI 1.1, 1.4, 1.6; X 1.2, pp.136--138
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion). -/
structure RelativeNormalCrossingsChart
    {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (.of F))
    (U : X.Opens) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X) where
  W : X.Etale
  point : (Scheme.pointSmallEtale t).fiber.obj W
  r : ℕ
  comparison : W.left ⟶ AffineSpace (ULift.{u} (Fin r)) (Spec (.of F))
  over : comparison ≫ (AffineSpace (ULift.{u} (Fin r)) (Spec (.of F)) ↘ Spec (.of F)) =
    W.hom ≫ f
  smooth : Smooth comparison
  chart : Multiplicative (ULift.{u} (Fin r) → ℕ) →* divisorialSections U.ι W
  coordinates : ∀ i : ULift.{u} (Fin r),
    (chart (Multiplicative.ofAdd (Pi.single i 1))).1 =
      comparison.appTop (AffineSpace.coord (Spec (.of F)) i)
  isChart : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω'] (t' : Spec (.of Ω') ⟶ X)
    (w' : (Scheme.pointSmallEtale t').fiber.obj W),
    ∃ h : IsUnit.submonoid (strictLocalRing X t') ≤ divisorialStalk U.ι t',
      IsDivisorialStalkChart (divisorialStalk U.ι t') h
        ((divisorialGerm U.ι t' W w').comp chart)
  boundary :
    Scheme.IdealSheafData.vanishingIdeal
      ⟨((W.hom ⁻¹ᵁ U : W.left.Opens) : Set W.left)ᶜ,
        (W.hom ⁻¹ᵁ U).isOpen.isClosed_compl⟩ =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.span {∏ i : ULift.{u} (Fin r),
          comparison.appTop (AffineSpace.coord (Spec (.of F)) i)})

/-- The scheme-theoretic intersection of a subset of the coordinate branches of a
relative chart, using the actual pullbacks of the affine coordinates. The empty subset
cuts out the whole neighbourhood. Source: ILO VIII Remark 4.2.2(i); X 1.2
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion). -/
noncomputable def RelativeNormalCrossingsChart.intersectionIdeal
    {F : Type u} [Field F] {X : Scheme.{u}} {f : X ⟶ Spec (.of F)}
    {U : X.Opens} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {t : Spec (.of Ω) ⟶ X} (C : RelativeNormalCrossingsChart f U t)
    (s : Finset (ULift.{u} (Fin C.r))) : C.W.left.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.span {a | ∃ i ∈ s, a = C.comparison.appTop (AffineSpace.coord (Spec (.of F)) i)})

/-- Condition (b): the smooth coordinate charts exist at every geometric point.
No global labelling or irreducibility of the coordinate branches is imposed.
Source: ILO X 1.2 and Lemma 2.2, p.149
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion). -/
def HasRelativeNormalCrossingsCharts
    {F : Type u} [Field F] {X : Scheme.{u}} (f : X ⟶ Spec (.of F))
    (U : X.Opens) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
    Nonempty (RelativeNormalCrossingsChart f U t)

/-- The free-characteristic criterion, with pointed charts, log regularity, ordinary
smoothness, all branch intersections of the expected pure codimension, and the relative
strict normal crossings converse. No perfection hypothesis is imposed.
Source: ILO VI 1.4--1.8; X Proposition 1.2, pp.136--139, Lemma 2.2, p.149;
VIII Remark 4.2.2(i), p.118
(blueprint: lem-sfb-free-characteristic-relative-nc-criterion).

Proof plan (the eleven steps of the DAG node):

1. All constructions are local near the chosen geometric point. The finite-type hypothesis makes
   $X$ Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since a field is Noetherian.
   Assume (a). The trivial log field is log regular: its log ideal is zero, its local ring is a
   field and its characteristic has rank zero. Apply [lem-sfb-log-smooth-preserves-log-regularity]
   to obtain log regularity of $(X,M)$. Now [lem-trf-log-regular-sharp-chart] gives an affine
   pointed etale neighbourhood $V$ and a chart by $P=\overline M_{\bar x}\simeq\mathbf N^r$
   inducing the specified characteristic at $\bar x$. Write $t_i$ for the images of its basis.
   Each $t_i$ is a nonunit at $\bar x$, so each branch contains that point. The chart gives the
   $F$-morphism $c=(t_1,\ldots,t_r):V\to\mathbf A^r_F$. Log smoothness remains valid on $V$ by the
   strict-etale locality of [lem-sfb-log-smooth-composition-strict-base-change].
   Uses: lem-weil-pbc-finite-type-over-noetherian, lem-sfb-log-smooth-preserves-log-regularity,
   lem-trf-log-regular-sharp-chart, lem-sfb-log-smooth-composition-strict-base-change.

2. Give $T=\mathbf A^r_F$ the associated log structure of $\mathbf N^r\to F[z_1,\ldots,z_r]$,
   $e_i\mapsto z_i$, using [lem-trf-associated-log-universal-stalks]. Its structural map to the
   trivial log field is log smooth by [def-per-fs-log-smooth-etale]: the chart is $0\to\mathbf
   N^r$, its group map has zero kernel and torsion-free cokernel, and its comparison is the
   identity. The source chart identifies $M|_V$ with the pullback of this log structure, so $c$ is
   strict. From [def-per-log-differential-stalk] the polynomial logarithmic differential module is
   free on $d\log z_i$: the relations give $dz_i=z_i d\log z_i$, and an inverse sends $d\log z_i$
   to $e_i$ and $df$ to $\sum_i z_i(\partial f/\partial z_i)e_i$. For a unit $u$ its logarithmic
   image must be $u^{-1}du$. The same calculation holds on etale neighbourhoods: [lem-weil-pbc-
   flat-unramified-formally-etale] gives a unique lift across the square-zero algebra $B\oplus
   B^r$ of the identity of any etale algebra $B$, with polynomial structure $f\mapsto(f,\sum_i
   z_i\partial_i f\,e_i)$. Its second component is the unique extending derivation. These
   extensions commute with etale restrictions by uniqueness, and passing to the geometric-stalk
   colimit gives the inverse there too. Thus the logarithmic differential fibre of $T/F$ at every
   geometric point is freely generated by the $d\log z_i$.
   Uses: lem-trf-associated-log-universal-stalks, def-per-fs-log-smooth-etale, def-per-log-
   differential-stalk, lem-weil-pbc-flat-unramified-formally-etale.

3. Put $k=\kappa(\bar x)$. Apply [lem-sfb-log-cotangent-characteristic-quotient] to $V$ over the
   trivial log field. Its surjection $k\otimes\omega_{V/F}\twoheadrightarrow k\otimes_{\mathbf
   Z}\overline M_{\bar x}^{\rm gp}=k^r$ sends $d\log t_i$ to the $i$th basis vector. Hence the map
   from the logarithmic differential fibre of $T/F$ to that of $V/F$ is injective: a relation
   among its basis images maps to the same relation among the basis vectors of $k^r$. Both log
   schemes are log smooth over the same base, and $c$ is strict. Thus [lem-sfb-strict-log-
   jacobian-criterion] makes $c$ smooth on a neighbourhood of $\bar x$. Shrink $V$ to this
   neighbourhood. No separability or perfection assumption on $F$ was used.
   Uses: lem-sfb-log-cotangent-characteristic-quotient, lem-sfb-strict-log-jacobian-criterion,
   def-per-log-cotangent-comparison.

4. Record the geometry of any smooth comparison $c:V\to\mathbf A^r_F$. For
   $J\subseteq\{1,\ldots,r\}$, put $T_J=V(z_i:i\in J)$ and $V_J=V(t_i:i\in J)$. Then
   $T_J\simeq\mathbf A^{r-|J|}_F$ and $V_J=V\times_TT_J$ scheme-theoretically. Work locally where
   $c$ has constant relative dimension $d$, using [sbc-lem-smooth-relative-dimension-locally-
   constant]. By [sbc-lem-affine-space-smooth] and [lem-sbc-smooth-relative-dimension-permanence],
   $V_J\to T_J$ is smooth of relative dimension $d$, $V_J/F$ is smooth of relative dimension
   $d+r-|J|$, and $V/F$ is smooth of relative dimension $d+r$. To verify pure codimension, work on
   a finite-type affine neighbourhood of a generic point $\eta$ of an irreducible component of
   $V_J$. The local ring of $V_J$ at $\eta$ has dimension zero. Apply [lem-weil-pbc-dimension-at-
   point-local-ring-trdeg] to this affine intersection and to the ambient affine neighbourhood at
   the same point: the residue fields agree, so subtraction gives $\dim\mathcal O_{V,\eta}=|J|$.
   This is exactly the height of the prime of that component in the ambient affine ring.
   Consequently every nonempty $V_J$ is smooth of the expected pure codimension $|J|$.
   Uses: sbc-lem-affine-space-smooth, sbc-lem-smooth-relative-dimension-locally-constant, lem-sbc-
   smooth-relative-dimension-permanence, lem-weil-pbc-dimension-at-point-local-ring-trdeg.

5. The scheme $V$ and all the $V_J$ of Step 4 are regular by [lem-weil-pbc-smooth-scheme-over-
   field-regular]. At a point $v$, discard the $t_i$ which are units in $R=\mathcal O_{V,v}$. Each
   remaining quotient $R/(t_i)$ is a regular local ring, hence a domain by [lem-sc-regular-local-
   domain]; thus $(t_i)$ is prime. Two of these prime ideals cannot be equal: their common zero
   scheme would then have codimension one, whereas Step 4 gives codimension two for their
   intersection. Consequently the nonunit $t_i$ are pairwise nonassociated prime elements in the
   domain $R$. If a power of $f$ is divisible by $\prod t_i$, primality makes every $t_i$ divide
   $f$; successive cancellation and pairwise nonassociation make their product divide $f$.
   Therefore $(\prod t_i)$ is radical. Its zero scheme is reduced, including the empty product
   case, and has support the union of the coordinate branches.
   Uses: lem-weil-pbc-smooth-scheme-over-field-regular, lem-sc-regular-local-domain.

6. In a chart by $\mathbf N^r$, the characteristic at any point is obtained by discarding exactly
   the basis elements whose images are units: if a monomial is a unit in a local ring then each of
   its factors is a unit. Thus it is $\mathbf N^s$ for the number $s$ of vanishing coordinates,
   and the triviality locus is $D(t_1\cdots t_r)$. Under (a) this locus is $U\times_XV$ by the
   added triviality-locus requirement. Step 5 now identifies the reduced closed subscheme on
   $B\times_XV$ with $V(t_1\cdots t_r)$, proving (b). Conversely, given (b), the chart makes $M$
   fs, gives precisely these free characteristic monoids, and has triviality locus $U$. The
   compatible charts $0\to\mathbf N^r$ have zero kernel and torsion-free group cokernel; their
   comparison is exactly the assumed smooth $c$. Hence [def-per-fs-log-smooth-etale] gives (a).
   Its etale-local formulation applies on the covering neighbourhoods. All coordinates in the
   (a)-to-(b) construction vanish at the distinguished point by Step 1.
   Uses: def-trf-fs-log-blowup, def-per-fs-log-smooth-etale.

7. The trivial log field is log regular: its nonunit log ideal is zero, its local ring is a field
   of dimension zero, and its characteristic has rank zero. On the charts just proved,
   $0\to\mathbf N^r$ has injective group map and torsion-free cokernel. Apply [lem-trf-log-smooth-
   log-regular] to these charts to obtain log regularity of $(X,M)$; its recovered divisorial
   structure and its triviality locus agree with the specified pair by Step 6. Also $V/F$ is
   smooth by Step 4, so smoothness descends along the etale covering $V\to X$ by [lem-trf-etale-
   source-smoothness]. Step 4 already proves the asserted smoothness and expected codimensions for
   all local branch intersections. Thus either condition gives all the stated consequences.
   Uses: lem-trf-log-smooth-log-regular, lem-trf-etale-source-smoothness.

8. For the final converse, suppose $X/F$ is smooth and $D=B_{\rm red}$ is a relative strict normal
   crossings divisor as defined in [def-trf-smooth-strict-normal-crossings-divisor]. Fix $x$.
   Delete the finitely many components not containing $x$; call the remaining ones
   $C_1,\ldots,C_r$. Each $C_i$ is smooth of codimension one, and $Z=\bigcap_i C_i$ is smooth of
   pure codimension $r$. Apply [lem-pur-smooth-pair-local-coordinates] separately to
   $C_i\hookrightarrow X$ to obtain a local generator $t_i$ of its ideal. In its coordinate chart
   the regular sequence has length one: at a generic point of $C_i$ the ambient local ring has
   dimension one and the quotient dimension zero, so [lem-trf-regular-sequence-dimension-formula]
   forces this length to be one. Shrink to a common affine neighbourhood, with
   $I_Z=(t_1,\ldots,t_r)$. Apply the same smooth-pair coordinate lemma to $Z\hookrightarrow X$:
   its ideal is locally generated by a coordinate regular sequence of some fixed length $b$. At a
   generic point of a component of $Z$ meeting this neighbourhood, the ambient local dimension is
   $r$ by pure codimension and the quotient local dimension is zero. Again [lem-trf-regular-
   sequence-dimension-formula] gives $b=r$. Hence [lem-weil-pbc-regular-sequence-conormal-free]
   gives a locally free conormal module of rank $r$ on this neighbourhood of $x$. The specified
   $r$ generators $t_i$ therefore form a basis of its fibre $(I/I^2)\otimes\kappa(x)$, where
   $I=I_{Z,x}\subset\mathcal O_{X,x}$.
   Uses: def-trf-smooth-strict-normal-crossings-divisor, lem-pur-smooth-pair-local-coordinates,
   lem-trf-regular-sequence-dimension-formula, lem-weil-pbc-regular-sequence-conormal-free.

9. Apply [lem-pur-conormal-sequence-smooth-immersion] to $Z\hookrightarrow X$ over $F$; its
   hypothesis is the smoothness of $Z/F$, not perfection of $F$. Its injective first arrow sends
   the conormal basis from Step 8 to $dt_1,\ldots,dt_r$. Thus these differentials are independent
   in $\Omega_{X/F,x}\otimes\kappa(x)$. On the affine finite-type neighbourhood the differentials
   of finitely many algebra generators span this vector space, by the defining Leibniz relations.
   Extend the independent $dt_i$ to a basis by selecting differentials $dg_1,\ldots,dg_s$ from
   that spanning family. Now [lem-pur-etale-at-point-from-differentials] makes
   $h=(t_1,\ldots,t_r,g_1,\ldots,g_s):V\to\mathbf A^{r+s}_F$ etale after shrinking. The projection
   $\mathbf A^{r+s}_F\to\mathbf A^r_F$ is the affine $s$-space projection over $\mathbf A^r_F$, so
   it is smooth by [sbc-lem-affine-space-smooth]. Etale maps are smooth by [def-sbc-smooth-
   morphisms]. Their composite $c=(t_i)$ is smooth by [lem-trf-smooth-composition].
   Uses: lem-pur-conormal-sequence-smooth-immersion, lem-pur-etale-at-point-from-differentials,
   sbc-lem-affine-space-smooth, def-sbc-smooth-morphisms, lem-trf-smooth-composition.

10. On the resulting neighbourhood construct $L$ from the prelog chart $\mathbf N^r\to\mathcal O$,
   $e_i\mapsto t_i$, using [lem-trf-associated-log-universal-stalks]. Its characteristic at a
   point is $\mathbf N^s$ for the vanishing coordinates, and its triviality locus is $D(\prod
   t_i)=X\setminus B$ on this neighbourhood. The $0\to\mathbf N^r$ comparison is the smooth map of
   Step 9, so [lem-trf-log-smooth-log-regular] applies over the trivial log field. In addition to
   log regularity, its statement canonically identifies $L$ with $\mathcal O\cap j_*\mathcal
   O_U^\times$, which is precisely the specified $M$. Thus $\mathbf N^r$ is a chart for $M$. Steps
   4--5 show that $V(\prod t_i)$ is reduced; its support is the union of the chosen component
   supports, namely $B$ here. By uniqueness of the reduced induced closed subscheme it equals $D$
   on this neighbourhood. We have proved (b), and Step 6 gives (a).
   Uses: lem-trf-associated-log-universal-stalks, lem-trf-log-smooth-log-regular, lem-weil-pbc-
   reduced-induced-closed-subscheme.

11. If $r=0$, all products are $1$, all intersections with the empty index set are $V$, the
   characteristic is zero, and the comparison is the smooth structural map to $\mathbf
   A^0_F=\operatorname{Spec}F$. This handles $B=\varnothing$ and points outside the boundary.
   Nothing chooses global labels for branches, so distinct local branches may belong to one global
   component. All field-dependent inputs above assume only that $F$ is a field and use actual
   smoothness of the intersections, so the argument applies unchanged to imperfect fields.
   Uses: def-sbc-affine-space.
-/
theorem free_characteristic_relative_nc_criterion
    {F : Type u} [Field F] (X : Scheme.{u}) [X.Over (Spec (.of F))]
    [LocallyOfFiniteType (X ↘ Spec (.of F))] [QuasiCompact (X ↘ Spec (.of F))]
    (U : X.Opens) (hU : Dense (U : Set X)) :
    (IsFreeCharacteristicLogSmoothDivisorialPair (X ↘ Spec (.of F)) U ↔
      HasRelativeNormalCrossingsCharts (X ↘ Spec (.of F)) U) ∧
    (HasRelativeNormalCrossingsCharts (X ↘ Spec (.of F)) U →
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X),
        ∃ C : RelativeNormalCrossingsChart (X ↘ Spec (.of F)) U t,
          ∀ i : ULift.{u} (Fin C.r), C.point.left (default : Spec (.of Ω)) ∈
            C.W.left.zeroLocus {C.comparison.appTop (AffineSpace.coord (Spec (.of F)) i)}) ∧
    ((IsFreeCharacteristicLogSmoothDivisorialPair (X ↘ Spec (.of F)) U ∨
      HasRelativeNormalCrossingsCharts (X ↘ Spec (.of F)) U) →
      (∃ hX : IsLocallyNoetherian X,
        @IsDivisorialFineSaturatedLogRegularPair X U.toScheme U.ι inferInstance hX
          (by simpa only [DenseRange, Scheme.Opens.range_ι] using hU)) ∧
      Smooth (X ↘ Spec (.of F)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X)
        (C : RelativeNormalCrossingsChart (X ↘ Spec (.of F)) U t)
        (s : Finset (ULift.{u} (Fin C.r))),
        Smooth ((C.intersectionIdeal s).subschemeι ≫ C.W.hom ≫ (X ↘ Spec (.of F))) ∧
        ∀ (V : C.W.left.affineOpens) (p : Ideal Γ(C.W.left, V.1)),
          p ∈ ((C.intersectionIdeal s).ideal V).minimalPrimes →
            p.height = (s.card : ℕ∞)) ∧
    (Smooth (X ↘ Spec (.of F)) →
      (Scheme.IdealSheafData.vanishingIdeal
        ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩).IsSmoothStrictNormalCrossingsDivisor
          (X ↘ Spec (.of F)) →
      IsFreeCharacteristicLogSmoothDivisorialPair (X ↘ Spec (.of F)) U ∧
        HasRelativeNormalCrossingsCharts (X ↘ Spec (.of F)) U) := by
  sorry

end AlgebraicGeometry
