/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.Dimension
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import WeilConjectures.Blowup.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.Blowup.Affine.ChartAlgebra
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.FlatBaseChange
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.AlgebraicGeometry.BlowupChartRegularSequencePresentation
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.RingTheory.RegularLocalLiftRegularSequenceQuotient
import WeilConjectures.Blowup.Complement
import WeilConjectures.Compactification.StrictTransformBlowup
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.KrullDimension.Polynomial
import Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry

/-!
# Blowing up a closed point on a regular surface

Source: Stacks Project, Resolution of Surfaces, Tags 0AGQ, 0AGR and the opening of
Tag 0BIC; Divisors, Tags 02ND, 02NS and 080E; Morphisms, Tags 087S and 0892;
More on Algebra, Tag 07QU (blueprint: lem-per-surface-point-blowup-geometry).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The blowup of a reduced closed point on an integral regular excellent Noetherian
surface preserves those properties, dimension two, and existence of an ample invertible
module. Its exceptional fibre is the projective line over the residue field. Total
supports and strict transforms of closed subschemes have the stated descriptions.

The ideal `I` is constrained to be the kernel of the canonical residue-field point map,
so the centre has its reduced scheme structure. Closed subschemes are represented by
quasi-coherent ideal sheaves; the support of their total transform is the support of
the pulled-back ideal's quotient. The exceptional fibre is a scheme fibre product,
and its isomorphism with the projective line commutes with the maps to the residue field.

Source: Stacks Project, Tags 0AGQ, 0AGR, 0BIC, 02ND, 02NS, 080E, 087S, 0892 and 07QU
(blueprint: lem-per-surface-point-blowup-geometry).

Proof plan, following the ten steps of the node:
1. Let $\mathcal I$ be the ideal sheaf of the reduced closed point $p$. The closed-immersion
   ideal-sheaf description makes it quasi-coherent. On an affine $\operatorname{Spec}R$ containing
   $p$ it is the maximal ideal of $p$, and on an affine not containing $p$ it is the unit ideal.
   Each is finitely generated because $R$ is Noetherian; thus $\mathcal I$ is of finite type. It
   is nonzero: at $p$, its stalk is the maximal ideal of the two-dimensional regular local ring,
   which cannot be zero (a field has dimension zero).
   Uses: def-sbc-closed-immersion-ideal-sheaf, def-weil-pbc-noetherian-ring, pqf-def-coherent,
   def-weil-regular-scheme.
2. Apply the integral finite-type blowup theorem to $(X,\mathcal I)$: $X\prime$ is integral and
   $b$ is projective in the projective-bundle sense. Since $X$ has an ample invertible sheaf, the
   projective-bundle-to-H-projective theorem gives a closed immersion into a finite projective
   space over $X$, as required. The blowup properness theorem makes $b$ proper, hence of finite
   type by the definition of properness. Finite type over the Noetherian scheme $X$ makes
   $X\prime$ Noetherian. On an excellent affine open $\operatorname{Spec}R\subseteq X$, choose
   finite generators of the centre ideal $I$. Each blowup chart has ring $R[I/a]$, generated over
   $R$ by the finitely many fractions $i/a$ from those generators. These rings, and their
   localizations, are excellent by finite-type stability of excellent rings. Hence $X\prime$ is
   excellent.
   Uses: lem-per-integral-blowup-projective-geometry, lem-trf-projective-bundle-to-h-projective,
   lemma-nagata-blowup-proper, def-weil-proper-morphism, lem-weil-pbc-finite-type-over-noetherian,
   lem-exc-finite-type-localization-excellent, def-nagata-blowup-chart-ring, prop-nagata-affine-
   blowup-chart.
3. Choose an ample invertible module $M$ on $X$. By step 2 (the integral finite-type blowup
   theorem) $b$ is projective in the projective-bundle sense. The theorem that a projective-
   bundle-projective morphism is quasi-projective therefore supplies an invertible $\mathcal
   O_{X\prime}$-module $N$ that is $b$-relatively ample: $b$ is quasi-compact and $N|_{b^{-1}(V)}$
   is ample for every affine open $V\subseteq X$. These are exactly the hypotheses of the
   relative-to-absolute twisting theorem for $f=b$, together with the ample module $M$ on $X$; it
   gives an integer $a\geq0$ for which $N\otimes b^*(M^{\otimes a})$ is ample on $X\prime$. This
   constructs the ample module needed for the next blowup; no ampleness of $b^*M$ alone is
   asserted.
   Uses: lem-per-integral-blowup-projective-geometry, lem-per-projective-bundle-relative-ample,
   lem-per-relative-ample-absolute-twist.
4. Put $A=\mathcal O_{X,p}$, with maximal ideal $\mathfrak m$ and residue field $k=\kappa(p)$.
   Choose an affine neighbourhood $\operatorname{Spec}R$ of $p$ corresponding to a maximal ideal
   $\mathfrak n$, so $A=R_{\mathfrak n}$. Localization is flat, and flat base change of blowups
   identifies $B=\operatorname{Bl}_{\mathfrak m}(\operatorname{Spec}A)$ with
   $X\prime\times_X\operatorname{Spec}A$. This preserves the fibre over $p$, and every local ring
   at a point of that fibre: on an affine chart with ring $C$, the base change replaces $C$ by
   $(R\setminus\mathfrak n)^{-1}C$. A prime $\mathfrak q$ over $\mathfrak n$ avoids these
   denominators, so $((R\setminus\mathfrak n)^{-1}C)_{\mathfrak q}=C_{\mathfrak q}$. Thus it
   suffices to compute $B$ along its closed fibre.
   Uses: lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-flat, thm-nagata-
   blowup-flat-base-change.
5. Since $A$ is regular local of dimension two, choose generators $x,y$ of $\mathfrak m$. Both
   orders $(x,y)$ and $(y,x)$ are regular sequences. The blowup chart isomorphisms and the
   regular-sequence presentation give the covering charts $C_x=A[\mathfrak m/x]=A[t]/(xt-y)$ and
   $C_y=A[\mathfrak m/y]=A[u]/(yu-x)$. These charts cover because $x,y$ in degree one generate the
   Rees algebra. In the first chart $\mathfrak m C_x=(x)$, and in the second $\mathfrak m
   C_y=(y)$. Multiplication by the chart generator is injective: $C_x\subseteq A_x$ and $x$ is a
   unit in $A_x$, and likewise for $y$. This proves the local nonzerodivisor assertion directly,
   without assuming regularity of the blowup.
   Uses: def-weil-regular-scheme, lem-weil-pbc-regular-local-generators-regular-sequence, def-
   nagata-affine-blowup, def-nagata-affine-blowup-chart-map, prop-nagata-affine-blowup-chart, def-
   nagata-blowup-chart-ring, lem-trf-blowup-chart-regular-sequence-presentation.
6. The closed fibre on these charts has coordinate rings $C_x/(x)=k[t]$ and $C_y/(y)=k[u]$. On
   their overlap $t=y/x$ is invertible and $u=x/y=t^{-1}$. The standard projective-space chart
   theorem identifies exactly this gluing with $\mathbf P^1_k$, so $E\cong\mathbf P^1_k$ as
   schemes, not just as sets. The polynomial ring over a field is regular; hence all local rings
   of $E$, being the prime localizations on these two charts, are regular local. Thus $E$ is
   regular.
   Uses: lem-weil-pbc-projective-space-standard-charts, lem-weil-pbc-polynomial-ring-field-
   regular-ring, def-weil-regular-scheme.
7. Let $q$ lie on $E$. By the local-ring comparison above, $\mathcal O_{X\prime,q}$ is a prime
   localization of $C_x$ or $C_y$. It is Noetherian, since $X\prime$ is Noetherian. The
   appropriate chart generator $g=x$ or $y$ belongs to its maximal ideal and is a nonzerodivisor,
   and the quotient by $g$ is $\mathcal O_{E,q}$, regular local by the preceding step. Apply
   regularity lifting from a regular-sequence quotient with the sequence $(g)$. Away from $E$, the
   blowup-complement isomorphism identifies local rings with those of the regular scheme $X$. All
   local rings of $X\prime$ are therefore regular local, so $X\prime$ is regular.
   Uses: lem-exc-regular-local-lift-regular-sequence-quotient, thm-nagata-global-blowup-
   complement, def-weil-regular-scheme, lem-weil-pbc-localization-noetherian.
8. For $q\in E$, the dimension formula for a local quotient by one nonzerodivisor gives
   $\dim\mathcal O_{X\prime,q}=1+\dim\mathcal O_{E,q}$. Since $E$ is covered by spectra of $k[t]$,
   whose Krull dimension is one, these local dimensions are at most two. At the point $t=0$ the
   localization $k[t]_{(t)}$ has dimension one: $(0)\subsetneq(t)$ gives a chain of length one and
   the global dimension bounds it above. Thus one local ring of $X\prime$ has dimension two. Off
   $E$ all local dimensions are at most $\dim X=2$ by the complement isomorphism. Taking the
   supremum of all local-ring dimensions proves $\dim X\prime=2$.
   Uses: lem-weil-pbc-dimension-quotient-nonzerodivisor, lem-sf-noetherian-polynomial-dimension,
   def-pc-dimension, thm-nagata-global-blowup-complement.
9. Let $W\subseteq X$ be closed and contain $p$, and put $U=X\setminus\{p\}$. The strict transform
   is a closed subscheme of $W\times_X X\prime$ and agrees with that fibre product over $U$. The
   support of $W\times_X X\prime$ is $b^{-1}(|W|)$: locally, an ideal $J$ defining $W$ lies in the
   prime of a point upstairs exactly when its image lies in that prime, equivalently when the
   contracted prime lies in $V(J)$. Consequently $E=b^{-1}(p)$ lies in this support. Every point
   of the support outside $E$ is in the strict transform by the agreement over $U$, while the
   strict transform itself lies in the support of the fibre product. These two inclusions prove
   the asserted union, including when $W=p$ or $W=X$.
   Uses: def-nagata-strict-transform, lemma-nagata-strict-transform-restrict, def-weil-closed-
   immersion.
10. For an integral closed subscheme $Y\subseteq X$, apply the closed-ambient strict-transform
   theorem to its closed immersion and the blowup of $p$. It identifies the strict transform with
   $\operatorname{Bl}_{p\times_XY}(Y)$, with its morphism to $X\prime$. This also covers $Y=p$:
   the pulled-back ideal is zero, its Rees algebra has only degree zero, and its Proj is empty, as
   is the strict transform of the subscheme contained in the centre. If $Y$ avoids $p$, the
   pulled-back ideal is the unit ideal and the blowup is $Y$.
   Uses: lemma-nagata-strict-transform-ambient-closed, def-nagata-affine-blowup.
-/
theorem surface_point_blowup_geometry
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hRegular : IsRegularScheme X)
    (hExcellent : ∀ U : X.affineOpens, IsExcellent Γ(X, U))
    (hDimension : X.dim = 2)
    (hAmple : ∃ (L : X.Modules) (hL : L.IsInvertible), @Scheme.Modules.IsAmple X L hL)
    (p : X) (hp : IsClosed ({p} : Set X))
    (hpDimension : ringKrullDim (X.presheaf.stalk p) = 2)
    (I : X.IdealSheafData) (hI : I = (X.fromSpecResidueField p).ker) :
    IsIntegral I.blowup ∧ IsRegularScheme I.blowup ∧
      (∀ U : I.blowup.affineOpens, IsExcellent Γ(I.blowup, U)) ∧
      IsNoetherian I.blowup ∧ I.blowup.dim = 2 ∧
      (∃ (L : I.blowup.Modules) (hL : L.IsInvertible),
        @Scheme.Modules.IsAmple I.blowup L hL) ∧
      (LocallyOfFiniteType I.blowupMap ∧ QuasiCompact I.blowupMap) ∧
      IsHProjective I.blowupMap ∧
      (∃ e : pullback I.blowupMap (X.fromSpecResidueField p) ≅
          ProjectiveLine (Spec (X.residueField p)),
        e.hom ≫ (ProjectiveLine (Spec (X.residueField p)) ↘ Spec (X.residueField p)) =
          pullback.snd I.blowupMap (X.fromSpecResidueField p)) ∧
      IsRegularScheme (pullback I.blowupMap (X.fromSpecResidueField p)) ∧
      (∀ W : X.IdealSheafData, p ∈ W.support →
        ((W.comap I.blowupMap).support : Set I.blowup) =
          Set.range (pullback.fst I.blowupMap (X.fromSpecResidueField p)) ∪
            Set.range (strictTransformMap W.subschemeι I.blowupMap I.support.compl)) ∧
      (∀ (Y : X.IdealSheafData) [IsIntegral Y.subscheme],
        ∃ e : I.strictTransform Y.subschemeι ≅ (I.comap Y.subschemeι).blowup,
          e.hom ≫ (I.comap Y.subschemeι).blowupMap =
            strictTransformToSource Y.subschemeι I.blowupMap I.support.compl) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
