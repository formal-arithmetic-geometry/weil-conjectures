/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q110
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.Topology.KrullDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Sober

import WeilConjectures.AlgebraicGeometry.Ample
import Mathlib.RingTheory.RingHom.Flat
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProperBirationalNormalCurveIso
import WeilConjectures.AlgebraicGeometry.ChowLemma
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.FlatProperComponentCountLowerSemicontinuous
import Sheaf.AlgebraicGeometry.Morphisms.GenericFiniteOpenNeighborhood
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Sheaf.AlgebraicGeometry.ChowProjectiveClosedImmersions
import Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair
import Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-!
# De Jong marked semistable model in the projective-bundle convention

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Theorem 1.2
(i), (iii)--(vi), printed p. 131 (blueprint: lem-trf-dejong-relative-marked-semistable).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- De Jong's marked semistable alteration theorem in the projective-bundle convention.
Source: ILO, Exposé IX, Theorem 1.2 (i), (iii)--(vi), p. 131
(blueprint: lem-trf-dejong-relative-marked-semistable).

Proof (the fourteen DAG steps):

1. Apply [lem-trf-stein-smooth-generic-curve] to $f:X\to Y$. Write its factorization as
   $X\xrightarrow{g}Y_0\xrightarrow{q}Y$, with generic point $\eta_0$ of $Y_0$. The new base is
   excellent integral Noetherian, $q$ is finite dominant and projective-bundle, and $g$ is proper
   with smooth geometrically integral generic curve. Put $K=\kappa(y)$ and $K_0=\kappa(\eta_0)$;
   the tool identifies $K_0$ with $H^0(X_y,\mathcal O)$ and makes $K_0/K$ finite separable. We
   keep the same closed subscheme $Z$ of the same total scheme $X$.

2. Write the given projective structure as $Y\to\operatorname{Spec}R$. On the affine scheme
   $\operatorname{Spec}R$, the structure sheaf is ample by [def-weil-pbc-ample-invertible-module]:
   its section $1$ has the whole affine scheme as its nonvanishing locus. Thus
   [lem-trf-projective-bundle-to-h-projective] converts this morphism to H-projective if
   necessary. Now $Y$ has an ample invertible sheaf by [lem-weil-pbc-projective-ample-invertible].
   Apply [lem-trf-projective-bundle-to-h-projective] to $q$; then
   [lem-trf-h-projective-composition] makes $Y_0\to\operatorname{Spec}R$ H-projective. Thus $Y_0$
   also has an ample invertible sheaf. We use this absolute ampleness when the flatification
   blowup is converted below.

3. Apply [lem-weil-pbc-chow-noetherian] to $g$. Its proper surjection and immersion into $\mathbf
   P^n_{Y_0}$ satisfy [det-chow-projective-closed-immersions], so the immersion is closed and the
   map to $X$ is projective. Replace the Chow scheme by the reduced closure of the inverse image
   of its dense isomorphism open in $X$. Call it $C_0$, with $p:C_0\to X$. This is an integral
   closed subscheme of the Chow scheme, still proper birational onto $X$, and H-projective over
   $Y_0$. The generic fibre $(C_0)_{\eta_0}$ is integral, proper and birational over $X_{\eta_0}$,
   and has dimension $1$ by [lem-sc-closed-irreducible-dimension-trdeg], since the two function
   fields agree. The target is smooth and hence normal by [lem-sc-smooth-normal]. Apply
   [lem-trf-proper-birational-normal-curve-iso] to conclude that $p_{\eta_0}$ is an isomorphism.
   In particular $(C_0)_{\eta_0}$ is smooth and geometrically integral.

4. The proper closed subscheme $Z_y$ of the proper curve $X_y$ is proper by
   [lem-weil-pbc-closed-immersion-proper]. It is etale by hypothesis, hence unramified, flat and
   locally finitely presented by [def-weil-etale-morphism]. By
   [lem-weil-pbc-unramified-quasi-finite-at-points] and [pqf-lem-proper-lqf-finite], it is finite
   etale over $K$. The finite separable extension $K_0/K$ gives an etale map
   $\operatorname{Spec}K_0\to\operatorname{Spec}K$ by
   [lem-weil-pbc-finite-separable-extension-etale]. The structure map of $Z_y$ factors through it,
   so cancellation in [lem-weil-pbc-etale-composition-cancellation](3) makes $Z_{\eta_0}$ etale
   over $K_0$. It remains finite: a finite spanning set for its coordinate algebra over $K$ also
   spans over $K_0$. Via the generic isomorphism of Step 3, take its inverse image in
   $(C_0)_{\eta_0}$, and let $H_0$ be its schematic closure in $C_0$. This is exactly the
   horizontal marking to be flatified; the other components of $p^{-1}Z$ are not asserted to be
   flat.

5. Apply [lem-trf-flatification-horizontal-curve-pair] to $C_0\to Y_0$ and $H_0$. It gives a
   projective-bundle birational blowup $v:Y_1\to Y_0$, with excellent integral Noetherian $Y_1$,
   and strict transforms $C_1,H_1$. The morphism $h_1:C_1\to Y_1$ is H-projective, flat and
   finitely presented of pure relative dimension $1$; $H_1\to Y_1$ is finite flat finitely
   presented of pure relative dimension $0$, with empty marking permitted. Their generic fibres
   are the original smooth geometrically integral curve and finite etale marking. The projection
   $C_1\to C_0$ is proper birational. Since $Y_0$ has an ample invertible sheaf,
   [lem-trf-projective-bundle-to-h-projective] converts $v$ to H-projective;
   [lem-trf-h-projective-composition] makes $Y_1\to\operatorname{Spec}R$ H-projective.

6. Now $(C_1,H_1)$ meets the global flatness, finite-presentation and pure-dimension hypotheses of
   [lem-trf-stable-modification-flat-curve-pair]. Its generic fibre is smooth with etale marking.
   Obtain an excellent integral base $Y'$ and an H-projective dominant generically finite $r:Y'\to
   Y_1$, and a morphism of closed pairs $(m,n):(X',D)\to(C_1,H_1)\times_{Y_1}Y'$. The map $m$ is
   projective-bundle and is an isomorphism on the generic fibre over $Y'$. The morphism $f':X'\to
   Y'$ is flat finitely presented of pure relative dimension $1$ with nodal geometric fibres;
   $D\hookrightarrow X'$ is closed and is etale over $Y'$, inside the relative smooth locus.
   Define $b=qvr$ and let $a$ be the composite $X'\xrightarrow{m}C_1\times_{Y_1}Y'\to C_1\to
   C_0\xrightarrow{p}X$. The morphism of pairs and the projections give $fa=bf'$ as an equality of
   morphisms.

7. The H-projective morphisms $r$ and $Y_1\to\operatorname{Spec}R$ make
   $Y'\to\operatorname{Spec}R$ H-projective by [lem-trf-h-projective-composition]. Also
   $W=C_1\times_{Y_1}Y'\to Y'$ is H-projective by [lem-pc-projective-base-change]. Thus
   $W\to\operatorname{Spec}R$ is H-projective and $W$ has an ample invertible sheaf by
   [lem-weil-pbc-projective-ample-invertible]. Apply [lem-trf-projective-bundle-to-h-projective]
   to $m:X'\to W$ and compose with $W\to Y'$ to make $f'$ H-projective. The same composition lemma
   makes $b=qvr$ H-projective. A closed embedding in $\mathbf P^N$ is a projective-bundle
   embedding with the trivial rank-$N+1$ module, so these conclusions imply exactly the
   projective-bundle projectivity requested in the item. By [lem-pc-projective-proper], $f'$, $m$
   and $b$ are proper.

8. The generic-fibre isomorphisms in Steps 3, 5 and 6 identify $X'_{\eta'}$ with
   $X_{\eta_0}\times_{K_0}\kappa(\eta')$. It is geometrically integral by the definition
   [def-pc-geometrically-irreducible], and smooth by [lem-pc-proper-base-change]. Moreover $X'$ is
   integral: at $x\in X'$, put $A=\mathcal O_{Y',f'(x)}$ and $B=\mathcal O_{X',x}$. The ring $A$
   is a domain, and $B$ is flat over $A$ by [def-weil-flat-morphism]. Tensoring
   $A\hookrightarrow\operatorname{Frac}A$ with $B$, using [def-weil-pbc-flat-ring-map], injects
   $B$ into $B\otimes_A\operatorname{Frac}A$. The latter ring is a localization of the coordinate
   ring of a nonempty affine open of the integral generic fibre. It is nonzero because $B$ injects
   into it, and is a domain. Thus every $B$ is a domain, so $X'$ is reduced. The same nonzero
   localization gives a generalization of every $x$ in the generic fibre; hence that irreducible
   fibre is dense in $X'$, making $X'$ irreducible as well.

9. The image of the proper $f'$ is closed and contains $\eta'$, so is all of the integral base
   $Y'$. Its geometric fibres are therefore nonempty. Apply
   [lem-weil-pbc-flat-proper-component-count-lower-semicontinuous] to $f'$ (proper, flat and
   finitely presented). The generic geometric fibre is integral, so its number of connected
   components is $1$. If any fibre had at least two components, lower semicontinuity would give a
   nonempty open of $Y'$ on which all fibres had at least two components; this open contains
   $\eta'$, a contradiction. Consequently every geometric fibre is connected. Their pure dimension
   $1$ and ordinary-double-point completed-ring description already come from Step 6.

10. The projection $W\to C_1$ is a base change of proper $r$, and $C_1\to C_0$ and $p$ are proper.
   Thus [lem-weil-pbc-proper-fp-permanence] makes $a$ proper. The generic curve is unchanged by
   $p$, the flatification and $m$, while $\kappa(\eta')/K_0$ is finite. Therefore $a$ induces a
   finite extension of the function field of $X$; it is dominant and its fibre over the generic
   point of $X$ has one point. Likewise $b$ is dominant with finite generic fibre. Apply
   [lem-weil-pbc-generic-finite-morphism-open-neighborhood] to $a$ and $b$, both proper maps of
   finite type over Noetherian targets, to find dense opens over which they are finite. This
   verifies the stated precise generically-finite convention, without an invertibility or
   prime-to-anything restriction on the degree.

11. All base schemes produced by the Stein, flatification and stable-modification tools are
   excellent integral Noetherian. The total space $X'$ is of finite type over $Y'$, since it is
   projective; every affine coordinate ring of $X'$ is a finite type algebra over an excellent
   base chart, after localization as necessary. Thus [lem-exc-finite-type-localization-excellent]
   proves excellence. Proper finite-type schemes over Noetherian schemes are Noetherian by
   [lem-weil-pbc-finite-type-over-noetherian]. Combined with Step 8, this gives exactly the
   required excellent integral source schemes.

12. Because $D$ is closed in the proper $Y'$-scheme $X'$, [lem-weil-pbc-closed-immersion-proper]
   makes $D\to Y'$ proper. The etale property of Step 6 gives flatness, local finite presentation
   and unramifiedness by [def-weil-etale-morphism];
   [lem-weil-pbc-unramified-quasi-finite-at-points] gives local quasi-finiteness. By
   [lem-trf-nodal-family-fitting-singular], the relative smooth locus $U\subset X'$ is open. It
   contains $D$, and $U\to Y'$ is smooth of relative dimension $1$ because its geometric fibres
   are the smooth opens in the pure one-dimensional fibres. The closed subscheme $D\subset U$
   satisfies clause (3) of [lem-pc-cartier-criterion], hence is a relative effective Cartier
   divisor on $U/Y'$. On $X'\setminus D$ its ideal is the unit ideal. These two open
   neighbourhoods cover $X'$, so $D$ is an effective Cartier divisor on $X'$ as required; the
   empty divisor is included.

13. Apply [lem-trf-nodal-family-fitting-singular] to $f'$. It gives the open relative smooth locus
   $U$ and a closed singular subscheme supported on $X'\setminus U$. Set
   $T_{\mathrm{sing}}=f'(X'\setminus U)$. This is closed because $f'$ is proper. Since the generic
   fibre is smooth, it omits $\eta'$, so is nowhere dense. By construction $f'$ is smooth over
   $Y'\setminus T_{\mathrm{sing}}$.

14. Let $E=a^{-1}(|Z|)$. It is closed and has finitely many irreducible components by
   [lem-weil-pbc-noetherian-finitely-many-components]. Its generic fibre is exactly $|D_{\eta'}|$,
   because all the generic maps of pairs used above are isomorphisms. Every component of $E$
   dominating $Y'$ has its generic point in this generic fibre, hence in the closed subset $|D|$;
   its entire closure is therefore in $|D|$. Let $V$ be the union of the remaining, vertical
   components of $E$. It is closed, and properness of $f'$ makes $T_{\mathrm{vert}}=f'(V)$ closed.
   It omits $\eta'$, so is nowhere dense. Every point of $E$ either lies in $|D|$ or in $V$,
   giving $E\subset|D|\cup f'^{-1}(T_{\mathrm{vert}})$. Finally take $T'=T_{\mathrm{sing}}\cup
   T_{\mathrm{vert}}$. This is closed, excludes the generic point of the integral base, and gives
   both required smoothness and boundary inclusion. This constructs a closed bad set rather than
   assuming the set-theoretic image of $E\setminus D$ is closed.
-/
theorem exists_deJong_relativeMarkedSemistable
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.Opens, IsAffineOpen U → IsExcellent Γ(X, U))
    (hY : ∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U))
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Y ⟶ Spec (CommRingCat.of R)) (hp : IsProjectiveBundle p)
    (y : Y) (hy : IsGenericPoint y Set.univ)
    [Smooth (f.fiberToSpecResidueField y)] [IrreducibleSpace (f.fiber y)]
    (hdim : topologicalKrullDim (f.fiber y) = 1)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hZ : IsNowhereDense (Set.range j))
    [Etale ((j ≫ f).fiberToSpecResidueField y)] :
    ∃ (X' Y' : Scheme.{u}) (a : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y')
      (hfp : LocallyOfFinitePresentation f'),
      a ≫ f = f' ≫ b ∧
      IsProper a ∧ IsDominant a ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (pullback.snd a U.ι)) ∧
      IsProjectiveBundle b ∧ IsDominant b ∧
      (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (pullback.snd b U.ι)) ∧
      IsIntegral X' ∧ IsIntegral Y' ∧
      (∀ U : X'.Opens, IsAffineOpen U → IsExcellent Γ(X', U)) ∧
      (∀ U : Y'.Opens, IsAffineOpen U → IsExcellent Γ(Y', U)) ∧
      IsProjectiveBundle f' ∧ Flat f' ∧ QuasiCompact f' ∧ QuasiSeparated f' ∧
      @HasNodalGeometricFibres _ _ f' hfp ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (g : Spec (.of Ω) ⟶ Y'),
        (pullback f' g).IsPureDimension 1) ∧
      (∃ (D : Scheme.{u}) (i : D ⟶ X'),
        IsEffectiveCartierCenter i ∧
        IsProper (i ≫ f') ∧ Etale (i ≫ f') ∧
        (∀ d : D, i d ∈ ((@Scheme.Hom.smoothLocus _ _ f' hfp) : Set X')) ∧
        ∃ (T : Set Y') (hT : IsClosed T), IsNowhereDense T ∧
          Smooth (f' ∣_ (⟨Tᶜ, hT.isOpen_compl⟩ : Y'.Opens)) ∧
          Set.preimage a (Set.range j) ⊆ Set.range i ∪ Set.preimage f' T) ∧
      ∃ y' : Y', IsGenericPoint y' Set.univ ∧
        Smooth (f'.fiberToSpecResidueField y') ∧
        GeometricallyIntegral (f'.fiberToSpecResidueField y') := by
  sorry

end AlgebraicGeometry
