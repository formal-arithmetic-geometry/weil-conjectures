/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Irreducible
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber
public import WeilConjectures.AlgebraicGeometry.Modules.HomObjSections
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.NonnegativeProjectiveTwistVanishing
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.Topology.ClosedImmersionPushforwardCohomology
import WeilConjectures.AlgebraicGeometry.SectionBoundaryExact
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyAgree
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import Sheaf.TraceFormula.GenericFibrePointsSmooth
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.CurveSectionDegreePositivity
import Sheaf.RingTheory.HenselianSmoothAlgebraLifting
import Sheaf.TraceFormula.PointedGenusZeroProjectiveLine
import Sheaf.TraceFormula.SmoothCurveSectionCartier

/-! # Polar sections on a proper valuation curve

Source: Temkin, *Stable modification of relative curves*, Proposition 4.4.6,
printed pp. 32--33 (blueprint: lem-trf-valuation-nodal-polar-section).

Local equations express poles through evaluation of a section of the dual divisor ideal.
No regularity or nodality is required away from the distinguished component.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- The canonical section `1` of the dual of a divisor ideal: it is the inclusion of the
ideal into the structure sheaf, regarded as a global section of its internal Hom.
Source: Temkin, Proposition 4.4.6, pp. 32--33
(blueprint: lem-trf-valuation-nodal-polar-section). -/
def polarDivisorCanonicalSection {Y : Scheme.{u}} (J : Y.IdealSheafData) :
    Γ(J.toModulesᵛ, ⊤) :=
  Scheme.Modules.homToΓHomObj J.toModules (Scheme.Modules.unit Y) J.toModulesι

/-- The polar section with nonzero values at the chosen horizontal Cartier points.
Source: Temkin, Proposition 4.4.6, printed pp. 32--33
(blueprint: lem-trf-valuation-nodal-polar-section).

The component `Z` is specified with its reduced closed immersion `z` into the closed fibre.
The geometric nodality and boundary bounds are imposed only over `Z`. The other components
are enumerated bijectively, including the empty enumeration. The ideal of the sum of the
horizontal divisors is their product, and multiplication of the divisor by `m` is ideal power.
For a local equation `t` of a horizontal divisor, `q` is the generator of the total divisor
ideal mapping to `t^m`. Evaluation of `a` on `q` is the numerator in `a = b/t^m`.
Its fibre germ is a unit, while the fibre germ of `t` generates the maximal ideal and is a
non-zero-divisor. This states exact pole order `m`. Off the divisor, the functional is
multiplication by a regular function on the ideal viewed inside the structure sheaf. The canonical
section is the inclusion functional, and its scheme-theoretic zero ideal is the total divisor ideal.

Proof, with the DAG's ten steps:

1. Put $k=\kappa(s)$. The valuation ring $V$ is integrally closed: if an element $x$ of $K$ is
   integral but not in $V$, then $x^{-1}$ is a nonunit of $V$; dividing a monic integral equation
   by its highest power of $x$ gives $1\in x^{-1}V$, a contradiction. The same argument applies to
   its localizations. Thus $T$ is integral normal with separably closed function field $K$. Apply
   [sbc-lem-etale-over-normal] to $T$: its local ring at $s$, namely $V$, is strictly henselian.
   In particular $V$ is henselian and $k$ is separably closed.

2. The proper component $Z$ becomes $\mathbf P^1$ after extension to an algebraic closure
   $\overline k$. Smoothness descends by [lem-trf-smooth-fpqc-base-descent]. It has a $k$-rational
   point $q$ by [lem-pc-rational-points-dense]. The projective-space vanishing [lem-
   pc-d2-nonnegative-projective-twist-vanishing] and flat cohomology base change [lem-sc-flat-
   base-change-coherent] give $H^1(Z,\mathcal O_Z)=0$. On the two standard charts of the geometric
   projective line, a global function lies in both $\overline k[t]$ and $\overline k[t^{-1}]$
   inside $\overline k[t,t^{-1}]$, hence is constant. Faithful field extension and the same base-
   change theorem therefore give $H^0(Z,\mathcal O_Z)=k$. The point $q$ is Cartier by [lem-trf-
   smooth-curve-section-cartier], applied to $Z\to\operatorname{Spec}k$. By [lem-pc-degree-base-
   change], $\mathcal O_Z(q)$ has degree one. Apply [lem-trf-pointed-genus-zero-projective-line]
   to get $Z\simeq\mathbf P^1_k$.

3. If $n=0$, choose $m=1$, $P=0$, $L=\mathcal O_Y$ and $a=e=1$; all point and pole assertions are
   empty. Hence suppose $n>0$. Write $C=Y_s$ with its reduced structure. Apply [lem-trf-generic-
   fibre-points-smooth] to $C\to\operatorname{Spec}k$, whose source and base are Noetherian: $C$
   is geometrically reduced and of finite type over a field. Around the generic point of each
   $Z_i$ there is a nonempty smooth open in $C$ disjoint from all other components, including $Z$.
   By [lem-trf-smooth-at-point-fibre-criterion] these points belong to the relative smooth locus
   of $Y\to T$, since $Y\to T$ is flat and finitely presented. The rational-point density [lem-pc-
   rational-points-dense] gives a $k$-rational point $p_i$ in each such open.

4. Choose a smooth affine $T$-neighbourhood $U_i=\operatorname{Spec}B_i$ of $p_i$ inside the
   relative smooth locus. Its coordinate algebra is smooth over $V$ by the affine smooth-morphism
   convention. The point is a $V$-algebra map $B_i\to k$. Apply [lem-trf-henselian-smooth-algebra-
   lifting] with $(A,I)=(V,\mathfrak m_V)$ to obtain $B_i\to V$, hence a section $\sigma_i:T\to Y$
   through $p_i$ contained in $U_i$. As $Y\to T$ is separated, [lem-weil-pbc-section-separated-
   closed-immersion] makes the sections closed immersions. By [lem-trf-smooth-curve-section-
   cartier] in the smooth locus their images $P_i$ have ideals locally generated by one non-zero-
   divisor, and the same is true in $Y$ since the ideal is the unit ideal off their images. Two
   images cannot meet: the inverse image under $\sigma_i$ of the other closed section would be a
   nonempty closed subset of $T$ and so would contain $s$, contradicting $p_i\ne p_j$. The $P_i$
   are therefore pairwise disjoint and each is isomorphic to $T$.

5. Let $E=\sum_i p_i$ on $C$, $W=\bigcup_i Z_i$ with reduced structure, and $D=Z\cap W$ with its
   scheme-theoretic structure. The points $p_i$ are smooth points of $C$ and $W$, so $E$ is
   Cartier on both; write $\mathcal I_D$ for the ideal of $D$ in $W$. For $\epsilon\in\{0,1\}$ put
   $N_{m,\epsilon}=\mathcal O_C(mE-\epsilon E)$. Because $E$ is disjoint from $Z$, restriction to
   $Z$ has a canonical trivialization. There is an exact sequence on $C$, with $j_W,j_Z$ the
   closed inclusions, $0\to j_{W,*}(\mathcal I_D\otimes\mathcal O_W((m-\epsilon)E))\to
   N_{m,\epsilon}\to j_{Z,*}\mathcal O_Z\to0$. Indeed, on an affine open with component ideals $I$
   for $Z$ and $J$ for $W$, reducedness of $C=Z\cup W$ says $I\cap J=0$. The kernel $I$ of $A\to
   A/I$ identifies with $(I+J)/J$, the ideal of $D$ in $W$. Tensor this identity with the locally
   free rank-one module $N_{m,\epsilon}$. This proves the sequence without any hypothesis on the
   singularities away from $Z$.

6. Put $M=\mathcal O_W(E)$. On each normalized irreducible component of $W$, the pullback of the
   canonical section of $M$ is nonzero and has a zero above $p_i$: near $p_i$ the curve is smooth
   and the divisor is its reduced rational point. Thus its degree is positive by [lem-trf-curve-
   section-degree-positivity]; pullback preserves invertibility by [lem-weil-pbc-invertible-
   pullback-tensor]. The componentwise degree criterion [lem-trf-fibre-degree-ample-criterion]
   shows that $M$ is ample on the proper reduced curve $W$. The two fixed coherent sheaves
   $\mathcal I_D$ and $\mathcal I_D\otimes M^{-1}$ may have singular support; Serre vanishing
   applies to coherent sheaves, so no smoothness or semistability of $W$ is needed.

7. Apply [lem-pc-serre-vanishing] to those two coherent sheaves and $M$. For one sufficiently
   large positive $m$, both $H^1(W,\mathcal I_D\otimes M^m)$ and $H^1(W,\mathcal I_D\otimes
   M^{m-1})$ vanish. The closed-immersion cohomology comparison [lem-sc-cohomology-closed-
   immersion-pushforward], together with [lem-sc-zariski-module-abelian-cohomology-agree],
   identifies these with the cohomology of their direct images on $C$. The long exact sequence of
   right derived global sections [lem-weil-pbc-right-derived-universal-delta-functor] for the two
   sequences in step 5, and $H^1(Z,\mathcal O_Z)=0$, give $H^1(C,\mathcal O_C(mE))=H^1(C,\mathcal
   O_C(mE-E))=0$.

8. The evaluation sequence $0\to\mathcal O_C(mE-E)\to\mathcal O_C(mE)\to\mathcal O_C(mE)|_E\to0$
   is exact, as is seen by dividing by a local parameter at each $p_i$. Its section boundary has
   zero target by step 7. By [lem-sc-module-section-boundary-exact], every section on $E$ lifts to
   $C$. Each fibre over $p_i$ is one-dimensional over $k$, so choose a nonzero vector in each of
   these finitely many fibres. Their tuple lifts to $a_s\in H^0(C,\mathcal O_C(mE))$, and
   $a_s(p_i)\ne0$ for all $i$.

9. Put $P=m\sum_iP_i$ and $L=\mathcal O_Y(P)$. Locally its ideal is $(t^m)$ and its dual is
   generated by $t^{-m}$, so $L$ is invertible, flat over $V$ because $Y$ is flat, and of finite
   presentation as an $\mathcal O_Y$-module. The quotient $\mathcal O_{P_i}\simeq\mathcal O_T$ is
   $V$-flat, so tensoring its ideal sequence with $k$ preserves injectivity. The resulting ideal
   cuts out $p_i$; its generator is a local parameter there, since the fibre section is a smooth
   curve point. Thus restriction gives $L_s=\mathcal O_C(mE)$. Cohomology above degree one on $C$
   vanishes by [lem-sc-noetherian-cohomology-above-dimension]. Combining this with step 7 gives
   $H^q(C,L_s)=0$ for every $q\ne0$. Its degree-zero cohomology is finite-dimensional by [lem-pc-
   coherent-hi]. Apply the general form of [sk-thm-picard-perfect] with $i=0$ and
   $r=\dim_kH^0(C,L_s)$. Its open locus contains $s$ and therefore is all of $T$, since an open
   neighbourhood of the closed point of a local spectrum is the whole spectrum. Consequently
   $f_*L$ is finite locally free and formation of $H^0$ commutes with the base change to $s$.
   Since $T$ is affine, $\Gamma(Y,L)\otimes_V k\simeq H^0(C,L_s)$; quotienting a module by
   $\mathfrak m_V$ is surjective. Lift $a_s$ to $a\in\Gamma(Y,L)$.

10. The local generator $t$ of the ideal of $P_i$ restricts to a uniformizer of the smooth point
   $p_i$ on $C$. Write $a=b\,t^{-m}$ locally. The assertion $a_s(p_i)\ne0$ says $b(p_i)\ne0$, so
   $b$ is a unit near $p_i$ and its restriction to $C$ is a unit in the corresponding local ring.
   Thus the associated meromorphic function has pole order exactly $m$ at $p_i$. Away from $P$,
   the inclusion $L\subseteq\mathcal K_Y$ is just $\mathcal O_Y\subseteq\mathcal K_Y$, so there
   are no other poles; this inclusion is defined by inverting the non-zero-divisor $t$. Finally
   $e=1$ is locally $t^m\,t^{-m}$, hence its zero scheme is exactly $P$. The lifted value at each
   $p_i$ is the selected nonzero vector. These are all the required conclusions.
-/
theorem exists_valuation_nodal_polar_section
    (K : Type u) [Field K] [IsSepClosed K] (V : ValuationSubring K)
    [Finite (PrimeSpectrum V)]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of V))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y))
    (hpure : ∀ t : Spec (.of V), (f.fiber t).IsPureDimension 1)
    (hred : ∀ t : Spec (.of V), GeometricallyReduced (f.fiberToSpecResidueField t))
    (s : Spec (.of V)) (hs : IsClosed ({s} : Set (Spec (.of V))))
    (Z : Scheme.{u}) [IsReduced Z] (z : Z ⟶ f.fiber s) [IsClosedImmersion z]
    (hZ : Set.range z ∈ irreducibleComponents (f.fiber s))
    (hgeom : Nonempty
      (Over.mk (pullback.snd (z ≫ f.fiberToSpecResidueField s)
        (Spec.map (CommRingCat.ofHom (algebraMap ((Spec (.of V)).residueField s)
          (AlgebraicClosure ((Spec (.of V)).residueField s)))))) ≅
        Over.mk (ProjectiveSpace (ULift.{u} (Fin 2))
          (Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField s)))) ↘
            Spec (.of (AlgebraicClosure ((Spec (.of V)).residueField s))))))
    (hnodal : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of ((Spec (.of V)).residueField s)))
      (x : pullback (C := Scheme.{u}) (f.fiberToSpecResidueField s) g),
      pullback.fst (f.fiberToSpecResidueField s) g x ∈ Set.range z →
      x ∉ (pullback.snd (f.fiberToSpecResidueField s) g).smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal
          ((pullback (f.fiberToSpecResidueField s) g).presheaf.stalk x))
          ((pullback (f.fiberToSpecResidueField s) g).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) Ω ⧸ Ideal.span
            {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))
    (hboundary : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ Spec (.of ((Spec (.of V)).residueField s))),
      {x : pullback (C := Scheme.{u}) (f.fiberToSpecResidueField s) g |
        pullback.fst (f.fiberToSpecResidueField s) g x ∈ Set.range z ∧
        ∃ W ∈ irreducibleComponents (f.fiber s), W ≠ Set.range z ∧
          pullback.fst (f.fiberToSpecResidueField s) g x ∈ W}.encard ≤ 2) :
    Nonempty (Over.mk (z ≫ f.fiberToSpecResidueField s) ≅
      Over.mk (ProjectiveSpace (ULift.{u} (Fin 2))
        (Spec (.of ((Spec (.of V)).residueField s))) ↘
          Spec (.of ((Spec (.of V)).residueField s)))) ∧
    ∃ (n : ℕ) (Zi : Fin n → Set (f.fiber s)),
      Function.Injective Zi ∧
      Set.range Zi = {W ∈ irreducibleComponents (f.fiber s) | W ≠ Set.range z} ∧
      ∃ (p : Fin n → f.fiber s) (σ : Fin n → (Spec (.of V) ⟶ Y)),
        (∀ i, σ i ≫ f = 𝟙 _) ∧
        (∀ i, IsClosedImmersion (σ i) ∧ (σ i).ker.IsInvertible) ∧
        (∀ i, Set.range (σ i) ⊆ (f.smoothLocus : Set Y)) ∧
        (∀ i j, i ≠ j → Disjoint (Set.range (σ i)) (Set.range (σ j))) ∧
        (∀ i, σ i s = f.fiberι s (p i)) ∧
        (∀ i, p i ∈ Zi i ∧ p i ∉ Set.range z ∧
          ∀ W ∈ irreducibleComponents (f.fiber s), p i ∈ W → W = Zi i) ∧
        (∀ i, p i ∈ (f.fiberToSpecResidueField s).smoothLocus ∧
          IsIso ((f.fiberToSpecResidueField s).residueFieldMap (p i))) ∧
        ∃ (m : ℕ), 0 < m ∧ ∃ J : Y.IdealSheafData,
          J = (∏ i, (σ i).ker) ^ m ∧ J.IsInvertible ∧ J.toModulesᵛ.IsInvertible ∧
          ∃ a : Γ(J.toModulesᵛ, ⊤),
            (∀ i, Scheme.Modules.residueValue a (f.fiberι s (p i)) trivial ≠ 0) ∧
            (∀ i, Module.rank (Y.residueField (f.fiberι s (p i)))
              (Scheme.Modules.residueFiber J.toModulesᵛ (f.fiberι s (p i))) = 1) ∧
            (Scheme.Modules.homOfGlobalSection J.toModulesᵛ
              (polarDivisorCanonicalSection J)).zeroLocus = J ∧
            (∀ i, ∃ (U : Y.affineOpens) (hx : f.fiberι s (p i) ∈ U.1)
              (t : Γ(Y, U.1)) (q : Γ(J.toModules, U.1)),
              t ∈ nonZeroDivisors Γ(Y, U.1) ∧
              (σ i).ker.ideal U = Ideal.span {t} ∧
              J.toModulesι.app U.1 q = t ^ m ∧
              IsLocalRing.maximalIdeal ((f.fiber s).presheaf.stalk (p i)) =
                Ideal.span {((f.fiber s).presheaf.germ
                  ((f.fiberι s) ⁻¹ᵁ U.1) (p i) hx) ((f.fiberι s).app U.1 t)} ∧
              ((f.fiber s).presheaf.germ ((f.fiberι s) ⁻¹ᵁ U.1) (p i) hx)
                ((f.fiberι s).app U.1 t) ∈
                  nonZeroDivisors ((f.fiber s).presheaf.stalk (p i)) ∧
              IsUnit (((f.fiber s).presheaf.germ ((f.fiberι s) ⁻¹ᵁ U.1) (p i) hx)
                ((f.fiberι s).app U.1
                  ((Scheme.Modules.ΓHomObjAddEquiv J.toModules
                    (Scheme.Modules.unit Y) a).app U.1 q)))) ∧
            (∀ x : Y, x ∉ J.support → ∃ (U : Y.affineOpens), x ∈ U.1 ∧
              ∃ b : Γ(Y, U.1), ∀ q : Γ(J.toModules, U.1),
                (Scheme.Modules.ΓHomObjAddEquiv J.toModules
                  (Scheme.Modules.unit Y) a).app U.1 q =
                    b * @id Γ(Y, U.1) (J.toModulesι.app U.1 q)) := by
  sorry

end AlgebraicGeometry
