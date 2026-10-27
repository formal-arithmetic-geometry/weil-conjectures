/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.AlgebraicGeometry.BoundedHilbertWeightPolynomials
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.TraceFormula.NodalSubcurveBoundary
import WeilConjectures.AlgebraicGeometry.Ample
import Sheaf.AlgebraicGeometry.AmpleIffNormalizedComponentDegreePos
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Sheaf.AlgebraicGeometry.NodalNormalizationQuotient
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
import WeilConjectures.AlgebraicGeometry.AffineMorphismCohomologyEdge
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler
import Sheaf.TraceFormula.PointedGenusZeroProjectiveLine
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction

/-! # Component interpolation from leading Hilbert weights

Source: Morrison, arXiv:0810.2340, Section 3.2, Theorem 8, step (9), printed p.14;
Gieseker, Lectures on moduli of curves, Proposition 1.0.7 and pp.64--65.
(blueprint: lem-sfb-gieseker-component-interpolation)

The auxiliary restriction arrows are fixed on every standard chart. Their eventual
quadratic estimate characterizes the leading coefficients of the recorded Hilbert weights.
A subset of irreducible components specifies a reduced union, including disconnected
and empty unions. An integral closed component outside it specifies exactly one component
of the normalization of the reduced complement.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- Each complementary normalized component has degree at least its boundary count,
except for a rational normal component of degree one less. Here `r = n + 2`.
The isomorphism to the projective line is over k; the line-bundle isomorphism and
surjectivity of ambient linear forms state completeness in the component's own span.

Source: Morrison, Section 3.2, Theorem 8, step (9), p.14; the leading-weight version
is the reconstruction from Gieseker Proposition 1.0.7 and pp.64--65 recorded in the DAG.
(blueprint: lem-sfb-gieseker-component-interpolation)

Proof plan (the nine DAG steps):
1. Projectivity gives properness (lem-pc-projective-proper) and Noetherianity
   (lem-weil-pbc-finite-type-over-noetherian). Use
   lem-trf-reduced-curve-normalization-genus and lem-trf-nodal-subcurve-boundary for
   finitely many smooth normalized components and their distinct boundary branches.
   The hyperplane line is ample (def-weil-pbc-ample-invertible-module), so each
   normalized component degree is positive by lem-trf-fibre-degree-ample-criterion.
2. For each reduced union A, restrict L to A. Its pushforward is coherent by
   lem-pc-closed-immersion-coherent-cohomology; its restriction kernel is coherent by
   lem-weil-pbc-coherent-kernel-cokernel-locnoeth. Dimension vanishing
   (lem-sc-noetherian-cohomology-above-dimension) kills H² of the kernel. The long
   exact sequence (pqf-def-cohomology) and H¹(D,L)=0 give H¹(A,L)=0. Higher groups
   vanish too; lem-pc-coherent-hi gives finiteness. Thus h⁰(A,L)=chi(A,L), also for
   disconnected A and the empty union.
3. Tensor the sequence of lem-trf-nodal-normalization-quotient by L. Its last term
   has unchanged Euler characteristic by lem-pc-chi-zero-dim-support. Apply
   lem-pc-euler-additive, lem-weil-pbc-affine-morphism-cohomology-edge and
   def-pc-degree-line-bundle to get chi(A,L)-chi(A,O)=sum of normalized degrees e_A.
4. For an integral component T, lem-sc-global-functions and dimension vanishing give
   chi(T,O)=1-p_T with p_T=h¹(T,O)≥0. The nodal Euler formula
   (lem-trf-nodal-curve-normalization-euler) gives, when T meets A in ell nodes,
   h⁰(A union T,L)-h⁰(A,L)=e_T+1-p_T-ell. If u counts its other boundary nodes,
   k_(A union T)-k_A=u-ell, including self-nodes in p_T already.
5. Set epsilon=(g-1)/d in (0,1/9), q=r/d=1-epsilon, and
   Delta(A)=h⁰(A,L)-q(e_A+k_A/2). The Hilbert comparison
   (lem-sfb-projective-hilbert-polynomial-dimension) gives e_D=d, hence Delta(D)=0;
   Delta(empty)=0. Choose an inclusion-maximal union with negative Delta, if any.
6. If all complementary degrees dominate their boundary counts, apply only the
   degree-bounded case of lem-sfb-subcurve-span-weight-bound. It supplies a zero/one
   flag with s≤h⁰(A,L) and a_F≥e_A+k_A/2. The weight hypothesis gives a_F≤s/q,
   contradicting Delta(A)<0. Thus some complementary T has e≤ell-1 and ell≥2.
7. Maximality gives Delta(A union T)-Delta(A)>0. Step 4 computes this difference as
   epsilon*e+1-p_T-(1-q/2)*ell-q*u/2, at most q*(1-(ell+u)/2)-p_T≤0.
   This contradiction proves q(e_A+k_A/2)≤h⁰(A,L) for every union, without using
   the rational-normal exception of the span estimate.
8. Fix Y,T and let b count its branches to Y; let kappa count all its attachments.
   If e<b then kappa≥b≥e+1. The inequality for T gives
   (1-3*epsilon)*e≤1+epsilon-2*p_T, forcing p_T=0 and e=1 since epsilon<1/9.
   Also kappa≤2*(1+epsilon)/(1-epsilon)<5/2. Thus kappa=b=2 and e=b-1.
9. Apply lem-trf-pointed-genus-zero-projective-line to T with its degree-one line.
   It is a smooth projective line, and lem-trf-nodal-normalization-adjunction makes
   its normalization an isomorphism. The coordinate sections generate its line.
   A one-dimensional image would trivialize that positive-degree line, so the image
   is all of its two-dimensional H⁰. Its own-span embedding is the complete degree-one
   system. Empty Y has b=0; the full union has no complementary component.
-/
theorem gieseker_component_interpolation
    (k : Type u) [Field k] [IsAlgClosed k] (g d n : ℕ)
    (hg : 2 ≤ g) (hd : 9 * (g - 1) < d) (hr : n + 2 + g = d + 1)
    (D : Scheme.{u}) [ConnectedSpace D] [IsReduced D]
    (i : D ⟶ ℙ(HilbertPlucker.Coordinates.{u} n; Spec (.of k)))
    [IsClosedImmersion i]
    (f : D ⟶ Spec (.of k))
    (hf : i ≫ (ℙ(HilbertPlucker.Coordinates n; Spec (.of k)) ↘ Spec (.of k)) = f)
    [LocallyOfFinitePresentation f] (hpure : D.IsPureDimension 1)
    (hnodal : ∀ x : D, x ∉ f.smoothLocus →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal (D.presheaf.stalk x))
          (D.presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) k ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) *
              MvPowerSeries.X 1})))
    (hP : ProjectiveHilbertPolynomial.IsCoordinatePolynomial k (n + 1) i
      (Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (1 - (g : ℚ))))
    (L : D.Modules)
    (hL : (Scheme.Modules.tensorPullback i).obj
      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1) ≅ L)
    (hcomplete : Function.Bijective
      (fun v : HilbertPlucker.Coordinates n → k ↦
        ∑ j : HilbertPlucker.Coordinates n,
          f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv (v j)) •
            hL.hom.app ⊤
              (((Scheme.Modules.tensorPullbackSectionAdjunction i).unit.app
                (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1)).app
                  ⊤ (ProjectiveSpace.twistOneSection
                    (HilbertPlucker.Coordinates n) (Spec (.of k)) j))))
    (h0 : Module.finrank k (UniformProjectiveFibreVanishing.cohomology k f L 0) = n + 2)
    (h1 : Subsingleton ((RingedSpace.moduleCohomology D.toRingedSpace 1).obj L))
    (ρ : ∀ m : ℕ, ModuleCat.of k
      (MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m) ⟶
        BoundedHilbertWeight.sections k n i m)
    (hρ : ∀ (m : ℕ)
      (p : MvPolynomial.homogeneousSubmodule (HilbertPlucker.Coordinates.{u} n) k m)
      (j : HilbertPlucker.Coordinates.{u} n),
      ((Scheme.Modules.tensorPullback i).obj
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n)
          (Spec (.of k)) (m : ℤ))).presheaf.map (homOfLE le_top).op
        ((UniformProjectiveFibreVanishing.zeroSections _).hom (ρ m p)) =
      Scheme.Modules.tensorPullbackSection i
        (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) (m : ℤ))
        (ProjectiveSpace.standardOpen _ (Spec (.of k)) j)
        (ProjectiveSpace.chartRingEquiv _ k j (MvPolynomial.dehomogenizeX k j p.val) •
          ProjectiveSpace.twistGenerator _ (Spec (.of k)) (m : ℤ) j))
    (a : Module.Basis (HilbertPlucker.Coordinates.{u} n) k
      (BoundedHilbertWeight.LinearForms k n) → (HilbertPlucker.Coordinates.{u} n → ℕ) → ℚ)
    (ha : ∀ (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k
      (BoundedHilbertWeight.LinearForms k n)) (w : HilbertPlucker.Coordinates.{u} n → ℕ),
      (∀ j, w j ≤ 4) → ∃ m₀ A : ℕ, ∀ m : ℕ, m₀ ≤ m →
        |(BoundedHilbertWeight.weight (ρ m) b w : ℚ) - a b w * (m : ℚ)^2| ≤ (A : ℚ) * m)
    (hweight : ∀ (b : Module.Basis (HilbertPlucker.Coordinates.{u} n) k
      (BoundedHilbertWeight.LinearForms k n)) (w : HilbertPlucker.Coordinates.{u} n → ℕ),
      (∀ j, w j ≤ 4) → a b w ≤ (d : ℚ) / (n + 2 : ℕ) * ∑ j, (w j : ℚ))
    (S : Set (Set D)) (hS : S ⊆ irreducibleComponents D)
    (T : Scheme.{u}) [IsIntegral T] (j : T ⟶ D) [IsClosedImmersion j]
    (hT : Set.range j ∈ irreducibleComponents D) (houtside : Set.range j ∉ S)
    (e : ℤ)
    (he : e = @Scheme.Modules.degree k _ T.normalization
      ⟨T.fromNormalization ≫ j ≫ f⟩
      ((Scheme.Modules.tensorPullback (T.fromNormalization ≫ j)).obj L))
    (b : ℕ) (hb : b = ((T.fromNormalization ≫ j) ⁻¹' ⋃₀ S).ncard) :
    (b : ℤ) ≤ e ∨
      (IsIso T.fromNormalization ∧ e = (b : ℤ) - 1 ∧
        ∃ φ : T ≅ ℙ(HilbertPlucker.Coordinates.{u} 0; Spec (.of k)),
          φ.hom ≫ (ℙ(HilbertPlucker.Coordinates 0; Spec (.of k)) ↘ Spec (.of k)) = j ≫ f ∧
          Nonempty
            ((Scheme.Modules.tensorPullback (j ≫ i)).obj
              (ProjectiveSpace.twist (HilbertPlucker.Coordinates n) (Spec (.of k)) 1) ≅
              (Scheme.Modules.tensorPullback φ.hom).obj
                (ProjectiveSpace.twist (HilbertPlucker.Coordinates 0) (Spec (.of k)) e)) ∧
          Function.Surjective
            (fun v : HilbertPlucker.Coordinates n → k ↦
              ∑ l : HilbertPlucker.Coordinates n,
                (j ≫ f).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv (v l)) •
                  @id (Γ((Scheme.Modules.tensorPullback (j ≫ i)).obj
                    (ProjectiveSpace.twist (HilbertPlucker.Coordinates n)
                      (Spec (.of k)) 1), ⊤))
                    (((Scheme.Modules.tensorPullbackSectionAdjunction (j ≫ i)).unit.app
                      (ProjectiveSpace.twist (HilbertPlucker.Coordinates n)
                        (Spec (.of k)) 1)).app ⊤
                          (ProjectiveSpace.twistOneSection
                            (HilbertPlucker.Coordinates n) (Spec (.of k)) l)))) := by
  sorry

end AlgebraicGeometry
