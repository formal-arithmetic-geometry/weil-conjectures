/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q108
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Sheaf.AlgebraicGeometry.DivisorModule
public import Mathlib.Data.Real.Basic
import Sheaf.TraceFormula.ReducedCurveNormalizationGenus
import Sheaf.AlgebraicGeometry.NormalizationSingularSkyscraper
import Sheaf.AlgebraicGeometry.EulerCharZeroDimSupport
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import Sheaf.AlgebraicGeometry.CurveDegreeTensorAdditive

/-!
# Uniform codimension of normalization jet conditions

Source: Morrison, Section 3.2, Theorem 8, proof of step (4), pp. 14--15;
Stacks Project, Tags 0C1R, 0AYT, 0BS6 and 0CCS, simultaneous-jet extension.
(blueprint: lem-sfb-normalization-jet-codimension).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/-- A normalized reduced irreducible component, using the existing normalization construction.
Source: Stacks Project, Tag 0C1R (blueprint: lem-sfb-normalization-jet-codimension). -/
abbrev normalizationJetBranch (D : Scheme.{u}) (Z : irreducibleComponents D) : Scheme.{u} :=
  (D.reducedNormalizationComponent Z).normalization

/-- The canonical map of a normalization branch to the original curve.
Source: Stacks Project, Tag 0C1R (blueprint: lem-sfb-normalization-jet-codimension). -/
abbrev normalizationJetBranchMap (D : Scheme.{u}) (Z : irreducibleComponents D) :
    normalizationJetBranch D Z ⟶ D :=
  (D.reducedNormalizationComponent Z).fromNormalization ≫
    (Scheme.IdealSheafData.vanishingIdeal
      ⟨Z.1, isClosed_of_mem_irreducibleComponents _ Z.2⟩).subschemeι

/-- Global sections with scalars restricted along the specified structure map to Spec k.
This is the concrete degree-zero section model, not a chosen cohomology object.
Source: Stacks Project, Tag 01DZ (blueprint: lem-sfb-normalization-jet-codimension). -/
def normalizationJetSections (k : Type u) [Field k] {D : Scheme.{u}}
    (f : D ⟶ Spec (.of k)) (M : D.Modules) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)).obj
      ((RingedSpace.globalSectionsFunctor D.toRingedSpace).obj M)

/-- Degree on the branch, with its canonical k-structure, of the pulled-back line bundle.
Source: Stacks Project, Tag 0AYR (blueprint: lem-sfb-normalization-jet-codimension). -/
def normalizationJetDegree (k : Type u) [Field k] {D : Scheme.{u}}
    (f : D ⟶ Spec (.of k)) (L : D.Modules) (Z : irreducibleComponents D) : ℤ :=
  letI : (normalizationJetBranch D Z).Over (Spec (.of k)) :=
    ⟨normalizationJetBranchMap D Z ≫ f⟩
  ((Scheme.Modules.pullback (normalizationJetBranchMap D Z)).obj L).degree k

/-- Simultaneous normalization jets impose their total order of conditions up to a uniform
constant. The section subspace is characterized exactly by membership in powers of the
maximal ideals in the pulled-back stalks. In a line-bundle frame on a smooth curve this
says that the coefficient has valuation at least n; zero lies in every such power.

Source: Morrison, Section 3.2, Theorem 8 proof step (4), pp. 14--15, extended to simultaneous
jets; Stacks Project, Tags 0C1R, 0AYT, 0BS6 and 0CCS.
(blueprint: lem-sfb-normalization-jet-codimension).

Proof:
1. Projectivity gives properness by lem-pc-projective-proper. Apply
   lem-trf-reduced-curve-normalization-genus and lem-trf-normalization-singular-skyscraper:
   there are finitely many smooth proper connected normalization branches, and the
   normalization quotient Q is coherent with finite support. Put delta = dim H^0(Q),
   finite by lem-pc-chi-zero-dim-support. On each reduced component,
   lem-sfb-integral-curve-span-degree-rigidity gives positive degree of the restricted O(1).
2. Tensor the normalization exact sequence by L^m, locally a free rank-one module.
   The local trivializations identify the middle term with the direct image of the
   pulled-back line bundle and glue. Left exactness from pqf-def-cohomology embeds H_m
   into T_m, the sum of branch section spaces, with cokernel dimension at most delta;
   lem-pc-chi-zero-dim-support makes this bound independent of m.
3. By lem-sc-global-functions, lem-pc-coherent-hi,
   lem-sc-noetherian-cohomology-above-dimension and
   lem-sc-smooth-connected-curve-local-rings, chi(O_Ci) = 1 - g_i and all section spaces
   are finite-dimensional. The definition of degree and
   lem-trf-curve-degree-tensor-additive give h^0(L_i^m) >= m e_i + 1 - g_i.
4. Form B_i = sum n_q [q]. The lemma lem-sfb-smooth-curve-section-degree-cap with q = 1
   identifies its vanishing space with H^0(L_i^m(-B_i)) and bounds its dimension by
   m e_i - N_i + 1, since N_i <= m e_i. Zero divisors are allowed.
5. The inverse image of these branch vanishing spaces is exactly U by the germ condition.
   Thus dim U <= sum (m e_i - N_i + 1), and subtraction gives the stated estimate with
   C = delta + sum g_i. This is nonnegative and independent of m and all n_q. Empty
   marking sets and distinct branch points with the same image impose the same formulas.
-/
theorem normalization_jet_codimension
    (k : Type u) [Field k] [IsAlgClosed k] (r : ℕ) (hr : 2 ≤ r)
    (D : Scheme.{u}) [IsReduced D] [Nonempty D]
    (i : D ⟶ ℙ(ULift.{u} (Fin r); Spec (.of k))) [IsClosedImmersion i]
    (hpure : D.IsPureDimension 1)
    (S : ∀ Z : irreducibleComponents D,
      Finset {q : normalizationJetBranch D Z //
        IsClosed ({q} : Set (normalizationJetBranch D Z))}) :
    (∀ Z : irreducibleComponents D,
      Smooth (normalizationJetBranchMap D Z ≫ i ≫
        (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k))) ∧
      IsProper (normalizationJetBranchMap D Z ≫ i ≫
        (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k))) ∧
      IsConnectedCurve (normalizationJetBranchMap D Z ≫ i ≫
        (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k))) ∧
      0 < normalizationJetDegree k
        (i ≫ (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)))
        (ProjectiveSpace.twistRestrict i 1) Z) ∧
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (m : ℕ), 1 ≤ m →
      ∀ (n : ∀ Z : irreducibleComponents D,
        {q : normalizationJetBranch D Z //
          IsClosed ({q} : Set (normalizationJetBranch D Z))} → ℕ),
      (∀ Z : irreducibleComponents D,
        ((∑ q ∈ S Z, n Z q) : ℤ) ≤ m * normalizationJetDegree k
          (i ≫ (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)))
          (ProjectiveSpace.twistRestrict i 1) Z) →
      ∃ U : Submodule k (normalizationJetSections k
          (i ≫ (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)))
          ((ProjectiveSpace.twistRestrict i 1).tensorPow m)),
        (∀ s, s ∈ U ↔ ∀ (Z : irreducibleComponents D), ∀ q ∈ S Z,
          ((Scheme.Modules.pullback (normalizationJetBranchMap D Z)).obj
            ((ProjectiveSpace.twistRestrict i 1).tensorPow m)).presheaf.germ ⊤ q.val trivial
              (AlgebraicGeometry.pullbackΓ (normalizationJetBranchMap D Z)
                ((ProjectiveSpace.twistRestrict i 1).tensorPow m) s) ∈
            (IsLocalRing.maximalIdeal ((normalizationJetBranch D Z).presheaf.stalk q.val)) ^
              n Z q • (⊤ : Submodule ((normalizationJetBranch D Z).presheaf.stalk q.val)
                (((Scheme.Modules.pullback (normalizationJetBranchMap D Z)).obj
                  ((ProjectiveSpace.twistRestrict i 1).tensorPow m)).presheaf.stalk q.val))) ∧
        (Module.finrank k (normalizationJetSections k
            (i ≫ (ℙ(ULift.{u} (Fin r); Spec (.of k)) ↘ Spec (.of k)))
            ((ProjectiveSpace.twistRestrict i 1).tensorPow m)) : ℝ) -
          (Module.finrank k U : ℝ) ≥
            (∑ᶠ Z : irreducibleComponents D, ((∑ q ∈ S Z, n Z q) : ℝ)) - c := by
  sorry

end AlgebraicGeometry
