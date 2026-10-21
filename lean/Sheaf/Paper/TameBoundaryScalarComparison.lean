/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.AllContinuousScalarMate
public import Sheaf.Paper.StrictLocalKummerTameModule
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Algebra.Homology.FiniteFreeMonoCokernelKFlat
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.ExactOpenClosedUnboundedCalculus

/-!
# Tame strict-normal-crossing boundary scalar comparison

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), all-continuous tame-pair comparison obligation.
(blueprint: lem-sfb-continuous-algcl-tame-boundary-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- Use the component family already furnished by the SNC boundary definition. Every
subset of this finite family is allowed as the outer boundary, so the enumeration is
immaterial. Source: direct-image proof paragraph (3), pair data
(blueprint: lem-sfb-continuous-algcl-tame-boundary-comparison). -/
abbrev tameBoundaryComponents {Y : Scheme.{u}} (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) :
    Fin hD.2.2.choose → Y.IdealSheafData :=
  hD.2.2.choose_spec.choose

/-- Scalar extension to all continuous algebraic-closure coefficients commutes with the
open direct image of the inner extension by zero of a tame lisse module.
Source: direct-image proof paragraph (3), tame-pair local calculation
(blueprint: lem-sfb-continuous-algcl-tame-boundary-comparison).

Proof, following the eight DAG steps:
1. L is locally finite free. Scalar extension of L[0] is L_Omega[0], preserving the
scalar unit. The conjugate open-scalar isomorphism carries T(b_!L[0]) to b_!L_Omega[0]
on the whole unbounded category (def-sfb-derived-open-immersion-shriek-iso and
lem-pur-sheaf-ring-derived-coefficient-adjunction).
2. Remove the inner components to form c:Y° -> Y and a:W -> Y°. The transverse tame
exchange c_!Ra_*L_F = Rj_*b_!L_F holds for E and Omega and vanishes at the inner boundary
(lem-sfb-transverse-tame-open-shriek-exchange).
3. On each SNC stratum choose the common pro-etale cover and tame inertia representation
provided by lem-sfb-tame-stratum-kummer-descent. They model restrictions on entire strata
for both coefficients, including the empty-boundary stratum.
4. lem-sfb-tame-inertia-continuous-koszul computes these derived invariants by the finite
Koszul complex of rho(gamma_i)-1 on M^H. The finite prime-to-ell image of H permits the
averaging idempotent. Its coefficient map is the termwise inclusion.
5. Choose an E-basis of M^H. The Koszul terms are finite free and the differentials are
matrices over E. Its finite split stupid filtration proves K-flatness from the finite
free case (lem-sfb-finite-free-mono-cokernel-kflat, def-pc-kflat-complex). The total
complex of def-pc-tensor-complex-sheaves thus computes derived scalar extension, and
z tensor (x_I) maps to (z x_I), preserving matrices and signs. The representative
comparison is lem-pur-sheaf-ring-derived-coefficient-adjunction. Rank zero or r=0 works.
6. Unit normalization identifies this finite-matrix map with the prescribed beta_a.
Use the two Kummer/Koszul normalization clauses, the K-flat pullback comparison of
lem-sfb-kflat-scalar-comparison-normalization, and the scalar adjunction of
lem-weil-pbc-ring-sheaf-change-adjunction. Both transposes are the direct-image counit
followed by x mapping to 1 tensor x, hence agree by adjunction uniqueness.
7. The stratum covers detect isomorphisms by lem-zl-condensed-cover-restriction-conservative.
Filter by closed unions of loci on at least m components. Successive differences are
disjoint open-and-closed strata. Finite induction using lem-weil-pbc-proetale-ringed-open-closed
and lem-sfb-exact-open-closed-unbounded-calculus kills the cone of beta_a.
8. Naturality of the transverse exchange for L -> Res L_Omega, together with open-scalar
compatibility and the scalar-restriction/direct-image adjunction, identifies beta_j with
c_! beta_a. Its units are the same as in step 6. Every surrounding comparison is
invertible, so beta_j is invertible. Empty inner or outer boundary gives the same
identity/open-unit exchange. No singular or wild case is asserted. -/
theorem tameBoundaryScalarComparison_isIso
    (p : ℕ) [Fact p.Prime] (_hpℓ : p ≠ ℓ) (k : Type u) [Field k] [CharP k p]
    (Y V W : Scheme.{u})
    [Y.Over (Spec (.of k))] [V.Over (Spec (.of k))] [W.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    [LocallyOfFiniteType (W ↘ Spec (.of k))] [QuasiCompact (W ↘ Spec (.of k))]
    [IsSeparated (W ↘ Spec (.of k))]
    (_hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D) (out : Finset (Fin hD.2.2.choose))
    (j : V ⟶ Y) [IsOpenImmersion j] [j.IsOver (Spec (.of k))]
    (b : W ⟶ V) [IsOpenImmersion b] [b.IsOver (Spec (.of k))]
    (_hj : Set.range j =
      (⋃ a ∈ out, ((tameBoundaryComponents D hD a).support : Set Y))ᶜ)
    (_hb : Set.range (b ≫ j) = (D.support : Set Y)ᶜ)
    (L : Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) W))
    (_hL : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) L)
    (_htame : IsStrictLocalKummerTameModule p
      (Profinite.continuousMapRingObj E.1) D (b ≫ j) L) :
    IsIso (tameBoundaryScalarComparison ℓ E j
      ((DerivedCategory.singleFunctor _ 0).obj
        ((openImmersionLowerShriek (Profinite.continuousMapRingObj E.1) b).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
