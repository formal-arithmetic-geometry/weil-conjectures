/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateTransitivity
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTateBasis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor

/-! # Native integral Tate-line scalar transport

Source: latest blueprint, prop-weil-twist-preserves, first paragraph and local
rank-one argument; thm-pur-finite-reduction-of-purity, Step 2.
(blueprint: lem-pur-integral-tensor-transport).

All coefficients are continuous condensed coefficients, pulled to the small
pro-etale site. All derived operations are ordinary and uncompleted. The old
arithmetic inclusion is used only as a ring homomorphism into the valuation ring;
no discrete/condensed comparison is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 10000
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

-- Fix the site size in the coefficient universe before elaborating scalar adjunctions.
-- This is Mathlib's canonical witness, with no extra unconstrained size universe.
private local instance nativeSiteSmall (T : AlgebraicGeometry.Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ₀ Λ₁ Λ₂ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]
  [MonObj Λ₂] [IsCommMonObj Λ₂]

end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {Λ₀ Λ₁ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ₀] [IsCommMonObj Λ₀] [MonObj Λ₁] [IsCommMonObj Λ₁]

end AlgebraicGeometry.ProEtale.QuotientChange

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.NativeIntegralTensorTransport
open QuotientChange

variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[ell] E] [FiniteDimensional ℚ_[ell] E]

/-- Continuity of the canonical valuation-ring inclusion. Its composite into E
is the continuous field inclusion restricted to Z_ell.
Source: prop-weil-twist-preserves, scalar extension of the first twist
(blueprint: lem-pur-integral-tensor-transport).
Proof: the characterization of purTwistIntegersMap in E identifies the composite
with algebraMap Q_ell E composed with the continuous subtype map Z_ell to Q_ell.
The spectral norm makes the field inclusion an isometry. The valuation ring has
the subtype topology, so continuity of the composite proves the assertion. -/
theorem integralInclusion_continuous :
    letI := spectralNorm.normedField ℚ_[ell] E
    Continuous (Scheme.purTwistIntegersMap ell E) := by
  let := spectralNorm.normedField ℚ_[ell] E
  let := spectralNorm.normedAlgebra ℚ_[ell] E
  apply continuous_induced_rng.mpr
  have hm : (fun z : ℤ_[ell] ↦ (Scheme.purTwistIntegersMap ell E z : E)) =
      (algebraMap ℚ_[ell] E) ∘ (fun z : ℤ_[ell] ↦ (z : ℚ_[ell])) := by
    funext z
    exact (Scheme.purTwistIntegersMap_existsUnique ell E).exists.choose_spec z
  change Continuous (fun z : ℤ_[ell] ↦ (Scheme.purTwistIntegersMap ell E z : E))
  rw [hm]
  exact (continuous_algebraMap ℚ_[ell] E).comp continuous_subtype_val

/-- The specified continuous condensed map Z_ell to O_E, by postcomposition.
Source: prop-weil-twist-preserves, scalar extension of the first twist
(blueprint: lem-pur-integral-tensor-transport). -/
def integralMap : Profinite.continuousMapRingObj.{u} ℤ_[ell] ⟶ twistIntegralRing ell E :=
  letI := spectralNorm.normedField ℚ_[ell] E
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (⟨{ app := fun S ↦ RingCat.ofHom
            (ULift.ringEquiv.symm.toRingHom.comp
              (((Scheme.purTwistIntegersMap ell E).compLeftContinuous S.unop
                (integralInclusion_continuous ell E)).comp ULift.ringEquiv.toRingHom))
          naturality := fun _ _ _ ↦ rfl }⟩)

/-- N_T = B_T tensor over R_T with the native root-limit line.
Source: prop-weil-twist-preserves (blueprint: lem-pur-integral-tensor-transport). -/
abbrev line (T : Scheme.{u}) :=
  (extension (integralMap ell E) T).obj (tateModule T ell)

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]

/-- The actual scalar transport: inverse ordinary balancing followed by extension
of the supplied comparison. Source: prop-weil-twist-preserves
(blueprint: lem-pur-integral-tensor-transport). -/
def transport (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (h : X ⟶ Y)
    {M : Modules R Y} {N : Modules R X}
    (tau : (CondensedRing.upperStar R h).obj M ≅ N) :
    (CondensedRing.upperStar S h).obj ((extension a Y).obj M) ≅
      (extension a X).obj N :=
  (CondensedRing.pullIso a h).symm.app M ≪≫ (extension a X).mapIso tau

/-- The actual inverse-image adjunct on underlying abelian sheaves.
Source: Cartesian coefficients (blueprint: lem-pur-integral-tensor-transport). -/
abbrev adjunct {X Y : Scheme.{u}} (h : X ⟶ Y) {M : Modules R Y} {N : Modules R X}
    (v : (CondensedRing.upperStar R h).obj M ⟶ N) :=
  ((CondensedRing.upperStarLowerStarAdjunction R h).homEquiv M N v).hom

omit [IsCommMonObj S] in
attribute [local instance] proofSectionDerived

set_option maxHeartbeats 2000000 in
-- The three normalized coefficient comparisons require a larger elaboration budget.

end AlgebraicGeometry.ProEtale.NativeIntegralTensorTransport
