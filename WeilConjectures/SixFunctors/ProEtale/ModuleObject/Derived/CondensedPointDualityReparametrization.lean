/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointDualComparisonData
import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-! # Reparametrization coherence for condensed point evaluation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]
  (I : Type w) [Finite I]

/-- Canonical reindexing of sections, built from component pullback composition and
the canonical trivialization of an automorphism of an algebraically closed point.
Source: blueprint Step 5, Frobenius-equivariance paragraph.
(blueprint: lem-a1-condensed-point-duality-reparametrization) -/
noncomputable def condensedBoundaryCanonicalReindexIso
    (e : Equiv.Perm I) (σ : k ≃+* k) (t : I) :
    condensedBoundarySections ℓ k I (e t) ≅
      condensedBoundaryPermutationPullback ℓ k I e σ ⋙
        condensedBoundarySections ℓ k I t := by
  let τ := upperStarIsoIdOfIsSepClosed
    (Profinite.padicAlgClRingObj ℓ) (Spec.map (CommRingCat.ofHom σ.toRingHom))
  let r := condensedBoundaryReparametrizationRestriction ℓ k I e σ t
  exact Functor.isoWhiskerRight
    ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (condensedBoundaryRestriction ℓ k I (e t)) τ.symm ≪≫ r.symm)
    (pointSections ℓ k) ≪≫ Functor.associator _ _ _

/-- Monoidality of the canonical derived reindexing.
Source: blueprint local boundary duality, Step 5, Frobenius-equivariance paragraph.

Proof: the component pullback-composition isomorphism respects the coefficient unit
and multiplication. The canonical trivialization of field-automorphism pullback is
also monoidal: under the equivalence with condensed modules it is the identity on
coefficients and modules. The section formula already proved above identifies the
reindexing with the composite of these two maps. The section unit normalization gives
its unit equation, and the section tensor normalization gives its tensor equation
on pure tensors. Pure tensors span, so the tensor equation holds as a module map.
Apply this degreewise to complexes. The inclusions of the pairs of degrees into the
total tensor are jointly epimorphic; the equations in complex_tensor therefore
identify the two total-complex comparison maps. Choose K-flat resolutions of the
two source complexes to compute derived tensor, so that the source localization's
tensor comparison is invertible. The equations in complex_tensor identify the
chosen fiber tensor maps with the localized total-complex maps; naturality of the
localization factors and the exact/left-derived pullback comparison identifies
the resulting natural isomorphism with condensedBoundaryReindexIso. Cancel these
invertible comparison maps to obtain its tensor equation. The unit equation follows
in the same way from complex_unit and fiber_unit. Transport along the resolution
isomorphisms proves both equations for all derived objects. Empty component sets
make the assertion vacuous; zero complexes satisfy the same equations.
(blueprint: lem-a1-condensed-point-duality-reparametrization)
-/
theorem condensed_point_duality_reparametrization
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    [s : CondensedBoundaryEvaluationTensor ℓ k I]
    (hs : IsCanonicalCondensedBoundaryEvaluationTensor ℓ k I) :
    ∀ (e : Equiv.Perm I) (σ : k ≃+* k) (t : I),
      CondensedBoundaryReindexSectionNormalization ℓ k I e σ t
          (condensedBoundaryCanonicalReindexIso ℓ k I e σ t) ∧
      CondensedBoundaryReindexMonoidal ℓ k I e σ t
          (condensedBoundaryCanonicalReindexIso ℓ k I e σ t) ∧
      CondensedBoundaryReindexDualNormalization ℓ k I e σ t
          (condensedBoundaryCanonicalReindexIso ℓ k I e σ t) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
