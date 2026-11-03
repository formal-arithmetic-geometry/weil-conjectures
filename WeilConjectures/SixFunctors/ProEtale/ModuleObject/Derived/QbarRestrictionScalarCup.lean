/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CondensedPointCupConstruction.ExactMonoidalSectionsCup
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TensorRestriction.TwistedActionTensorRestrictionSupplement
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-! # Normalized exact cup for a scalar coordinate isomorphism
Source: scalar-coordinate transport in point-fibre coherence.
(blueprint: lem-sf-qbar-restriction-scalar-cup).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The balanced scalar restriction cup with all chain and localization squares.
Source: scalar-coordinate transport, Step 1 of rational point-fibre coherence
(blueprint: lem-sf-qbar-restriction-scalar-cup).

Proof: restriction along a ring isomorphism is an exact equivalence. Its ordinary
lax tensorator sends x tensor y to x tensor y and its unit is the ring map. Both
are invertible, so the exact strong monoidal cup construction applies. Retaining
its ordinary structure proves the two displayed formulas. -/
theorem qbarRestrictionScalarCup {R S : Type (u + 1)} [CommRing R] [CommRing S]
    (e : R ≃+* S)
    [PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} e.toRingHom)]
    [PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} e.toRingHom)] :
    ∃ d : ExactSectionsDerivedCup.{u + 2, u + 1, u + 1, u + 1, u + 1}
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} e.toRingHom),
      (∀ (M N : ModuleCat.{u + 1} S) (x : M) (y : N),
        (d.ordinary.μ M N) (x ⊗ₜ[R] y) = x ⊗ₜ[S] y) ∧
      ∀ r : R, d.ordinary.ε r = e r := by
  let G : ModuleCat.{u + 1} S ⥤ ModuleCat.{u + 1} R :=
    ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} e.toRingHom
  have : G.IsLeftAdjoint :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1, u + 1, u + 1}
      e).toAdjunction.isLeftAdjoint
  have : G.IsRightAdjoint :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u + 1, u + 1, u + 1}
      e).symm.toAdjunction.isRightAdjoint
  have : PreservesColimitsOfSize.{0, 0} G := by infer_instance
  have hε : IsIso (Functor.LaxMonoidal.ε G) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (show R → S from Functor.LaxMonoidal.ε G)
    have h : (show R → S from Functor.LaxMonoidal.ε G) = e :=
      funext (ModuleCat.restrictScalars_η e.toRingHom)
    rw [h]
    exact e.bijective
  have hμ (M N : ModuleCat.{u + 1} S) : IsIso (Functor.LaxMonoidal.μ G M N) :=
    CategoryTheory.TwistedActionRingedSite.TensorRestriction.restrictScalars_mu_isIso
      R S e.toRingHom M N e.bijective
  let := Functor.Monoidal.ofLaxMonoidal G
  let := Functor.preservesFlat_of_isEquivalence G
  obtain ⟨d, hd⟩ := CategoryTheory.CondensedPointCupConstruction.exact_monoidal_sections_cup
    G (inferInstance : G.Monoidal)
  refine ⟨d, ?_, ?_⟩
  · intro M N x y
    rw [hd]
    exact ModuleCat.restrictScalars_μ_tmul e.toRingHom M N x y
  · intro r
    rw [hd]
    exact ModuleCat.restrictScalars_η e.toRingHom r

end AlgebraicGeometry.ProEtale.CondensedRing
