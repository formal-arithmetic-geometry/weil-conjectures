/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSectionsCupWeilTransport.CondensedSectionsCupWeilTransportDefs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-! Triviality of a coefficient line over the geometric point.

Source: the coefficient-line sub-step of the Frobenius pairing proof in blueprint latest.
(blueprint: lem-pod-condensed-degree-zero-line-trivialization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
attribute [local instance 30000] CategoryTheory.Functor.monObjObj
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

namespace AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport

set_option maxHeartbeats 0 in
-- Coefficient extension and the pullback compositor carry large instance arguments.
private theorem locallyFreeRankOne_trivial
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of D.k))))
    (hL : LocallyFreeRankOne L) : Nonempty (L ≅ 𝟙_ _) := by
  classical
  obtain ⟨𝒰, hframe⟩ := hL
  have hmem := (show Scheme.proetalePrecoverage ≤ Scheme.precoverage @WeaklyEtale from
    inf_le_right) _ 𝒰.mem₀
  have hc := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp hmem
  obtain ⟨i, x, _⟩ := hc.1 (IsLocalRing.closedPoint D.k)
  have : WeaklyEtale (𝒰.f i) := hc.2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (𝒰.f i) x
  obtain ⟨e⟩ := hframe i
  let e' := (Mod.extendScalars (condensedPullbackHom Λ (𝒰.f i))).mapIso e
  let P := CondensedRing.upperStar Λ (𝒰.f i)
  let Q := CondensedRing.upperStar Λ σ
  let κ : P ⋙ Q ≅ 𝟭 _ :=
    (CondensedRing.upperStarComp Λ σ (𝒰.f i)).symm ≪≫
      eqToIso (congrArg (CondensedRing.upperStar Λ) hσ) ≪≫
      CondensedRing.upperStarId Λ (Spec (.of D.k))
  exact ⟨(κ.app L).symm ≪≫ Q.mapIso e' ≪≫ κ.app (𝟙_ _)⟩

set_option maxHeartbeats 0 in
-- The pullback coefficient and derived module instances require extra elaboration.
/-- A degree-zero pro-etale locally free rank-one coefficient line over the geometric
point is globally isomorphic to the tensor unit. No compatibility of the chosen frame
with the supplied Weil datum is required.

Source: `sk-thm-frobenius`, coefficient-line paragraph of Step 1 of
`thm-pod-equivariance-of-the-twisted-pairing.proof.md` in blueprint latest.
(blueprint: lem-pod-condensed-degree-zero-line-trivialization).

Proof: a member of a pro-etale cover contains a point over the unique closed point.
It is weakly etale, so it has a section over the algebraically closed field. Extend
scalars on the local frame to the fixed condensed coefficient sheaf, pull it back
along this section, and use the native pullback composition and identity comparisons.
This gives a frame of the original module. Applying the degree-zero single functor
and its defining tensor-unit identification gives the derived frame. -/
theorem degreeZeroLine_trivial
    {D : WeilConjectures.FiniteFieldDatum.{u}}
    {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ]
    (L : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1})
        (condensedRingObj Λ (Spec (.of D.k)))))
    (hL : DegreeZeroLine L) : Nonempty (L ≅ 𝟙_ _) := by
  obtain ⟨L₀, hL₀, ⟨e₀⟩⟩ := hL
  obtain ⟨e⟩ := locallyFreeRankOne_trivial (D := D) L₀ hL₀
  exact ⟨e₀.symm ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e ≪≫
    DerivedCategory.singleFunctorObjUnitIso _⟩

end AlgebraicGeometry.ProEtale.CondensedSectionsCupWeilTransport
