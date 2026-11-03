/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantStratifiedZariskiLocality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralRestriction.IntegralRestrictionBoundedDescent

/-! # Finite affine descent of bounded constant-model constructibility

Source: the finite-cover descent argument in
`lem-pod-condensed-six-operation-preservation`, steps 1--2.
(blueprint: lem-pod-constant-model-finite-affine-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Boundedness and finite constant models descend from a finite affine cover.

Source: Stacks Tag 095E (finite affine cover) and the finite-cover descent step of
`lem-pod-condensed-six-operation-preservation`.
(blueprint: lem-pod-constant-model-finite-affine-descent).

Proof: descend boundedness by `bounded_finiteOpenDescent`. Exact open restriction
commutes with cohomology, so each cohomology module has finite constant local models
on the given cover. Glue its finite stratifications with
`stratified_of_affine_cover`, and use the qcqs clause of the constructibility definition.
The finite index set may be empty: both descent lemmas include the empty scheme case. -/
theorem constantModelBoundedConstructible_finiteAffineDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⋃ i, (U i : Set X)) = Set.univ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (hK : ∀ i, constantModelBoundedConstructible Λ (U i).toScheme
      ((upperStar Λ (U i).ι).mapDerivedCategory.obj K)) :
    constantModelBoundedConstructible Λ X K := by
  have hu : iSup U = ⊤ := by
    apply SetLike.coe_injective
    simpa only [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top] using hcover
  refine ⟨IntegralCompactSupport.IntegralRestriction.bounded_finiteOpenDescent
    Λ X (Fin n) U hu K (fun i ↦ ?_), fun q ↦ ?_⟩
  · exact DerivedCategory.TStructure.t.bounded.prop_of_iso
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ (U i).ι).app K).symm (hK i).1
  · rw [show IsConstantModelConstructible Λ X _ = IsFiniteConstantStratified Λ X _ from
      if_pos ⟨inferInstance, inferInstance⟩]
    apply stratified_of_affine_cover Λ n U hU hcover
    intro i
    let : IsAffine (U i).toScheme := hU i
    have h := (hK i).2 q
    have := (constantModelConstructibleFiniteTor_wellDefined Λ (U i).toScheme).1
    have h' := ObjectProperty.prop_of_iso (IsConstantModelConstructible Λ (U i).toScheme)
      (((upperStar Λ (U i).ι).mapDerivedCategoryHomologyFunctorIso q).app K).symm h
    exact (show IsConstantModelConstructible Λ (U i).toScheme _ =
      IsFiniteConstantStratified Λ (U i).toScheme _ from
      if_pos ⟨inferInstance, inferInstance⟩) ▸ h'

end AlgebraicGeometry.ProEtale.CondensedRing
