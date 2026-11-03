/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteTraceGlobalOperator
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompCompositionWitnesses

/-! # Left identity composition for an arbitrary identity compactification

The composition-independence and normalized identity laws of
sk-thm-sf-comp-composition identify the left identity compositor for every chosen
compactification of the identity. This calculation is kept here so callers use its
proved equation without importing the implementation of the chosen witness package.
Source: latest blueprint, sk-thm-sf-comp-composition, canonicity and identity verification
(blueprint: lem-trf-graph-composition-identity).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

attribute [local irreducible] compCompositionWitnesses DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

set_option maxHeartbeats 2000000 in
-- Instantiating the dependent witness laws needs this elaboration budget.
/-- Left identity composition with any compactification of the identity. Apply
compactification independence, remove the two identity comparisons, and use the normalized
left identity law. Source: sk-thm-sf-comp-composition, identity and independence clauses
(blueprint: lem-trf-graph-composition-identity). -/
theorem finiteTrfGraphCompositionUnitLeft
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (d : Compactification (𝟙 X.obj.left))
    (K : (localizingClosureProEtale Λ X.obj.left).FullSubcategory) :
    let W := compCompositionWitnesses ell k hk Λ hΛ
    (W.comp (𝟙 X) f d c (c.copy (Category.id_comp f.hom.left))).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map
        ((W.comparison (𝟙 X) d (Compactification.ofIsProper (𝟙 X.obj.left))).hom.app K ≫
          (CompactSupportComposition.identity Λ X.obj.left).hom.app K.obj) := by
  let W := compCompositionWitnesses ell k hk Λ hΛ
  let e := c.copy (Category.id_comp f.hom.left)
  let d' := Compactification.ofIsProper (𝟙 X.obj.left)
  have laws := (sk_thm_sf_comp_composition_witnesses ell k hk Λ hΛ).choose_spec
  have hi : (W.comp (𝟙 X) f d c e).hom.app K ≫
      (W.comparison ((𝟙 X) ≫ f) e e).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map
          ((W.comparison (𝟙 X) d d').hom.app K) ≫
        (W.comparison f c c).hom.app
          ⟨_, (W.preserves (𝟙 X) d').1 K.obj K.property⟩ ≫
        (W.comp (𝟙 X) f d' c e).hom.app K := by
    dsimp only [W]
    unfold compCompositionWitnesses
    exact laws.2.2.2.2.1 (𝟙 X) f d d' c c e e K
  have hcid1 : W.comparison ((𝟙 X) ≫ f) e e = Iso.refl _ := by
    dsimp only [W]
    unfold compCompositionWitnesses
    exact laws.2.1 ((𝟙 X) ≫ f) e
  have hcid2 : W.comparison f c c = Iso.refl _ := by
    dsimp only [W]
    unfold compCompositionWitnesses
    exact laws.2.1 f c
  have hu : (W.comp (𝟙 X) f d' c e).hom.app K =
      (rightDerivedLowerShriekOfCompactification Λ c).map
        ((CompactSupportComposition.identity Λ X.obj.left).hom.app K.obj) := by
    dsimp only [W]
    unfold compCompositionWitnesses
    exact laws.2.2.2.2.2.1 f c K
  simp only [hcid1, hcid2, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_obj, ObjectProperty.ι_obj, Category.comp_id, Category.id_comp] at hi
  rw [hu] at hi
  let R := rightDerivedLowerShriekOfCompactification Λ c
  exact hi.trans (R.map_comp
    ((W.comparison (𝟙 X) d d').hom.app K)
    ((CompactSupportComposition.identity Λ X.obj.left).hom.app K.obj)).symm

end WeilConjectures
