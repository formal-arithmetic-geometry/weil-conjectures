/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.DeligneLaumon.CondensedClopenCompact.CondensedClopenCompactDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.CondensedLisseExtensionInertia.CondensedLisseExtensionInertia
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # The geometric fibre identification for a constant extension

Source: latest blueprint, infinity reduction, the first sentence of the proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The geometric map of the literal finite constant extension is an isomorphism.
Source: latest blueprint, sk-lem-wft-infinity-reduction, opening sentence
(blueprint: lem-wft-infinity-constant-fiber-iso).

Proof: the inclusion k₀ → k_m followed by k_m → k is the fixed inclusion k₀ → k.
Applying Spec gives the same composite on bases. The pasting isomorphism for two
successive pullbacks therefore identifies the iterated geometric fibre with the
original one. The two projection equations identify its forward arrow with the
published native geometric map. This includes empty schemes and degree one. -/
theorem infinity_constant_extension_geometricMap_isIso
    (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    IsIso (constantExtensionGeometricMap D m hm X₀
      (infinityConstantExtensionModel D m hm X₀)
      (infinityConstantExtensionProjection D m hm X₀)) := by
  let b := Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))
  let c := Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)
  have hs : c ≫ b = Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)) := by
    have hc : (D.extensionSubfield m hm).subtype.comp (D.extensionEmbedding m hm) =
        algebraMap D.k₀ D.k :=
      (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
        D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  let e := pullbackLeftPullbackSndIso X₀.hom b c ≪≫ pullback.congrHom rfl hs
  have he : constantExtensionGeometricMap D m hm X₀
      (infinityConstantExtensionModel D m hm X₀)
      (infinityConstantExtensionProjection D m hm X₀) = e.hom := by
    apply pullback.hom_ext
    · simp [constantExtensionGeometricMap, NativeCondensedPullback.geometricMap,
        infinityConstantExtensionProjection, infinityConstantExtensionModel,
        FiniteFieldDatum.geometricFiber, NativeCondensedPullback.constantExtensionDatum,
        e, Over.pullback, pullback.congrHom]
      rfl
    · simp [constantExtensionGeometricMap, NativeCondensedPullback.geometricMap,
        infinityConstantExtensionProjection, infinityConstantExtensionModel,
        FiniteFieldDatum.geometricFiber, NativeCondensedPullback.constantExtensionDatum,
        e, Over.pullback, pullback.congrHom]
      rfl
  rw [he]
  infer_instance

end WeilConjectures
