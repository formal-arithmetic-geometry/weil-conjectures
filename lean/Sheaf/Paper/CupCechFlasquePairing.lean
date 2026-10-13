/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups P3, U3 and S3
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import Sheaf.Paper.ModuleCupResolutionData
import all Sheaf.Paper.ModuleCupPairingExists

/-! # Existence of a flasque computing tensor-paired resolution

Source: Stacks Project, Cohomology of Sheaves, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-cup-cech-flasque-pairing)
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Module sheaves admit computing resolutions with a sectionwise tensor pairing.
Source: Stacks Project, Section 20.31 (0FKU), naive cup product and the
flasque/Godement proof of Lemma 20.31.4 (0FKV).
(blueprint: lem-sc-cup-cech-flasque-pairing)
Proof: take the existential strictly nonnegative flasque integer complexes,
quasi-isomorphic augmentations and tensor cochain map supplied by
moduleCup_godement_pairing. Restrict to natural degrees. On each tensor summand,
tensor sections and apply the supplied chain map; its cochain identity gives
signed Leibniz, and its degree-zero formula gives augmentation_pair. Restrictions
commute because its components are sheaf morphisms. Choose injective resolutions
and extend each augmentation to a comparison degree by degree by injectivity.
moduleCup_flasque_acyclicity makes the supplied terms acyclic, and the separately
cited Leray acyclic-resolution comparison criterion makes every global comparison
homology map invertible. Assemble the fields of CupResolutionPairing.
No specific Godement model or natural choice of the existential complexes is
assumed, and no coefficient flatness is required. -/
theorem exists_cupCechFlasquePairing {X : Scheme.{uM}} (F G : X.Modules) :
    ∃ D : CupResolutionPairing F G,
      (∀ n : ℕ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.left.K.X n))) ∧
      (∀ n : ℕ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.right.K.X n))) ∧
      (∀ n : ℕ, TopCat.Sheaf.IsFlasque
        ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.target.K.X n))) := by
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  obtain ⟨K, L, M, a, b, c, ha, hb, hc, hK, hL, hM, fK, fL, fM, t, ht⟩ :=
    moduleCup_godement_pairing X F G
  have := ha
  have := hb
  have := hc
  have := hK
  have := hL
  have := hM
  have := natAugmentation_quasiIso a
  have := natAugmentation_quasiIso b
  have := natAugmentation_quasiIso c
  refine ⟨{
    left := computingFlasqueResolution _ (natAugmentation a) (fun n ↦ fK n)
    right := computingFlasqueResolution _ (natAugmentation b) (fun n ↦ fL n)
    target := computingFlasqueResolution _ (natAugmentation c) (fun n ↦ fM n)
    pair := tensorChainSectionPair K L M t
    restriction := ?_
    leibniz := ?_
    augmentation_pair := ?_ }, ?_, ?_, ?_⟩
  · intro r s V W h x y
    change (M.X ((r + s : ℕ) : ℤ)).presheaf.map (homOfLE h).op
      (tensorChainSectionPair K L M t r s V x y) =
        tensorChainSectionPair K L M t r s W
          ((K.X (r : ℤ)).presheaf.map (homOfLE h).op x)
          ((L.X (s : ℤ)).presheaf.map (homOfLE h).op y)
    have hres := tensorSection_restriction
      (HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
        (by simp) ≫ t.f _) V W h x y
    simpa only [tensorChainSectionPair_apply, Hom.comp_app,
      ConcreteCategory.comp_apply, app_val_apply] using hres
  · intro r s V x y
    have hs := tensorChain_leibniz K L M t (r : ℤ) (s : ℤ) V x y
    change (M.d ((r + s : ℕ) : ℤ) ((r + s + 1 : ℕ) : ℤ)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
        (show r + 1 + s = r + s + 1 by omega))).val.app (op V)
        (tensorChainSectionPair K L M t (r + 1) s V
          ((K.d (r : ℤ) ((r + 1 : ℕ) : ℤ)).val.app (op V) x) y) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
          (show r + (s + 1) = r + s + 1 by omega))).val.app (op V)
          (tensorChainSectionPair K L M t r (s + 1) V x
            ((L.d (s : ℤ) ((s + 1 : ℕ) : ℤ)).val.app (op V) y))
    rw [tensorChainSectionPair_transport K L M t (r + 1) s (r + s + 1) (by omega),
      tensorChainSectionPair_transport K L M t r (s + 1) (r + s + 1) (by omega),
      tensorChainSectionPair_apply]
    simp only [app_val_apply, Units.smul_def, Int.coe_negOnePow_natCast] at hs
    exact hs
  · intro V x y
    change tensorChainSectionPair K L M t 0 0 V
      (((natAugmentation a).f 0).val.app (op V) x)
      (((natAugmentation b).f 0).val.app (op V) y) =
      ((natAugmentation c).f 0).val.app (op V) (tmulSection x y)
    simp only [natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    rw [tensorChainSectionPair_apply]
    exact ht V x y
  · exact fun n ↦ fK n
  · exact fun n ↦ fL n
  · exact fun n ↦ fM n

end
end AlgebraicGeometry.Scheme.Modules
