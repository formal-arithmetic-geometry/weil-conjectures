/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData

import WeilConjectures.AlgebraicGeometry.LocalizingClosureCtfEqualsBc
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Components of the integral direct-image tower argument -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Realize an arbitrary finite coefficient extension inside the fixed algebraic closure.
private theorem integral_coefficient_iso :
    ∃ F : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (spIntegralCondensed l E) ≅
        Mon.mk (Profinite.padicIntegersRingObj l F)) := by
  let f : E →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let : FiniteDimensional ℚ_[l] F := F.property
  let e : E ≃ₐ[ℚ_[l]] F := f.equivFieldRange
  let := spectralNorm.normedField ℚ_[l] E
  let := PadicAlgCl.normedFieldOfAlgebra l F
  have hn (x : E) : Padic.coefficientExtensionAbsoluteValue l E x = ‖f x‖ := by
    let a : AbsoluteValue E ℝ :=
      { toFun := fun x ↦ ‖f x‖
        map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
        nonneg' := fun x ↦ norm_nonneg _
        eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
        add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
    have ha (y : ℚ_[l]) : a (algebraMap ℚ_[l] E y) = ‖y‖ := by
      change ‖f (algebraMap ℚ_[l] E y)‖ = ‖y‖
      rw [f.commutes]
      exact PadicAlgCl.norm_extends l y
    exact (spectralNorm_unique_field_norm_ext ha x).symm
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔
      e x ∈ PadicAlgCl.integers l F := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
    rw [hn] at h
    exact h.trans (by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
      rfl)
  let t : Padic.coefficientExtensionIntegers l E ≃+* PadicAlgCl.integers l F :=
    { toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, (hm _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    change ‖f x.val - f y.val‖ = Padic.coefficientExtensionAbsoluteValue l E (x.val - y.val)
    rw [← map_sub, hn]
  have hti : Continuous t.symm := (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  let q : Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) ≅
      Profinite.padicIntegersCondensedRing.{u} l F :=
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.toRingHom.compLeftContinuous _ ht.continuous).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.symm.toRingHom.compLeftContinuous _ hti).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.symm_apply_apply (x.down z)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.apply_symm_apply (x.down z) }
  let G := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  exact ⟨F, ⟨Mon.mkIso' (G.mapIso q)⟩⟩

/-- Restrict compactification coherence to integral bounded constructible objects.
Source: blueprint latest direct-image.proof.md paragraph (2), independence sentence.
Proof: the schemes are qcqs and the integral coefficients are admissible. The integral-model
criterion identifies bounded constructible objects with finite-Tor constructible objects,
which lie in the ambient localizing closure. Apply compactification_coherence_cocycle and
whisker its comparisons with this full-subcategory inclusion. Every compactification open
is quasi-compact by QuasiCompact.of_comp, so it defines a boundary compactification.
Transport along these canonical lifts. Their underlying compactifications are unchanged;
the identity, cocycle and dense-refinement normalization equations therefore restrict
componentwise. Empty schemes and equal compactifications require no exception.
(blueprint: lem-sp-integral-tower-constructible-coherence). -/
theorem constructible_compactification_coherence :
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    ∃ φ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₂,
      (∀ c : Compactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) ∧
      ∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f)
        (h₁ : r.obj ⟶ c₁) (h₂ : r.obj ⟶ c₂) (M : Constructible l E X),
        (φ c₁.obj.obj c₂.obj.obj).hom.app M ≫
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₂ M.obj =
        CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₁ M.obj
 := by
  intro k _ _ _ X Y _ _ _ _ _ _ _ _ f _ d _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : IsSeparated (f ≫ Y ↘ Spec (.of k)) := by
    rw [comp_over]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType (f ≫ Y ↘ Spec (.of k)) := by
    rw [CategoryTheory.comp_over f (Spec (.of k))]
    infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (Y ↘ Spec (.of k))
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  obtain ⟨F, hF⟩ := integral_coefficient_iso l E
  have hΛ : IsLocalizingAdmissibleCoefficient l (spIntegralCondensed l E) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, hF⟩))))
  have heq := (localizingClosure_ctf_equals_bc l X (spIntegralCondensed l E)
    (Or.inr (Or.inr (Or.inl ⟨F, Or.inl hF⟩)))).1.2.2.1
  have hloc (M : Constructible l E X) :
      localizingClosureProEtale (spIntegralCondensed l E) X M.obj := by
    intro P _ hP
    apply hP M.obj
    change (constantModelBoundedConstructible (spIntegralCondensed l E) X ⊓
      DerivedCategory.finiteTorAmplitude _) M.obj
    rw [heq]
    exact M.property
  let ι : Constructible l E X ⥤
      (localizingClosureProEtale (spIntegralCondensed l E) X).FullSubcategory :=
    { obj := fun M ↦ ⟨M.obj, hloc M⟩
      map := fun a ↦ ObjectProperty.homMk a.hom }
  let lift (c : Compactification f) : Compactification.BoundaryCompactification f :=
    ⟨⟨c, c.quasiCompact_openImmersion inferInstance⟩⟩
  obtain ⟨φ, _, hn, hi, hc⟩ :=
    CondensedRing.compactification_coherence_cocycle (spIntegralCondensed l E) l hΛ k f
  refine ⟨fun c₁ c₂ ↦ Functor.isoWhiskerLeft ι (φ (lift c₁) (lift c₂)), ?_, ?_, ?_⟩
  · intro c
    change Functor.isoWhiskerLeft ι (φ (lift c) (lift c)) = _
    rw [hi (lift c)]
    exact Functor.isoWhiskerLeft_refl _ _
  · intro c₁ c₂ c₃
    rw [← Functor.isoWhiskerLeft_trans, hc]
  · intro c₁ c₂ r h₁ h₂ M
    exact hn c₁ c₂ r h₁ h₂ (ι.obj M)

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
