/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward
import Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability
import all Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ExceptionalInverseImageExistence
import Sheaf.Paper.RationalRestrictionGlue
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.Paper.CondensedQbarLfpLocalTriviality
import Sheaf.Paper.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Cohomological boundedness of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

-- Normalize the three coefficient families without changing their condensed ring structure.
private noncomputable def continuous_coefficient_iso
    {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hei : Continuous e.symm) :
    Mon.mk (Profinite.continuousMapRingObj.{u} A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let eR : Profinite.continuousMapRingSheaf A ≅ Profinite.continuousMapRingSheaf B :=
    { hom := Profinite.continuousMapRingSheafMap e.toRingHom he
      inv := Profinite.continuousMapRingSheafMap e.symm.toRingHom hei
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact { hom := Mon.ofHom eAb.hom
          inv := Mon.ofHom eAb.inv
          hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
          inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

private lemma continuous_normalize (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F.val)) := by
  let f : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let F := f.fieldRange
  let e : E ≃ₐ[ℚ_[ℓ]] F := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional ℚ_[ℓ] F := e.toLinearEquiv.finiteDimensional
  refine ⟨⟨F, inferInstance⟩, ⟨?_⟩⟩
  exact continuous_coefficient_iso e.toRingEquiv
    e.toLinearMap.continuous_of_finiteDimensional
    e.symm.toLinearMap.continuous_of_finiteDimensional

private lemma integral_normalize (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F.val)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let f := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let F := f.fieldRange
  let e : E ≃ₐ[ℚ_[ℓ]] F := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional ℚ_[ℓ] F := e.toLinearEquiv.finiteDimensional
  have hn (x : E) : ‖e x‖ = ‖x‖ := by
    rfl
  have hm (x : E) : x ∈ PadicAlgCl.integers ℓ E ↔ e x ∈ PadicAlgCl.integers ℓ F := by
    rw [PadicAlgCl.mem_integers_iff, PadicAlgCl.mem_integers_iff]
    change ‖x‖₊ ≤ 1 ↔ ‖e x‖₊ ≤ 1
    exact_mod_cast (show ‖x‖ ≤ 1 ↔ ‖e x‖ ≤ 1 by rw [hn])
  let ei : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F :=
    { toFun := fun x ↦ ⟨e x, (hm x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hm _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hi : Isometry ei := AddMonoidHomClass.isometry_of_norm ei (fun x ↦ hn x)
  have his : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hi (ei.symm x) (ei.symm y)).symm
  exact ⟨⟨F, inferInstance⟩,
    ⟨continuous_coefficient_iso ei hi.continuous his.continuous⟩⟩

-- Compare the local finite-presentation and finite constant-model conventions on strata.
private lemma free_constant_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ j : C.I₀,
      ∃ n : ℕ, Nonempty ((CondensedRing.upperStar Λ (C.f j)).obj M ≅
        Mod.finiteFree (condensedRingObj Λ (C.X j)) n)) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨C, hC⟩ := hM
  refine ⟨C, fun j ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC j
  let F := upperStarFromPoint (C.X j)
  let : PreservesFiniteColimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.2.1
  let : PreservesFiniteColimits F := by dsimp [F, upperStarFromPoint]; infer_instance
  let : PreservesFiniteLimits pointUpperStar.{u} :=
    profinite_point_pullback.2.2.2.2.2.2.2.2.1
  let : PreservesFiniteLimits F := by dsimp [F, upperStarFromPoint]; infer_instance
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let : PreservesFiniteColimits (F.mapMod Λ) := inferInstance
  let : PreservesBinaryBiproducts (F.mapMod Λ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : (F.mapMod Λ).Additive := Functor.additive_of_preservesBinaryBiproducts _
  have eF : (F.mapMod Λ).obj (Mod.finiteFree Λ n) ≅
      Mod.finiteFree (condensedRingObj Λ (C.X j)) n :=
    (F.mapMod Λ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Iso.refl _)
  refine ⟨Mod.finiteFree Λ n, ?_, ⟨e ≪≫ eF.symm⟩⟩
  exact ⟨n, 0, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩

private lemma qbar_lfp_constant_model
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) M) :
    HasFiniteConstantLocalModel (Profinite.padicAlgClRingObj ℓ) X M := by
  exact free_constant_model _ X M (condensedQbar_lfp_locally_free ℓ X M hM)

private lemma qbar_constructible_constant_model
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X))
    (hM : IsConstructibleModuleObject (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X) M) :
    IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  apply qbar_lfp_constant_model
  exact lfp_of_iso (lfp_comap (inv (condensedPullbackHom
    (Profinite.padicAlgClRingObj ℓ) (S.immersion a))) (hS a))
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom
        (Profinite.padicAlgClRingObj ℓ) (S.immersion a))).app _).symm
private lemma finite_lfp_constant_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X))
    (hM : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X) M) :
    HasFiniteConstantLocalModel (Profinite.continuousMapRingObj E.val) X M := by
  apply free_constant_model
  obtain ⟨C, hC⟩ := finite_lf ℓ E X M hM
  refine ⟨C, fun j ↦ ?_⟩
  let φ := condensedPullbackHom (Profinite.continuousMapRingObj E.val) (C.f j)
  have hh := free_comap (inv φ) (hC j)
  exact free_of_iso hh ((Mod.extendScalarsIsoComapInv φ).app _).symm

private lemma finite_constructible_constant_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.continuousMapRingObj E.val) X) M) :
    IsConstantModelConstructible (Profinite.continuousMapRingObj E.val) X M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let : TopologicalSpace.NoetherianSpace (S.domain a) :=
    (S.immersion a).isEmbedding.isInducing.noetherianSpace
  apply finite_lfp_constant_model ℓ E
  exact lfp_of_iso (lfp_comap (inv (condensedPullbackHom
    (Profinite.continuousMapRingObj E.val) (S.immersion a))) (hS a))
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom
        (Profinite.continuousMapRingObj E.val) (S.immersion a))).app _).symm

private lemma integral_constructible_iff_constant_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) :
    IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) M ↔
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M := by
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  have hp := integralLfpConstantModelComparison ℓ (ULift.{u} E.val) X
    ((Mod.comap ψ).obj M)
  refine Iff.trans ?_ (hp.trans (constantModel_comap_iff φ X M))
  constructor
  · exact _root_.constructible_comap ψ
  · intro h
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
        Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)

private lemma constant_model_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  let φ := condensedPullbackHom Λ (S.immersion a)
  apply lfp_of_comap (inv φ)
  exact lfp_of_iso ((hS a).isLocallyFinitelyPresented _)
    ((Mod.extendScalarsIsoComapInv φ).app _)

private lemma coefficient_constructible_comparison
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X),
      IsConstructibleModuleObject (condensedRingObj Λ' X) M →
      IsConstantModelConstructible Λ' X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstructibleModuleObject (condensedRingObj Λ X) M) :
    IsConstantModelConstructible Λ X M := by
  let φ := e.inv.hom
  have : IsIso φ := inferInstanceAs (IsIso ((Mon.forget _).map e.inv))
  apply (constantModel_comap_iff φ X M).mp
  exact h _ (_root_.constructible_comap (coefficientMap φ X) hM)

private lemma bounded_constructible_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M →
      IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  funext K
  apply propext
  constructor
  · intro hK
    exact ⟨hK.1, fun n ↦ constant_model_constructible Λ X _ (hK.2 n)⟩
  · intro hK
    exact ⟨hK.1, fun n ↦ h _ (hK.2 n)⟩

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

-- Identify the ambient localizing hulls before transferring the adjunction.
private lemma closure_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (hbc : constantModelBoundedConstructible Λ X = boundedConstructible
      (condensedRingObj Λ X))
    (hctf : (constantModelBoundedConstructible Λ X ⊓
      DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible Λ X) :
    localizingClosureProEtale Λ X = boundedConstructibleLocalizingClosure Λ X := by
  rw [localizingClosureProEtale, hctf, hbc]
  rw [Functor.closure_index_eq.{u + 1, u + 1, u + 2}]
  apply le_antisymm
  · intro K hK
    apply hK (boundedConstructibleLocalizingClosure Λ X)
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro I F hF h
      let := hF
      exact ObjectProperty.prop_colimit _ F (fun i ↦ h i.as)
    · exact boundedConstructible_le_localizingClosure Λ X
  · have (I : Type (u + 1)) :
        (localizingClosureOfSize.{u + 1}
          (boundedConstructible (condensedRingObj Λ X))).IsClosedUnderColimitsOfShape
            (Discrete I) :=
      Functor.closedUnderCoproducts _ (Functor.closure_isLocalizing.{u + 1} _) I
    have := (Functor.closure_isLocalizing.{u + 1} (boundedConstructible (condensedRingObj Λ X))).1
    have := (Functor.closure_isLocalizing.{u + 1} (boundedConstructible (condensedRingObj Λ X))).2.1
    apply boundedConstructibleLocalizingClosure_le
    · intro K hK P hP hSP
      exact hSP K hK

private noncomputable def propertyEquiv {C : Type*} [Category C]
    {P Q : ObjectProperty C} (h : P = Q) : P.FullSubcategory ≌ Q.FullSubcategory where
  functor := ObjectProperty.ιOfLE h.le
  inverse := ObjectProperty.ιOfLE h.ge
  unitIso := Iso.refl _
  counitIso := Iso.refl _

private noncomputable def properIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    rightDerivedLowerShriekOfCompactification Λ (Compactification.ofIsProper f) ≅
      (lowerStar Λ f).rightDerivedFunctor := by
  let e := ((openImmersionLowerShriekUpperStarAdjunction Λ (𝟙 X)).ofNatIsoRight
    (upperStarId Λ X)).leftAdjointUniq Adjunction.id
  let e' := Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _
  exact Functor.isoWhiskerRight e' _ ≪≫ Functor.leftUnitor _

private lemma bounded_of_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left] (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (eZ : localizingClosureProEtale Λ Z.left = boundedConstructibleLocalizingClosure Λ Z.left)
    (eY : localizingClosureProEtale Λ Y.left = boundedConstructibleLocalizingClosure Λ Y.left)
    (hbcY : boundedConstructible (condensedRingObj Λ Y.left) ≤
      constantModelBoundedConstructible Λ Y.left)
    (hres : ∀ (h : ∀ K, localizingClosureProEtale Λ Z.left K →
        localizingClosureProEtale Λ Y.left
          ((rightDerivedLowerShriekOfCompactification Λ
            (Compactification.ofIsProper g.left)).obj K))
      (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
        (localizingClosureProEtale Λ Z.left).FullSubcategory)
      (_adj : localizingLowerShriek Λ (Compactification.ofIsProper g.left) h ⊣ G)
      (K : (localizingClosureProEtale Λ Y.left).FullSubcategory),
      constantModelBoundedConstructible Λ Y.left K.obj →
        DerivedCategory.TStructure.t.bounded (G.obj K).obj)
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (_adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    DerivedCategory.TStructure.t.bounded
      (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj := by
  let EZ := propertyEquiv eZ
  let EY := propertyEquiv eY
  let G' := EY.functor ⋙ G ⋙ EZ.inverse
  have h : ∀ A, localizingClosureProEtale Λ Z.left A →
      localizingClosureProEtale Λ Y.left
        ((rightDerivedLowerShriekOfCompactification Λ
          (Compactification.ofIsProper g.left)).obj A) := by
    intro A hA
    apply (congrFun eY _).mpr
    exact (boundedConstructibleLocalizingClosure Λ Y.left).prop_of_iso
      ((properIso Λ g.left).symm.app A)
      (ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ A ((congrFun eZ A).mp hA))
  let F' := localizingLowerShriek Λ (Compactification.ofIsProper g.left) h
  let eF : F' ≅ EZ.functor ⋙ ellAdicLocalizingLowerStar Λ ℓ g hΛ ⋙ EY.inverse :=
    NatIso.ofComponents
      (fun A ↦ ObjectProperty.isoMk _ ((properIso Λ g.left).app A.obj)) (by
        intro A B f
        apply ObjectProperty.hom_ext
        exact (properIso Λ g.left).hom.naturality f.hom)
  let adj' : F' ⊣ G' :=
    ((EZ.toAdjunction.comp _adj).comp EY.symm.toAdjunction).ofNatIsoLeft eF.symm
  exact hres h G' adj' (EY.inverse.obj
    ((boundedConstructibleToLocalizing Λ Y.left).obj K)) (hbcY _ K.property)

-- Existing restriction theorems supply boundedness for the transferred right adjoint.
private lemma admissible_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (hctf : (constantModelBoundedConstructible Λ Y.left ⊓
      DerivedCategory.finiteTorAmplitude _) = constantModelBoundedConstructible Λ Y.left)
    (h : ∀ K, localizingClosureProEtale Λ Z.left K →
        localizingClosureProEtale Λ Y.left
          ((rightDerivedLowerShriekOfCompactification Λ
            (Compactification.ofIsProper g.left)).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z.left).FullSubcategory)
    (adj : localizingLowerShriek Λ (Compactification.ofIsProper g.left) h ⊣ G)
    (K : (localizingClosureProEtale Λ Y.left).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ Y.left K.obj) :
    DerivedCategory.TStructure.t.bounded (G.obj K).obj := by
  obtain ⟨_, _, _, _, _, _, _, hex⟩ := exceptionalInverseImage_exists Λ ℓ k g hΛ
  obtain ⟨_, _, _, _, _, hcomp, ⟨G', _, _, ⟨adj'⟩, hpres⟩, _⟩ := hex
  obtain ⟨ec⟩ := hcomp (Compactification.ofIsProper g.left)
  let eF : _ ≅ localizingLowerShriek Λ (Compactification.ofIsProper g.left) h :=
    NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk _ (ec.app A)) (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact ec.hom.naturality f)
  let eG : G' ≅ G := (adj'.ofNatIsoLeft eF).rightAdjointUniq adj
  exact DerivedCategory.TStructure.t.bounded.prop_of_iso
    ((localizingClosureProEtale Λ Z.left).ι.mapIso (eG.app K))
    (hpres K ((congrFun hctf K.obj).mpr hK)).1.1

private lemma coefficient_cases
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) :
    (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.val))) ∨
    (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.val))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
  cases hΛ with
  | continuous E =>
    obtain ⟨F, hF⟩ := continuous_normalize ℓ E
    exact Or.inl ⟨F, hF⟩
  | integral E =>
    obtain ⟨F, hF⟩ := integral_normalize ℓ E
    exact Or.inr (Or.inl ⟨F, hF⟩)
  | algebraicClosure => exact Or.inr (Or.inr ⟨Iso.refl _⟩)

private lemma ellAdic_constructible_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [IsNoetherian X] [QuasiSeparatedSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  apply bounded_constructible_comparison
  rcases coefficient_cases Λ ℓ hΛ with ⟨E, ⟨e⟩⟩ | ⟨E, ⟨e⟩⟩ | ⟨e⟩
  · exact coefficient_constructible_comparison e X
      (finite_constructible_constant_model ℓ E X)
  · exact coefficient_constructible_comparison e X
      (fun M hM ↦ (integral_constructible_iff_constant_model ℓ E X M).mp hM)
  · obtain ⟨e⟩ := e
    exact coefficient_constructible_comparison e X
      (qbar_constructible_constant_model ℓ X)

private lemma qbar_restriction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (g : Z ⟶ Y) [IsProper g.left]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (h : ∀ K, localizingClosureProEtale Λ Z.left K →
        localizingClosureProEtale Λ Y.left
          ((rightDerivedLowerShriekOfCompactification Λ
            (Compactification.ofIsProper g.left)).obj K))
    (G : (localizingClosureProEtale Λ Y.left).FullSubcategory ⥤
      (localizingClosureProEtale Λ Z.left).FullSubcategory)
    (adj : localizingLowerShriek Λ (Compactification.ofIsProper g.left) h ⊣ G)
    (K : (localizingClosureProEtale Λ Y.left).FullSubcategory)
    (hK : constantModelBoundedConstructible Λ Y.left K.obj) :
    DerivedCategory.TStructure.t.bounded (G.obj K).obj := by
  let : Z.left.Over (Spec (.of k)) := ⟨Z.hom⟩
  let : Y.left.Over (Spec (.of k)) := ⟨Y.hom⟩
  let : LocallyOfFiniteType (Z.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType Z.hom)
  let : QuasiCompact (Z.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Z.hom)
  let : IsSeparated (Z.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Z.hom)
  let : LocallyOfFiniteType (Y.left ↘ Spec (.of k)) := inferInstanceAs
    (LocallyOfFiniteType Y.hom)
  let : QuasiCompact (Y.left ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact Y.hom)
  let : IsSeparated (Y.left ↘ Spec (.of k)) := inferInstanceAs (IsSeparated Y.hom)
  let : g.left.IsOver (Spec (.of k)) := ⟨Over.w g⟩
  let c : Compactification.BoundaryCompactification g.left :=
    ⟨⟨Compactification.ofIsProper g.left, show QuasiCompact (𝟙 Z.left) from inferInstance⟩⟩
  obtain ⟨_, _, _, hG, _⟩ :=
    (rationalRestrictionGlue.{u, u} Λ ℓ ⊥ (Or.inr hΛ) k (ringChar k)
      (Fact.out : ringChar k ≠ ℓ) g.left c h G adj).2
  exact (hG K hK).1

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- The canonical Brown right adjoint has finite cohomological amplitude on bounded
constructible inputs.  This is the geometric restriction step of the blueprint proof.

Source: blueprint `det-existence-restriction.proof.md`, Part (2), rational and integral
restriction theorems and their coefficient comparison.
Proof: identify the canonical Brown right adjoint with the geometric exceptional inverse
image on finite affine charts, apply the rational and integral restriction theorems, and
take a common bound over the finite affine cover.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded-canonical)
-/
theorem ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    (hF : (ellAdicLocalizingLowerStar Λ ℓ g hΛ).IsLeftAdjoint)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        (((@Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF).obj
          ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  let : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  let : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let : IsNoetherian Z.left := ⟨⟩
  let : IsNoetherian Y.left := ⟨⟩
  have eZ := ellAdic_constructible_comparison Λ ℓ hΛ Z.left
  have eY := ellAdic_constructible_comparison Λ ℓ hΛ Y.left
  have hcoeff := coefficient_cases Λ ℓ hΛ
  have hc :
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.val)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.val))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
    rcases hcoeff with ⟨E, hE⟩ | ⟨E, hE⟩ | hQ
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inr hE⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨E, Or.inl hE⟩))
    · exact Or.inr (Or.inr (Or.inr hQ))
  have htZ := (localizingClosure_ctf_equals_bc ℓ Z.left Λ hc).1.2.2.1
  have htY := (localizingClosure_ctf_equals_bc ℓ Y.left Λ hc).1.2.2.1
  let G := @Functor.rightAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF
  let adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G :=
    @Adjunction.ofIsLeftAdjoint _ _ _ _ (ellAdicLocalizingLowerStar Λ ℓ g hΛ) hF
  have hb : DerivedCategory.TStructure.t.bounded
      (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj := by
    apply bounded_of_restriction Λ ℓ g hΛ
      (closure_eq Λ Z.left eZ htZ) (closure_eq Λ Y.left eY htY) eY.ge _ G adj K
    rcases hcoeff with ⟨E, hE⟩ | ⟨E, hE⟩ | hQ
    · exact admissible_restriction Λ ℓ g (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩)))) htY
    · exact admissible_restriction Λ ℓ g
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, hE⟩))))) htY
    · exact qbar_restriction Λ ℓ g hQ
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hb
  refine ⟨a, b, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (DerivedCategory.isGE_iff _ a).mp ha i hi
  · exact (DerivedCategory.isLE_iff _ b).mp hb i hi

/-- The supplied localizing right adjoint has finite cohomological amplitude on a bounded
constructible input.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: use the finite affine factorization of the proper map and the boundedness part of
the rational restriction theorem, or its compatible integral torsion-level analogue.  A
finite affine cover gives a common pair of cohomological bounds; uniqueness of right
adjoints transports these bounds from the geometric construction to the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-bounded)
-/
theorem ellAdic_localizing_rightAdjoint_obj_isBounded
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  let F := ellAdicLocalizingLowerStar Λ ℓ g hΛ
  let hF : F.IsLeftAdjoint := ellAdic_isLeftAdjoint_localizingLowerStar Λ ℓ g hΛ
  let H := @Functor.rightAdjoint _ _ _ _ F hF
  let adjH : F ⊣ H := @Adjunction.ofIsLeftAdjoint _ _ _ _ F hF
  obtain ⟨a, b, hb⟩ := ellAdic_localizing_canonical_rightAdjoint_obj_isBounded
    Λ ℓ g hΛ hF K
  let e := adjH.rightAdjointUniq adj
  refine ⟨a, b, fun i hi ↦ ?_⟩
  let e' := (boundedConstructibleLocalizingClosure Λ Z.left).ι.mapIso
    (e.app ((boundedConstructibleToLocalizing Λ Y.left).obj K))
  exact (hb i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e'.symm)

end AlgebraicGeometry.ProEtale.CondensedRing
