/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups A2, D2
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward

import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
import all Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import all Sheaf.Paper.IntegralConstantModelHeartClosure
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.LocalizingClosureCtfEqualsBc
import Sheaf.Paper.ProperExceptionalRestriction
import Mathlib.Algebra.Field.ULift

/-! # Constructibility of the cohomology of the localizing exceptional object
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem continuousCoefficientIso {R S : Type}
    [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (e : R ≃+* S) (he : Continuous e) (hei : Continuous e.symm) :
    Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} R) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} S)) := by
  let eR : Profinite.continuousMapRingSheaf.{u} R ≅
      Profinite.continuousMapRingSheaf S :=
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
  refine ⟨{ hom := Mon.ofHom eAb.hom
            inv := Mon.ofHom eAb.inv
            hom_inv_id := ?_
            inv_hom_id := ?_ }⟩
  · apply Mon.Hom.ext
    exact eAb.hom_inv_id
  · apply Mon.Hom.ext
    exact eAb.inv_hom_id

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem continuousCoefficient_normalize (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} E) ≅
        Mon.mk (Profinite.continuousMapRingObj.{u} F.val)) := by
  let f : E →ₐ[ℚ_[ℓ]] PadicAlgCl ℓ := IsAlgClosed.lift
  let e := f.equivFieldRange
  let : FiniteDimensional ℚ_[ℓ] f.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨⟨f.fieldRange, inferInstance⟩, ?_⟩
  exact continuousCoefficientIso e.toRingEquiv
    e.toLinearMap.continuous_of_finiteDimensional
    e.symm.toLinearMap.continuous_of_finiteDimensional

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem integralCoefficient_normalize (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ F.val)) := by
  let f := IsScalarTower.toAlgHom ℚ_[ℓ] E (PadicAlgCl ℓ)
  let e := f.equivFieldRange
  let : FiniteDimensional ℚ_[ℓ] f.fieldRange := e.toLinearEquiv.finiteDimensional
  let F : PadicAlgCl.FiniteIntermediateField ℓ := ⟨f.fieldRange, inferInstance⟩
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have hmem (x : E) : x ∈ PadicAlgCl.integers ℓ E ↔
      e x ∈ PadicAlgCl.integers ℓ F.val := Iff.rfl
  let ei : PadicAlgCl.integers ℓ E ≃+* PadicAlgCl.integers ℓ F.val :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hmem _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hi : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    rfl
  have his : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hi (ei.symm x) (ei.symm y)).symm
  exact ⟨F, continuousCoefficientIso ei hi.continuous his.continuous⟩

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem moduleComparison_of_iso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ' ≅ Mon.mk Λ) (X : Scheme.{u})
    (hc : ∀ M, IsConstantModelConstructible Λ' X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ' X) M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  let φ := e.hom.hom
  let ψ := coefficientMap φ X
  refine (constantModel_comap_iff φ X M).symm.trans ((hc _).trans ?_)
  constructor
  · intro h
    exact _root_.constructible_of_iso
      (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
        Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)
  · exact _root_.constructible_comap ψ

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem moduleComparison_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree
          ((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} (U.f i)).mapMod
            (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    let φ := condensedPullbackHom Λ (S.immersion a)
    have h := (hS a).isLocallyFinitelyPresented _
    exact lfp_of_comap (inv φ)
      (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
  · rintro ⟨S, hS⟩
    refine ⟨S, fun a ↦ ?_⟩
    have : TopologicalSpace.NoetherianSpace (S.domain a) :=
      (S.immersion a).isEmbedding.isInducing.noetherianSpace
    let φ := condensedPullbackHom Λ (S.immersion a)
    have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
      ((Mod.extendScalarsIsoComapInv φ).app _).symm
    obtain ⟨U, hU⟩ := hLF _ _ h
    apply free_hasConstantModel Λ _
    refine ⟨U, fun i ↦ ?_⟩
    let ψ := condensedPullbackHom Λ (U.f i)
    exact free_of_iso (free_comap (inv ψ) (hU i))
      ((Mod.extendScalarsIsoComapInv ψ).app _).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem moduleComparison_integral (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) :
    IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M ↔
      IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) M := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let : NormedAlgebra ℚ_[ℓ] E.val := inferInstance
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
  apply moduleComparison_of_iso e X
  intro N
  exact (integralLfpConstantModelComparison ℓ (ULift.{u} E.val) X N).symm

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem coefficient_models (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance)
    (X : Scheme.{u}) [IsNoetherian X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    IsConstantModelConstructible Λ X M ↔
      IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  cases hΛ with
  | continuous E =>
    obtain ⟨F, ⟨e⟩⟩ := continuousCoefficient_normalize.{u} ℓ E
    exact moduleComparison_of_iso e.symm X
      (moduleComparison_of_localFree _ (finite_lf ℓ F) X) M
  | integral E =>
    obtain ⟨F, ⟨e⟩⟩ := integralCoefficient_normalize.{u} ℓ E
    exact moduleComparison_of_iso e.symm X (moduleComparison_integral ℓ F X) M
  | algebraicClosure =>
    exact moduleComparison_of_localFree _ (algcl_lf ℓ) X M

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem coefficient_normalForm (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    (hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance) :
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.val)) ∨
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.val))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)) := by
  cases hΛ with
  | continuous E =>
    obtain ⟨F, e⟩ := continuousCoefficient_normalize.{u} ℓ E
    exact Or.inr (Or.inr (Or.inl ⟨F, Or.inr e⟩))
  | integral E =>
    obtain ⟨F, e⟩ := integralCoefficient_normalize.{u} ℓ E
    exact Or.inr (Or.inr (Or.inl ⟨F, Or.inl e⟩))
  | algebraicClosure => exact Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩))

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem boundedHull_eq_sizedClosure
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) :
    CondensedRing.boundedConstructibleLocalizingClosure Λ X =
      localizingClosureOfSize.{u + 1} (boundedConstructible (condensedRingObj Λ X)) := by
  let B := boundedConstructible (condensedRingObj Λ X)
  let L := localizingClosureOfSize.{u + 1} B
  have hL := Functor.closure_isLocalizing.{u + 1} B
  let := hL.1
  let := hL.2.1
  let (I : Type (u + 1)) := Functor.closedUnderCoproducts L hL I
  apply le_antisymm
  · apply CondensedRing.boundedConstructibleLocalizingClosure_le
    intro K hK P hP hBP
    exact hBP K hK
  · intro K hK
    apply hK (CondensedRing.boundedConstructibleLocalizingClosure Λ X)
      ⟨inferInstance, inferInstance, ?_⟩
      (CondensedRing.boundedConstructible_le_localizingClosure Λ X)
    intro I A hA h
    let := hA
    exact ObjectProperty.prop_colimit _ A (fun i ↦ h i.as)

open MonoidalCategory MonObj Opposite Functor.LaxMonoidal Functor.OplaxMonoidal in
private theorem rightAdjoint_preserves_of_eq
    {C D : Type*} [Category* C] [Category* D]
    (P P' : ObjectProperty C) (Q Q' : ObjectProperty D)
    (eP : P = P') (eQ : Q = Q') (F : C ⥤ D)
    (h : ∀ A, P A → Q (F.obj A)) (h' : ∀ A, P' A → Q' (F.obj A))
    (G : Q.FullSubcategory ⥤ P.FullSubcategory)
    (J : Q'.FullSubcategory ⥤ P'.FullSubcategory)
    (adj : Q.lift (P.ι ⋙ F) (fun A ↦ h A.obj A.property) ⊣ G)
    (adj' : Q'.lift (P'.ι ⋙ F) (fun A ↦ h' A.obj A.property) ⊣ J)
    (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms]
    (T : ObjectProperty D)
    (hJ : ∀ A, T A.obj → R (J.obj A).obj)
    (A : Q.FullSubcategory) (hA : T A.obj) : R (G.obj A).obj := by
  cases eP
  cases eQ
  exact R.prop_of_iso (P.ι.mapIso ((adj'.rightAdjointUniq adj).app A)) (hJ A hA)

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

/-- Every cohomology object of the supplied localizing right adjoint on a bounded
constructible input is constructible.

Source: blueprint `sk-thm-existence` (4), `det-existence-restriction.proof.md`, Part (2).
Proof: compare local finite-presentation charts with the field, algebraic-closure, and
integral adic models using the cited local triviality and resolution theorems.  The smooth
and closed local restriction calculations preserve constructibility; finite affine descent
and uniqueness of right adjoints identify the result with the supplied `G`.
(blueprint: lem-sfb-adic-localizing-exceptional-cohomology)
-/
theorem ellAdic_localizing_rightAdjoint_obj_homology_constructible
    (G : (boundedConstructibleLocalizingClosure Λ Y.left).FullSubcategory ⥤
      (boundedConstructibleLocalizingClosure Λ Z.left).FullSubcategory)
    (adj : ellAdicLocalizingLowerStar Λ ℓ g hΛ ⊣ G)
    (K : (boundedConstructible (condensedRingObj Λ Y.left)).FullSubcategory) :
    ∀ n : ℤ, IsConstructibleModuleObject (condensedRingObj Λ Z.left)
      ((DerivedCategory.homologyFunctor _ n).obj
        ((G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj)) := by
  classical
  have : CompactSpace Z.left := QuasiCompact.compactSpace_of_compactSpace Z.hom
  have : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  have : QuasiSeparatedSpace Z.left := quasiSeparatedSpace_of_quasiSeparated Z.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have : IsNoetherian Z.left := ⟨⟩
  have : IsNoetherian Y.left := ⟨⟩
  have hcoeff := coefficient_normalForm ℓ Λ hΛ
  have hadm : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases hcoeff with h | h | ⟨E, h | h⟩ | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hbc (X : Scheme.{u}) [IsNoetherian X] [QuasiSeparatedSpace X] :
      constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
    funext A
    apply propext
    exact and_congr Iff.rfl (forall_congr' (fun n ↦ coefficient_models ℓ Λ hΛ X _))
  have hctf (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :=
    (localizingClosure_ctf_equals_bc ℓ X Λ hcoeff).1.2.2.1
  have hhull (X : Scheme.{u}) [IsNoetherian X] [QuasiSeparatedSpace X] :
      boundedConstructibleLocalizingClosure Λ X = localizingClosureProEtale Λ X := by
    rw [boundedHull_eq_sizedClosure, localizingClosureProEtale, hctf X, hbc X]
    exact (Functor.closure_index_eq.{u + 1, u + 1, u + 2}
      (boundedConstructible (condensedRingObj Λ X))).symm
  obtain ⟨_, _, _, _, h, _, _, hex⟩ := exceptionalInverseImage_exists Λ ℓ k g hadm
  obtain ⟨_, _, _, _, _, _, ⟨J, _, _, ⟨adjJ⟩, hJ⟩, _⟩ := hex
  obtain ⟨hStar, ⟨alpha⟩, _⟩ := proper_exceptional_restriction Λ ℓ k g hadm h J adjJ
  have adjStar := adjJ.ofNatIsoLeft alpha
  let : (boundedConstructible (condensedRingObj Λ Z.left)).IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e h.1,
      fun n ↦ _root_.constructible_of_iso
        ((DerivedCategory.homologyFunctor _ n).mapIso e) (h.2 n)⟩⟩
  have hpres : boundedConstructible (condensedRingObj Λ Z.left)
      (G.obj ((boundedConstructibleToLocalizing Λ Y.left).obj K)).obj := by
    apply rightAdjoint_preserves_of_eq
      (boundedConstructibleLocalizingClosure Λ Z.left) (localizingClosureProEtale Λ Z.left)
      (boundedConstructibleLocalizingClosure Λ Y.left) (localizingClosureProEtale Λ Y.left)
      (hhull Z.left) (hhull Y.left) (R((g.left)_*⟦Λ⟧))
      (ellAdic_localizing_rightDerivedLowerStar_obj Λ ℓ g hΛ) hStar G J adj adjStar
      (boundedConstructible (condensedRingObj Λ Z.left))
      (constantModelBoundedConstructible Λ Y.left)
    · intro A hA
      have hA' := (congrFun (hctf Y.left) A.obj).mpr hA
      exact (congrFun (hbc Z.left) _).mp (hJ A hA').1
    · exact (congrFun (hbc Y.left) K.obj).mpr K.property
  exact hpres.2

end AlgebraicGeometry.ProEtale.CondensedRing
