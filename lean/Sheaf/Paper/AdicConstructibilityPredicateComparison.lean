/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NJ, K7
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.Paper.CartesianCoefficients
import Mathlib.Algebra.Field.ULift
import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
import all Sheaf.Paper.CondensedCoefficientIsoConstructible
import all Sheaf.Paper.IntegralLfpConstantModelComparison
import all Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.CondensedQbarLfpLocalTriviality

/-!
# Adic constructibility predicates on Noetherian schemes

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-existence,
`det-existence-restriction.proof.md`, integral and rational cases, and
sec-proetale-coefficients/sk-def-sfb-constructible, clauses 1--2 and final paragraph
(blueprint: lem-sfb-adic-constructibility-predicate-comparison).

The comparison uses the specified condensed multiplication and the existing internal
module predicates. Under the section-action equivalence these are the same module sheaves.
Both bounded predicates live in the ordinary derived category; no completion is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem comparison_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ')
    (X : Scheme.{u})
    (h : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) :
    IsConstructibleModuleObject (condensedRingObj Λ' X) M ↔
      IsConstantModelConstructible Λ' X M := by
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := (upperStarFromPoint X).map φ
  let N := (Mod.comap ψ).obj M
  have er : (Mod.comap (inv ψ)).obj N ≅ M :=
    ((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
      Mod.comapId _).app M
  constructor
  · intro hM
    have hN := (h N).mp (_root_.constructible_comap ψ hM)
    have hback := constructible_comap (inv φ) X N hN
    apply constructible_iso _ hback
    exact ((Mod.comapComp ((upperStarFromPoint X).map (inv φ)) ψ).symm ≪≫
      Mod.comapCongr (by
        dsimp only [ψ]
        rw [← Functor.map_comp]
        simp) ≪≫ Mod.comapId _).app M
  · intro hM
    exact _root_.constructible_of_iso er
      (_root_.constructible_comap (inv ψ) ((h N).mpr (constructible_comap φ X M hM)))

private theorem finiteFree_fp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] (n : ℕ) :
    Mod.IsFinitelyPresented Λ (Mod.finiteFree Λ n) := by
  exact ⟨n, n, 0, ⟨(CategoryTheory.Limits.cokernelZeroIsoTarget (X := Mod.finiteFree Λ n)
    (Y := Mod.finiteFree Λ n)).symm⟩⟩

private theorem model_of_free_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree (condensedRingObj Λ (C.X i))
        ((CondensedRing.upperStar Λ (C.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ X M := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hC i
  let F := (upperStarFromPoint (C.X i)).mapMod Λ
  refine ⟨Mod.finiteFree Λ n, finiteFree_fp Λ n, ⟨e ≪≫ ?_⟩⟩
  exact (F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
    CategoryTheory.Limits.biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp))).symm

private theorem integralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    Nonempty (Mon.mk (integralCondensedRing ℓ (ULift.{u} E)) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E := ⟨fun c x ↦ by
    change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
      ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]⟩
  let F := ULift.{u} E
  let : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
    change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
    exact norm_smul_le a x.down⟩
  let : FiniteDimensional ℚ_[ℓ] F :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
  let A := latticeCoefficientIntegers ℓ F
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F) ≃+* E :=
    (WithAbs.equiv _).trans ULift.ringEquiv
  have he (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) : ‖e x‖ = ‖x‖ := by
    change ‖(WithAbs.equiv _ x).down‖ = spectralNorm ℚ_[ℓ] F (WithAbs.equiv _ x)
    exact NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (L := F) (WithAbs.equiv _ x)
  have hmem (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) :
      x ∈ A ↔ e x ∈ PadicAlgCl.integers ℓ E := by
    have hm := (Padic.extension_integers_dvr ℓ F
      (Padic.coefficientExtensionAbsoluteValue ℓ F)
      (spectralNorm_extends (K := ℚ_[ℓ]) (L := F))).choose_spec.choose_spec.1
    change WithAbs.equiv _ x ∈ Padic.coefficientExtensionIntegers ℓ F ↔ _
    change ∀ y : F, y ∈ Padic.coefficientExtensionIntegers ℓ F ↔
      Padic.coefficientExtensionAbsoluteValue ℓ F y ≤ 1 at hm
    rw [hm, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖e x‖₊ ≤ 1
    rw [← he, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
  let ei : A ≃+* PadicAlgCl.integers ℓ E :=
    { toFun := fun x ↦ ⟨e x, (hmem x).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x,
        (hmem _).mpr (by simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x y)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x y) }
  have hei : Isometry ei := by
    apply AddMonoidHomClass.isometry_of_norm ei
    intro x
    exact he x
  have heis : Isometry ei.symm := by
    intro x y
    simpa only [ei.apply_symm_apply] using (hei (ei.symm x) (ei.symm y)).symm
  let eR : Profinite.continuousMapRingSheafOfUniverse.{u,u} A ≅
      Profinite.padicIntegersCondensedRing.{u} ℓ E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.toRingHom.compLeftContinuous S.unop hei.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((ei.symm.toRingHom.compLeftContinuous S.unop
              heis.continuous).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact ei.apply_symm_apply _ }
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

private theorem field_local_model
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hM : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) M) :
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj E) X M := by
  obtain ⟨C, hC⟩ := exists_finiteFree_cover_of_condensedField_lfp ℓ E X M hM
  apply model_of_free_cover
  refine ⟨C, fun i ↦ ?_⟩
  let φ := condensedPullbackHom (Profinite.continuousCoefficientRingObj E) (C.f i)
  exact free_of_iso (free_comap (inv φ) (hC i))
    ((Mod.extendScalarsIsoComapInv φ).app _).symm

private theorem fieldCoefficientIso (E : Type) [NormedField E] :
    Nonempty (Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} E)) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} E)) := by
  let e := (ULift.ringEquiv : ULift.{u} E ≃+* E)
  let eR : Profinite.continuousCoefficientRingSheaf.{u} (ULift.{u} E) ≅
      Profinite.continuousMapRingSheaf.{u} E :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop
              Homeomorph.ulift.continuous_toFun).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop
              Homeomorph.ulift.symm.continuous_toFun).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
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

/-- Stratified local finite presentation agrees with finite constant scalar local models
for the three certified adic coefficient rings, including integral torsion modules.
Consequently their bounded constructible object properties in the same ordinary derived
category agree. The two existentially quantified stratifications need not be identical.

Source: blueprint main-20261015, `det-existence-restriction.proof.md`, integral/rational
cases; `sk-def-sfb-constructible/_section.md`, clauses 1--2 and final paragraph
(blueprint: lem-sfb-adic-constructibility-predicate-comparison).

Proof:
1. The general comparison from local models is the proved helper
`comparison_of_local_models` in the integral comparison module. Noetherianity makes X
qcqs and every stratum Noetherian. Transport finite presentations along the canonical
coefficient isomorphisms; constant local models imply local finite presentation.
2. For integral coefficients identify the valuation-topology ring of integers on
`ULift E` with the embedded ring of integers. The absolute value is the spectral norm,
which agrees with the given extension norm. This gives an isometric ring isomorphism,
hence a condensed ring isomorphism. Apply `integralLfpConstantModelComparison` and
transport both predicates along that isomorphism. Integral torsion modules are retained.
3. For finite field coefficients use `ULift E` to match the scheme universe. Continuous
functions into `ULift E` and E are canonically isomorphic condensed rings. On every
Noetherian stratum `exists_finiteFree_cover_of_condensedField_lfp` gives a finite free
cover. Its rank-n module is the pullback of the rank-n free module on the point, finitely
presented as the cokernel of a zero map. These are finite constant local models.
4. For the specified algebraic-closure ring use `condensedQbar_lfp_locally_free` and the
same free scalar model. This keeps the finite-subextension-valued coefficient ring.
5. Substitute the module equivalence in every cohomological degree. The boundedness
condition is identical, so the two object properties agree in the ordinary derived
category.
-/
theorem adicConstructibilityPredicateComparison
    (ℓ : ℕ) [Fact ℓ.Prime]
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hΛ : CondensedRing.IsEllAdicCoefficient ℓ Λ inferInstance) :
    (∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M) ∧
    boundedConstructible (condensedRingObj Λ X) = constantModelBoundedConstructible Λ X := by
  have : IsNoetherian X := ⟨⟩
  have hmod : ∀ M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X),
      IsConstructibleModuleObject (condensedRingObj Λ X) M ↔
        IsConstantModelConstructible Λ X M := by
    cases _hΛ with
    | continuous E =>
      let F := ULift.{u} E
      let : NormedField F :=
        { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
          dist_eq x y := dist_eq_norm_neg_add x.down y.down
          norm_mul x y := norm_mul x.down y.down }
      let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
        change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
        exact norm_smul_le a x.down⟩
      let : FiniteDimensional ℚ_[ℓ] F :=
        (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E)).symm.finiteDimensional
      obtain ⟨e⟩ := fieldCoefficientIso.{u} E
      exact comparison_transport e X
        (comparison_of_local_models (Profinite.continuousCoefficientRingObj F)
          (field_local_model ℓ F) X)
    | integral E =>
      obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
      exact comparison_transport e X (integralLfpConstantModelComparison ℓ (ULift.{u} E) X)
    | algebraicClosure =>
      exact comparison_of_local_models (Profinite.padicAlgClRingObj ℓ)
        (fun Y _ N hN ↦ model_of_free_cover _ Y N
          (condensedQbar_lfp_locally_free ℓ Y N hN)) X
  refine ⟨hmod, ?_⟩
  funext K
  apply propext
  exact and_congr Iff.rfl (forall_congr' fun n ↦ hmod _)

end AlgebraicGeometry.ProEtale
