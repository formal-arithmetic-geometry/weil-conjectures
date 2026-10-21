/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q28
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Sheaf.Paper.IntegralLfpConstantModelComparison
import Sheaf.Paper.IntegralConstructibleSerre
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Mathlib.Algebra.Field.ULift

/-!
# Integral constant-model constructible heart closure

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), printed pp. 60--61
(blueprint: lem-sfb-integral-constant-model-heart-closure).

The theorem states closure under ambient kernels, cokernels, and short exact extensions
for finite constant scalar models over the pulled-back condensed ring of integers.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj
open CondensedRing
universe v₁ v₂ u₁ u₂

section Presentation
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  {R : C} {S : D} [MonObj R] [MonObj S]
  [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]
private lemma fp_map (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)
end Presentation
section
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (φ : Λ ⟶ Λ') [IsMonHom φ] [IsIso φ]
omit [IsCommMonObj Λ] [IsCommMonObj Λ'] in
private lemma fp_point {P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ'}
    (hP : Mod.IsFinitelyPresented Λ' P) :
    Mod.IsFinitelyPresented Λ ((Mod.comap φ).obj P) := by
  apply fp_map (Mod.comap φ) _ hP
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ') ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))
private noncomputable def pull_comap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Mod.comap (coefficientMap φ X) ⋙ CondensedRing.upperStar Λ f ≅
      CondensedRing.upperStar Λ' f ⋙ Mod.comap (coefficientMap φ Y) :=
  (CondensedRing.comapUpperStarIso φ f).symm
private lemma local_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩
private lemma local_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : HasFiniteConstantLocalModel Λ' X M) :
    HasFiniteConstantLocalModel Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  refine ⟨(Mod.comap φ).obj P, fp_point φ hP, ⟨?_⟩⟩
  exact (pull_comap φ (U.f i)).app M ≪≫
    (Mod.comap (coefficientMap φ (U.X i))).mapIso eP ≪≫
    ((upperStarFromPoint (U.X i)).mapModComapIso φ).symm.app P
private lemma stratified_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsFiniteConstantStratified Λ' X M) :
    IsFiniteConstantStratified Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact local_iso ((pull_comap φ (S.immersion a)).app M).symm
    (local_comap φ _ _ (hS a))
private lemma stratified_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ local_iso
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩
private lemma constructible_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [if_pos h] at hM ⊢
    exact stratified_iso e hM
  · simp only [if_neg h] at hM ⊢
    intro U hU
    exact stratified_iso ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)
private lemma constructible_comap (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))
    (hM : IsConstantModelConstructible Λ' X M) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  classical
  unfold IsConstantModelConstructible at hM ⊢
  by_cases h : CompactSpace X ∧ QuasiSeparatedSpace X
  · simp only [if_pos h] at hM ⊢
    exact stratified_comap φ X M hM
  · simp only [if_neg h] at hM ⊢
    intro U hU
    exact stratified_iso ((pull_comap φ U.ι).app M).symm
      (stratified_comap φ _ _ (hM U hU))

private theorem constantModel_comap_iff (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) ↔
      IsConstantModelConstructible Λ' X M := by
  constructor
  · intro h
    have hh := constructible_comap (inv φ) X _ h
    exact constructible_iso
      (((Mod.comapComp (coefficientMap (inv φ) X) (coefficientMap φ X)).symm ≪≫
        Mod.comapCongr (by rw [← coefficientMap_comp]; simp) ≪≫
          Mod.comapId _).app M) hh
  · exact constructible_comap φ X M
end

private theorem integralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    Nonempty (Mon.mk (integralCondensedRing ℓ (ULift.{u} E.val)) ≅
      Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.val)) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let : NormedAlgebra ℚ_[ℓ] E.val := by infer_instance
  let F := ULift.{u} E.val
  let : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  let : NormedAlgebra ℚ_[ℓ] F := ⟨fun a x ↦ by
    change ‖a • x.down‖ ≤ ‖a‖ * ‖x.down‖
    exact norm_smul_le a x.down⟩
  let : FiniteDimensional ℚ_[ℓ] F :=
    (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.val)).symm.finiteDimensional
  let A := latticeCoefficientIntegers ℓ F
  let e : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F) ≃+* E.val :=
    (WithAbs.equiv _).trans ULift.ringEquiv
  have he (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) : ‖e x‖ = ‖x‖ := by
    change ‖(WithAbs.equiv _ x).down‖ = spectralNorm ℚ_[ℓ] F (WithAbs.equiv _ x)
    exact NormedAlgebra.norm_eq_spectralNorm ℚ_[ℓ] (L := F) (WithAbs.equiv _ x)
  have hmem (x : WithAbs (Padic.coefficientExtensionAbsoluteValue ℓ F)) :
      x ∈ A ↔ e x ∈ PadicAlgCl.integers ℓ E.val := by
    have hm := (Padic.extension_integers_dvr ℓ F
      (Padic.coefficientExtensionAbsoluteValue ℓ F)
      (spectralNorm_extends (K := ℚ_[ℓ]) (L := F))).choose_spec.choose_spec.1
    change WithAbs.equiv _ x ∈ Padic.coefficientExtensionIntegers ℓ F ↔ _
    change ∀ y : F, y ∈ Padic.coefficientExtensionIntegers ℓ F ↔
      Padic.coefficientExtensionAbsoluteValue ℓ F y ≤ 1 at hm
    rw [hm, PadicAlgCl.mem_integers_iff]
    change ‖x‖ ≤ 1 ↔ ‖e x‖₊ ≤ 1
    rw [← he, ← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm]
  let ei : A ≃+* PadicAlgCl.integers ℓ E.val :=
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
      Profinite.padicIntegersCondensedRing.{u} ℓ E.val :=
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

/-- Integral scalar-constant constructible module sheaves form a weak Serre subcategory.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(1), printed pp. 60--61
(blueprint: lem-sfb-integral-constant-model-heart-closure).

Proof: identify the finite constant scalar-model convention with the completed adic model
over the valuation ring of the finite coefficient field.  The adic stratified-perfect
criterion gives closure under cones, so the cone of a map between degree-zero objects has
constructible cohomology equal to its kernel and cokernel.  The same criterion applied to
the degree-zero triangle associated to a short exact sequence gives extension closure.
The coefficient comparison preserves scalar matrices and restrictions to strata, and the
Noetherian hypothesis is exactly quasi-compactness together with local Noetherianity.
-/
theorem isConstantModelConstructible_serre_padicIntegers
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) :
    (∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) (f : M ⟶ N),
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X N →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X (kernel f) ∧
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X (cokernel f)) ∧
    (∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)),
      S.ShortExact →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₁ →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₃ →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X S.X₂) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let : NormedAlgebra ℚ_[ℓ] E.val := by infer_instance
  obtain ⟨e⟩ := integralCoefficientIso.{u} ℓ E
  let φ := e.hom.hom
  have : IsMonHom φ := inferInstanceAs (IsMonHom e.hom.hom)
  have : IsIso φ := inferInstanceAs (IsIso e.hom.hom)
  let ψ := coefficientMap φ X
  have cmp (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)) :
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M ↔
        IsConstructibleModuleObject
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X) M := by
    have hp := integralLfpConstantModelComparison ℓ (ULift.{u} E.val) X
      ((Mod.comap ψ).obj M)
    refine (constantModel_comap_iff φ X M).symm.trans (hp.symm.trans ?_)
    constructor
    · intro h
      exact _root_.constructible_of_iso
        (((Mod.comapComp (inv ψ) ψ).symm ≪≫ Mod.comapCongr (by simp) ≪≫
          Mod.comapId _).app M) (_root_.constructible_comap (inv ψ) h)
    · exact _root_.constructible_comap ψ
  obtain ⟨hk, hc, he⟩ := integralConstructible_serre ℓ E.val X
  change ObjectProperty.IsClosedUnderKernels
    (IsConstructibleModuleObject (condensedRingObj
      (Profinite.padicIntegersRingObj ℓ E.val) X)) at hk
  change ObjectProperty.IsClosedUnderCokernels
    (IsConstructibleModuleObject (condensedRingObj
      (Profinite.padicIntegersRingObj ℓ E.val) X)) at hc
  change ObjectProperty.IsClosedUnderExtensions
    (IsConstructibleModuleObject (condensedRingObj
      (Profinite.padicIntegersRingObj ℓ E.val) X)) at he
  let P : ObjectProperty _ := IsConstructibleModuleObject
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X)
  let : P.IsClosedUnderKernels := hk
  let : P.IsClosedUnderCokernels := hc
  let : P.IsClosedUnderExtensions := he
  constructor
  · intro M N f hM hN
    exact ⟨(cmp _).mpr (P.prop_kernel f ((cmp M).mp hM) ((cmp N).mp hN)),
      (cmp _).mpr (P.prop_cokernel f ((cmp M).mp hM) ((cmp N).mp hN))⟩
  · intro S hS h₁ h₃
    exact (cmp _).mpr (P.prop_X₂_of_shortExact hS ((cmp _).mp h₁) ((cmp _).mp h₃))

end AlgebraicGeometry.ProEtale
