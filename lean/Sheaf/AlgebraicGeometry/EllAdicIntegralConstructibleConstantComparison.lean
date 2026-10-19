/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Noetherian
import all Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import Sheaf.Paper.IntegralLfpConstantModelComparison
import all Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Integral adic constant-model comparison

Source: det-existence-restriction.proof.md, coefficient comparison.
(blueprint: lem-sfb-adic-integral-constructible-constant-comparison)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
  [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
  [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]

private theorem embedded_norm_spectral (x : E) :
    ‖algebraMap E (PadicAlgCl l) x‖ = Padic.coefficientExtensionAbsoluteValue l E x := by
  let := PadicAlgCl.normedFieldOfAlgebra l E
  let : NormedAlgebra ℚ_[l] E := ⟨fun a x ↦ by
    change ‖algebraMap E (PadicAlgCl l) (a • x)‖ ≤ _
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
      PadicAlgCl.norm_extends]
    exact le_rfl⟩
  exact NormedAlgebra.norm_eq_spectralNorm ℚ_[l] x

private noncomputable def embeddedIntegerEquiv :
    latticeCoefficientIntegers l (ULift.{u} E) ≃+* PadicAlgCl.integers l E :=
  (coefficientWithAbsLiftRingEquiv l E).restrict _ _ (by
    intro x
    change x.ofAbs ∈ Padic.coefficientExtensionIntegers l (ULift.{u} E) ↔ _
    rw [coefficientIntegers_mem, coefficientLiftAbsoluteValue, PadicAlgCl.mem_integers_iff]
    rw [← NNReal.coe_le_coe]
    change _ ↔ ‖algebraMap E (PadicAlgCl l) x.ofAbs.down‖ ≤ (1 : ℝ)
    rw [embedded_norm_spectral])

private theorem embeddedIntegerEquiv_isometry :
    let := PadicAlgCl.normedFieldOfAlgebra l E
    Isometry (embeddedIntegerEquiv.{u} l E) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact (embedded_norm_spectral l E x.val.ofAbs.down).trans
    (coefficientLiftAbsoluteValue l E x.val.ofAbs).symm

private noncomputable def embeddedIntegerCondensedIso :
    Profinite.continuousMapRingSheafOfUniverse
        (latticeCoefficientIntegers l (ULift.{u} E)) ≅
      Profinite.padicIntegersCondensedRing.{u} l E := by
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  let e : latticeCoefficientIntegers l (ULift.{u} E) ≃ᵢ PadicAlgCl.integers l E :=
    { (embeddedIntegerEquiv l E).toEquiv with
      isometry_toFun := embeddedIntegerEquiv_isometry l E }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (embeddedIntegerEquiv l E)
      e.continuous e.symm.continuous V.unop).trans ULift.ringEquiv.symm)).toRingCatIso) ?_
  intro V V' f
  rfl

section Transport
variable {Λ Γ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Γ] [IsCommMonObj Γ]
  (φ : Λ ⟶ Γ) [IsMonHom φ] [IsIso φ]

omit [IsCommMonObj Λ] [IsCommMonObj Γ] in
private lemma point_presentation_comap {P : Mod _ Γ}
    (h : Mod.IsFinitelyPresented Γ P) : Mod.IsFinitelyPresented Λ ((Mod.comap φ).obj P) := by
  apply finitePresentation_map (Mod.comap φ) _ h
  intro n
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular Γ) ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

private lemma constant_localModel_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  exact ⟨P, hP, ⟨(upperStar Λ (C.f i)).mapIso e.symm ≪≫ eP⟩⟩

private lemma constant_localModel_comap {X : Scheme.{u}}
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X)}
    (h : HasFiniteConstantLocalModel Γ X M) :
    HasFiniteConstantLocalModel Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hC i
  refine ⟨(Mod.comap φ).obj P, point_presentation_comap φ hP, ⟨?_⟩⟩
  exact (comapUpperStarIso φ (C.f i)).symm.app M ≪≫
    (Mod.comap (coefficientMap φ (C.X i))).mapIso eP ≪≫
    ((upperStarFromPoint (C.X i)).mapModComapIso φ).symm.app P

private lemma constant_constructible_comap {X : Scheme.{u}} [IsNoetherian X]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Γ X)}
    (h : IsConstantModelConstructible Γ X M) :
    IsConstantModelConstructible Λ X ((Mod.comap (coefficientMap φ X)).obj M) := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at h ⊢
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun a ↦ ?_⟩
  exact constant_localModel_iso ((comapUpperStarIso φ (S.immersion a)).app M)
    (constant_localModel_comap φ (hS a))

private lemma constant_constructible_iso {X : Scheme.{u}} [IsNoetherian X]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (h : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at h ⊢
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun a ↦ constant_localModel_iso
    ((upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

end Transport

/-- General integral adic constructibility implies finite constant scalar local models.
Source: blueprint det-existence-restriction.proof.md, integral coefficient comparison;
Hemo--Richarz--Scholbach, Example 3.1 and Theorems 4.13, 6.2 and 6.12.
Proof: equip E with the norm induced by its given embedding in the fixed algebraic
closure. Uniqueness of the extended p-adic absolute value identifies this norm with
Padic.coefficientExtensionAbsoluteValue. Its closed unit ball is therefore the
spectral valuation ring used by integralLfpConstantModelComparison. The resulting
continuous ring isomorphism induces an isomorphism of condensed rings, including
multiplication, and hence equivalences of coefficient-module categories on the
point and on every scheme. These equivalences preserve regular modules, finite
biproducts, cokernels and inverse image. They consequently preserve local finite
presentations and finite constant scalar models, with the same covers and strata.
Apply integralLfpConstantModelComparison on the noetherian scheme and transport
its forward implication back through these equivalences. Empty strata, rank zero,
zero presentations and torsion are included; no completeness condition is added.
(blueprint: lem-sfb-adic-integral-constructible-constant-comparison) -/
theorem ellAdic_integral_constructible_constantModel
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) :
    IsConstructibleModuleObject (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X) M →
      IsConstantModelConstructible (Profinite.padicIntegersRingObj ℓ E) X M := by
  intro hM
  let e : integralCondensedRing ℓ (ULift.{u} E) ≅ Profinite.padicIntegersRingObj ℓ E :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (embeddedIntegerCondensedIso ℓ E)
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map _
    (embeddedIntegerCondensedIso ℓ E).hom
  have : IsMonHom e.inv := Sheaf.isMonHom_sheafCompose_map _
    (embeddedIntegerCondensedIso ℓ E).inv
  let N := (Mod.comap (coefficientMap e.hom X)).obj M
  have hN : IsConstructibleModuleObject
      (condensedRingObj (integralCondensedRing ℓ (ULift.{u} E)) X) N :=
    constructible_comap (coefficientMap e.hom X) hM
  have hm := (integralLfpConstantModelComparison ℓ (ULift.{u} E) X N).mp hN
  have hh := constant_constructible_comap e.inv hm
  apply constant_constructible_iso _ hh
  exact ((Mod.comapComp (coefficientMap e.inv X) (coefficientMap e.hom X)).symm ≪≫
    Mod.comapCongr (by
      change (upperStarFromPoint X).map e.inv ≫ (upperStarFromPoint X).map e.hom = _
      rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]) ≪≫ Mod.comapId _).app M


end AlgebraicGeometry.ProEtale.CondensedRing
