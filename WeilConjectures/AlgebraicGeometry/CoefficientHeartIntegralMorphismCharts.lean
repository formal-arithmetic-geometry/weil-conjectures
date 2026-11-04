/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Algebra.Field.ULift

/-! # Integral charts for the coefficient-heart argument -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Lift the coefficient field to the scheme universe without changing its degree. -/
private instance heartLiftFiniteDimensional (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    FiniteDimensional ℚ_[ℓ] (ULift.{u} E.1) :=
  (ULift.moduleEquiv (R := ℚ_[ℓ]) (M := E.1)).symm.finiteDimensional

/-- The lifted spectral absolute value is the one from the fixed algebraic closure. -/
private theorem heartLiftNorm (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (x : ULift.{u} E.1) :
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1) x =
      ‖algebraMap E.1 (PadicAlgCl ℓ) x.down‖ := by
  let f : ULift.{u} E.1 →+* PadicAlgCl ℓ :=
    (algebraMap E.1 (PadicAlgCl ℓ)).comp ULift.ringEquiv.toRingHom
  let av := (NormedField.toAbsoluteValue (PadicAlgCl ℓ)).comp f.injective
  have ha (y : ℚ_[ℓ]) : av (algebraMap ℚ_[ℓ] (ULift.{u} E.1) y) = ‖y‖ := by
    change ‖algebraMap E.1 (PadicAlgCl ℓ) (algebraMap ℚ_[ℓ] E.1 y)‖ = ‖y‖
    rw [← IsScalarTower.algebraMap_apply]
    exact PadicAlgCl.norm_extends ℓ y
  exact (spectralNorm_unique_field_norm_ext ha x).symm

/-- The field identification is an isometry for the specified spectral metric. -/
private theorem heartLiftFieldIsometry (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.1) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
    @Isometry (ULift.{u} E.1) E.1
      nf.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      (PadicAlgCl.normedFieldOfAlgebra ℓ E.1).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      ULift.down := by
  let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
  let : TopologicalSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  apply @Isometry.of_dist_eq _ _ nf.toMetricSpace.toPseudoMetricSpace
    (PadicAlgCl.normedFieldOfAlgebra ℓ E.1).toMetricSpace.toPseudoMetricSpace
  intro x y
  change dist (algebraMap E.1 (PadicAlgCl ℓ) x.down)
      (algebraMap E.1 (PadicAlgCl ℓ) y.down) =
    Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1) (-x + y)
  rw [heartLiftNorm ℓ E]
  change dist (x.down : PadicAlgCl ℓ) (y.down : PadicAlgCl ℓ) =
    ‖-(x.down : PadicAlgCl ℓ) + (y.down : PadicAlgCl ℓ)‖
  exact dist_eq_norm_neg_add _ _

/-- Integer membership is preserved by the specified field identification. -/
private theorem heartLiftIntegerMembership (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (x : ULift.{u} E.1) :
    x ∈ Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1) ↔
      x.down ∈ PadicAlgCl.integers ℓ E.1 := by
  rw [Padic.mem_coefficientExtensionIntegers, heartLiftNorm ℓ E, PadicAlgCl.mem_integers_iff,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

/-- Restrict ULift.down to the actual integer subrings; no coefficient data is chosen. -/
private def heartLiftIntegerEquiv (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1) ≃+*
      PadicAlgCl.integers ℓ E.1 :=
  RingEquiv.restrict (ULift.ringEquiv : ULift.{u} E.1 ≃+* E.1) _ _
    (heartLiftIntegerMembership ℓ E)

/-- A specified topological ring equivalence induces the pointwise condensed
coefficient isomorphism, retaining its actual function on sections. -/
private def heartContinuousCoefficientIso (A : Type u) (B : Type)
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} B) := by
  let eR : Profinite.continuousCoefficientRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheaf.{u} B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop
              he).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop
              hi).comp ULift.ringEquiv.toRingHom))
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
  refine { hom := Mon.ofHom eAb.hom
           inv := Mon.ofHom eAb.inv
           hom_inv_id := ?_
           inv_hom_id := ?_ }
  · apply Mon.Hom.ext
    exact eAb.hom_inv_id
  · apply Mon.Hom.ext
    exact eAb.inv_hom_id

/-- The integer coefficient comparison for the actual embedded extension.
Both maps are induced by the integer-ring restriction of ULift.down and its inverse. -/
private def heartIntegralCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.1) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Mon.mk (Profinite.continuousCoefficientRingObj
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1))) ≅
        Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1) := by
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  letI : PseudoEMetricSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace E.1 :=
    (PadicAlgCl.normedFieldOfAlgebra ℓ E.1).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  let e := heartLiftIntegerEquiv.{u} ℓ E
  have hfield := heartLiftFieldIsometry.{u} ℓ E
  have hfieldinv : Isometry (ULift.up : E.1 → ULift.{u} E.1) :=
    hfield.right_inv (fun _ ↦ rfl)
  have he : Continuous e := by
    change Continuous (fun x : Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1) =>
      (⟨x.1.down, (heartLiftIntegerMembership ℓ E x.1).1 x.2⟩ : PadicAlgCl.integers ℓ E.1))
    apply Continuous.subtype_mk
    exact hfield.continuous.comp continuous_subtype_val
  have hi : Continuous e.symm := by
    change Continuous (fun x : PadicAlgCl.integers ℓ E.1 =>
      (⟨ULift.up x.1, (heartLiftIntegerMembership ℓ E (ULift.up x.1)).2 x.2⟩ :
        Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1)))
    apply Continuous.subtype_mk
    exact hfieldinv.continuous.comp continuous_subtype_val
  exact heartContinuousCoefficientIso _ _ e he hi

/-- The rational coefficient comparison for the same fixed embedding. -/
private def heartRationalCoefficientIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.1) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Mon.mk (Profinite.continuousCoefficientRingObj (ULift.{u} E.1)) ≅
      Mon.mk (Profinite.continuousMapRingObj.{u} E.1) := by
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI := PadicAlgCl.normedFieldOfAlgebra ℓ E.1
  letI : PseudoEMetricSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  letI : PseudoEMetricSpace E.1 :=
    (PadicAlgCl.normedFieldOfAlgebra ℓ E.1).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
  let e : ULift.{u} E.1 ≃+* E.1 := ULift.ringEquiv
  have he := heartLiftFieldIsometry.{u} ℓ E
  have hi : Isometry (ULift.up : E.1 → ULift.{u} E.1) :=
    he.right_inv (fun _ ↦ rfl)
  exact heartContinuousCoefficientIso _ _ e he.continuous hi.continuous

/-- The continuous inclusion in the lifted coefficient presentation. -/
private def heartLiftIntegralScalar (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.1) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Profinite.continuousCoefficientRingObj
        (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1)) ⟶
      Profinite.continuousCoefficientRingObj (ULift.{u} E.1) := by
  letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
  letI : TopologicalSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let f := (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1)).subtype
  let fr : Profinite.continuousCoefficientRingSheaf
      (Padic.coefficientExtensionIntegers ℓ (ULift.{u} E.1)) ⟶
      Profinite.continuousCoefficientRingSheaf (ULift.{u} E.1) :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((f.compLeftContinuous S.unop continuous_subtype_val).comp
            ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩
  exact (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map fr

/-- The two explicit coefficient identifications commute with the scalar inclusion.
This is equality of the specified maps, checked on every continuous section. -/
private theorem heartCoefficientSquare (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    letI nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
    letI : TopologicalSpace (ULift.{u} E.1) :=
      nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    heartLiftIntegralScalar.{u} ℓ E ≫ (heartRationalCoefficientIso.{u} ℓ E).hom.hom =
      (heartIntegralCoefficientIso.{u} ℓ E).hom.hom ≫
        padicIntegersRingObjToContinuousMapRingObj ℓ E := by
  let nf := (Padic.coefficientExtensionAbsoluteValue ℓ (ULift.{u} E.1)).toNormedField
  let : TopologicalSpace (ULift.{u} E.1) :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  ext S : 3
  apply ConcreteCategory.hom_ext
  intro f
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  rfl

/-- Absorb a cleared common denominator into the source rationalization
isomorphism. The integral map then represents the original rational map exactly. -/
private theorem heartAbsorbDenominator
    {C D : Type*} [Category C] [Category D] [Preadditive D]
    (T : C ⥤ D) {P Q : C} {M N : D} (g : P ⟶ Q) (f : M ⟶ N)
    (eP : T.obj P ≅ M) (eQ : T.obj Q ≅ N) (n : ℕ) [IsIso (n • 𝟙 M)]
    (hs : T.map g ≫ eQ.hom = n • (eP.hom ≫ f)) :
    ∃ eP' : T.obj P ≅ M, T.map g ≫ eQ.hom = eP'.hom ≫ f := by
  refine ⟨eP ≪≫ asIso (n • 𝟙 M), ?_⟩
  simpa only [Iso.trans_hom, asIso_hom, Category.assoc, Preadditive.nsmul_comp,
    Category.id_comp, Preadditive.comp_nsmul] using hs

/-- A rational lisse morphism has compatible integral models on connected affine
etale neighbourhoods. The source lattice may be rescaled to absorb its denominator.

Source: latest blueprint,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`, proof (1),
"First let Lambda = E", through the construction of h = pi^m f.
(blueprint: lem-sfb-coefficient-heart-integral-morphism-charts).

Proof in words: take lattice atlases for the source and target and their common
etale refinement. Refine further by connected affine opens, which are Noetherian.
Transport the lattices from sectionwise modules to modules over the pulled-back
condensed integer ring using the canonical internal/sectionwise equivalence.
The rational target is the filtered localization of its integral lattice. The
qcqs finitely presented Hom/filtered-colimit formula factors the restriction of
f through one localization stage. Write ell as a unit times a power of the
uniformizer. Rescale the source lattice by the resulting uniformizer power;
its rationalization is still the source, and the factorization gives the stated
commuting square. Rank zero and the empty scheme are allowed. -/
theorem coefficientHeart_integralMorphismCharts (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Scheme.{u}) [IsNoetherian X]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) X)) (f : M ⟶ N)
    (hM : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) M)
    (hN : IsLisseCoefficientModule (Profinite.continuousMapRingObj E.1) N) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      IsAffine (C.X i) ∧ IsLocallyNoetherian (C.X i) ∧ ConnectedSpace (C.X i) ∧
      ∃ (P Q : Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) (C.X i))) (g : P ⟶ Q),
        IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) P ∧
        IsLisseCoefficientModule (Profinite.padicIntegersRingObj ℓ E.1) Q ∧
        let T := Mod.extendScalars
          (padicIntegersToPadicSubfield (C.X i) ℓ E)
        ∃ (eP : T.obj P ≅ (CondensedRing.upperStar
            (Profinite.continuousMapRingObj E.1) (C.f i)).obj M)
          (eQ : T.obj Q ≅ (CondensedRing.upperStar
            (Profinite.continuousMapRingObj E.1) (C.f i)).obj N),
          T.map g ≫ eQ.hom = eP.hom ≫
            (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) (C.f i)).map f := by
  sorry

end AlgebraicGeometry.ProEtale
