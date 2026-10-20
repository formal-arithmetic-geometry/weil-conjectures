/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.Paper.CompletedIntegralCoefficients
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import Sheaf.Paper.IntegralOperationsWellDefined
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import all Sheaf.Paper.IntegralReductionTowerUnrestricted

/-! # Well-defined completed integral scalar extension

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 3.4.10,
Proposition 3.5.1(3), and Proposition 6.8.14(1); Stacks Tags 06YS, 06YT, 08TC, 04VG
(blueprint: lem-weil-integral-scalar-extension-well-defined).

The zero-based level n means exponent n+1. Coefficients, tensor generators,
transitions, and the diagonal Roos maps are fixed before localization. Scalar
multiplication is expressed intrinsically by the canonical constant-section
endomorphism, descended through Q; no auxiliary linear structure is chosen.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false

universe t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace SheafOfModules.IntegralScalarProof

universe a b r

-- A linear map over the finite target remains linear over the completed target
-- when the two projection maps form a commuting triangle.
private noncomputable def restrictTriangle
    {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
    {R S T : Sheaf J RingCat.{r}} (p : R ⟶ S) (q : S ⟶ T) (p' : R ⟶ T)
    (h : p ≫ q = p') (M : SheafOfModules.{r} S) (N : SheafOfModules.{r} T)
    (k : M ⟶ (restrictScalars q).obj N) :
    (restrictScalars p).obj M ⟶ (restrictScalars p').obj N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((restrictScalars p).obj M).val.obj U)
        (Y := ((restrictScalars p').obj N).val.obj U)
        { toFun := k.val.app U
          map_add' := _root_.map_add _
          map_smul' := fun r x ↦ by
            change M.val.obj U at x
            change k.val.app U (p.hom.app U r • x) =
              p'.hom.app U r • (show N.val.obj U from k.val.app U x)
            rw [_root_.map_smul]
            have he := congrArg (fun f ↦ (f.hom.app U).hom r) h
            exact congrArg (fun a ↦ a • (show N.val.obj U from k.val.app U x)) he }
      naturality := by
        intro U V f
        ext x
        exact PresheafOfModules.naturality_apply k.val f x }

universe a' b' r'

variable {C : Type a'} [Category.{b'} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r'} RingCat.{r'})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r'}] [HasWeakSheafify J AddCommGrpCat.{r'}]

-- Tensor balancing uses the source coefficient sheaf A; the restricted action
-- uses the independent target coefficient sheaf B.
private noncomputable def scalarStep {A B S T : Sheaf J CommRingCat.{r'}}
    (f : A ⟶ S) (g : A ⟶ T) (p : B ⟶ S) (q : S ⟶ T) (p' : B ⟶ T)
    (hf : f ≫ q = g) (hp : p ≫ q = p')
    (M : SheafOfModules.{r'} ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).obj A)) :=
  restrictTriangle.{a', b', r'}
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map p)
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map q)
    ((sheafCompose J (forget₂ CommRingCat.{r'} RingCat.{r'})).map p')
    (by rw [← Functor.map_comp, hp])
    (SheafOfModules.changeOfRings.{b', a', r'} f M) (SheafOfModules.changeOfRings.{b', a', r'} g M)
    (SheafOfModules.UnrestrictedTowerProof.sheafMap f g q hf M)

end SheafOfModules.IntegralScalarProof

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The larger absolute value restricts to the specified absolute value on E.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: Compose the absolute value on L with the injective field inclusion. It extends the
p-adic absolute value. spectralNorm_unique_field_norm_ext identifies it with the
spectral absolute value on E (lem-weil-l-adic-extension-absolute-value). -/
theorem integralScalar_absoluteValue (x : E) :
    Padic.coefficientExtensionAbsoluteValue l L (ι x) =
      Padic.coefficientExtensionAbsoluteValue l E x := by
  let f : AbsoluteValue E ℝ :=
    (Padic.coefficientExtensionAbsoluteValue l L).comp ι.toRingHom.injective
  have hf : ∀ a : ℚ_[l], f (algebraMap (ℚ_[l]) E a) = ‖a‖ := by
    intro a
    change Padic.coefficientExtensionAbsoluteValue l L
      (ι (algebraMap (ℚ_[l]) E a)) = ‖a‖
    rw [ι.commutes]
    exact spectralNorm_extends a
  calc
    Padic.coefficientExtensionAbsoluteValue l L (ι x) = spectralNorm (ℚ_[l]) E x :=
      spectralNorm_unique_field_norm_ext hf x
    _ = Padic.coefficientExtensionAbsoluteValue l E x := rfl

/-- The field inclusion maps integers to integers, in independent site/coefficient sizes.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: By integralScalar_absoluteValue the two absolute values agree on x. The defining
DVR witnesses characterize membership in each integer ring by absolute value at most one.
Apply this characterization to hx and to ι x. -/
theorem integralScalar_integer_mem (x : E)
    (hx : x ∈ Padic.coefficientExtensionIntegers l E) :
    ι x ∈ Padic.coefficientExtensionIntegers l L := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
  have hL := (Padic.extension_integers_dvr l L
    (Padic.coefficientExtensionAbsoluteValue l L)
    (spectralNorm_extends (K := ℚ_[l]) (L := L))).choose_spec.choose_spec.1 (ι x)
  apply hL.mpr
  rw [integralScalar_absoluteValue l E L ι x]
  exact hE.mp hx

/-- The actual restriction of the field inclusion to the recorded valuation subrings.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarIntegerInclusion :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l L :=
  ((ι.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l L)
    (fun x ↦ integralScalar_integer_mem l E L ι x x.property))

/-- The source uniformizer powers vanish in the same-index target quotient.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The source uniformizer has absolute value less than one. By absolute-value
restriction it belongs to the target maximal ideal, generated by its uniformizer.
Taking (n+1)st powers gives the required ideal inclusion; quotienting kills its image. -/
theorem integralScalar_quotient_kernel (n : ℕ)
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E (n + 1)) :
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1)))
      (integralScalarIntegerInclusion l E L ι x) = 0 := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hL := (Padic.extension_integers_dvr l L
    (Padic.coefficientExtensionAbsoluteValue l L)
    (spectralNorm_extends (K := ℚ_[l]) (L := L))).choose_spec.choose_spec
  have hgenE : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hgenL : Ideal.span {Padic.coefficientExtensionUniformizer l L} =
      Padic.coefficientExtensionMaximalIdeal l L :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hπE : Padic.coefficientExtensionUniformizer l E ∈
      Padic.coefficientExtensionMaximalIdeal l E := by
    rw [← hgenE]
    exact Ideal.mem_span_singleton_self _
  have hπL : integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E) ∈
      Padic.coefficientExtensionMaximalIdeal l L := by
    apply (hL.2.1 _).mpr
    change Padic.coefficientExtensionAbsoluteValue l L
      (ι (Padic.coefficientExtensionUniformizer l E)) < 1
    rw [integralScalar_absoluteValue l E L ι]
    exact (hE.2.1 _).mp hπE
  rw [← hgenL, Ideal.mem_span_singleton] at hπL
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact (pow_dvd_pow_of_dvd hπL (n + 1)).trans (by
    simpa only [map_pow] using map_dvd (integralScalarIntegerInclusion l E L ι) hx)

/-- The canonical quotient map induced by inclusion of integer rings.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarQuotientMap (n : ℕ) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (n + 1) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E (n + 1))
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (n + 1))).comp
      (integralScalarIntegerInclusion l E L ι))
    (integralScalar_quotient_kernel l E L ι n)

/-- The quotient maps commute with the two canonical reductions.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: Both composites send a class represented by x to the class represented by ι x.
Quotient induction and ring-homomorphism extensionality give equality. -/
theorem integralScalarQuotientMap_transition (n : ℕ) :
    (Padic.coefficientExtensionTransition l L (n + 1)).comp
        (integralScalarQuotientMap l E L ι (n + 1)) =
      (integralScalarQuotientMap l E L ι n).comp
        (Padic.coefficientExtensionTransition l E (n + 1)) := by
  apply RingHom.ext
  intro x
  induction x using Quotient.inductionOn' with
  | h x => rfl

variable (Y : AlgebraicGeometry.Scheme.{t})

/-- The quotient inclusion after functorial constant sheafification.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarQuotientSheafMap (n : ℕ) :
    integralCoefficientCommRingSheaf l E Y n ⟶
      integralCoefficientCommRingSheaf l L Y n :=
  (constantSheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
    CommRingCat.{max u (t + 1)}).map (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E L ι n).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom)))

/-- The actual coefficient map ρ_n=(ι_n)_Y π_n, without auxiliary finite-field data.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarRho (n : ℕ) :
    completedIntegralCommRingSheafUnrestricted l E Y ⟶
      integralCoefficientCommRingSheaf l L Y n :=
  completedIntegralCommRingProjectionUnrestricted l E Y n ≫
    integralScalarQuotientSheafMap l E L ι Y n

set_option linter.defProp false in
/-- The recorded change-of-rings witness, fixing the ordinary functor on objects and maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReductionWitness (n : ℕ) :=
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)))
  letI := HasDerivedCategory.standard (SheafOfModules.{max u (t + 1)}
    (SheafOfModules.derivedChangeRingIndependentCoefficients
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l L Y n)))
  SheafOfModules.derivedChangeOfRingsIndependentCoefficients
    (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
    (O := completedIntegralCommRingSheafUnrestricted l E Y)
    (O' := integralCoefficientCommRingSheaf l L Y n)
    (integralScalarRho l E L ι Y n)

/-- Ordinary sheafified sectionwise extension along ρ_n, with its finite target action.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarReduction (n : ℕ) :
    integralTowerModules l E Y ⥤ integralOperationsFiniteModules l L Y n :=
  (integralScalarReductionWitness l E L ι Y n).choose

/-- Additivity from the canonical change-of-rings witness.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable instance integralScalarReduction_additive (n : ℕ) :
    (integralScalarReduction l E L ι Y n).Additive :=
  (integralScalarReductionWitness l E L ι Y n).choose_spec.choose_spec.choose_spec.choose

/-- Termwise extension P_{L,n}, before restriction of scalars.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarFiniteComplex (n : ℕ) :=
  (integralScalarReduction l E L ι Y n).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The complex Res^L_n(P_{L,n}) over the target completion.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarLevel (n : ℕ) :=
  integralScalarFiniteComplex l E L ι Y n ⋙ integralOperationsRestrict l L Y n

/-- The sheafified tensor generator s⊗x in the specified ordinary scalar extension.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTensorSection (n : ℕ)
    (M : integralTowerModules l E Y) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).obj M).val.obj U :=
  (eqToHom ((integralScalarReductionWitness l E L ι Y n).choose_spec.choose M).symm).val.app U
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (SheafOfModules.changeOfRingsPresheaf
        (integralScalarRho l E L ι Y n) M).presheaf).app U
          (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U,
            ((integralScalarRho l E L ι Y n).hom.app U).hom] x))

section ScalarTransitions

private theorem integralScalarQuotientSheafMap_transition (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι Y (n + 1) ≫
        unrestrictedCoefficientStep l L Y n =
      unrestrictedCoefficientStep l E Y n ≫ integralScalarQuotientSheafMap l E L ι Y n := by
  unfold integralScalarQuotientSheafMap unrestrictedCoefficientStep
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  cases x with
  | up x =>
    induction x using Quotient.inductionOn' with
    | h x => rfl

private theorem integralScalarRho_transition (n : ℕ) :
    integralScalarRho l E L ι Y (n + 1) ≫ unrestrictedCoefficientStep l L Y n =
      integralScalarRho l E L ι Y n := by
  unfold integralScalarRho
  rw [Category.assoc, integralScalarQuotientSheafMap_transition,
    ← Category.assoc, unrestrictedCoefficientStep_comp]

attribute [local irreducible] integralScalarReductionWitness

private theorem integralScalarReduction_obj (n : ℕ) (M : integralTowerModules l E Y) :
    (integralScalarReduction l E L ι Y n).obj M =
      SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)} (integralScalarRho l E L ι Y n) M :=
  (integralScalarReductionWitness l E L ι Y n).choose_spec.choose M

private theorem integralScalarReduction_map (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (integralScalarReduction l E L ι Y n).map a =
      eqToHom (integralScalarReduction_obj l E L ι Y n M) ≫
        SheafOfModules.changeOfRingsHom (integralScalarRho l E L ι Y n) M a ≫
          eqToHom (integralScalarReduction_obj l E L ι Y n N).symm :=
  (integralScalarReductionWitness l E L ι Y n).choose_spec.choose_spec.choose a

private noncomputable abbrev integralScalarRestrict (n : ℕ) :=
  SheafOfModules.restrictScalars.{max u (t + 1)}
    ((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map
        (completedIntegralCommRingProjectionUnrestricted l L Y n))

attribute [local irreducible] SheafOfModules.UnrestrictedTowerProof.sectionMap
  SheafOfModules.UnrestrictedTowerProof.presheafMap SheafOfModules.UnrestrictedTowerProof.sheafMap

private noncomputable def integralScalarModuleStepRaw (n : ℕ)
    (M : integralTowerModules l E Y) :=
  SheafOfModules.IntegralScalarProof.scalarStep.{t + 1, t, max u (t + 1)}
    (A := completedIntegralCommRingSheafUnrestricted l E Y)
    (B := completedIntegralCommRingSheafUnrestricted l L Y)
    (S := integralCoefficientCommRingSheaf l L Y (n + 1))
    (T := integralCoefficientCommRingSheaf l L Y n)
    (integralScalarRho l E L ι Y (n + 1)) (integralScalarRho l E L ι Y n)
    (completedIntegralCommRingProjectionUnrestricted l L Y (n + 1))
    (unrestrictedCoefficientStep l L Y n)
    (completedIntegralCommRingProjectionUnrestricted l L Y n)
    (integralScalarRho_transition l E L ι Y n)
    (unrestrictedCoefficientStep_comp l L Y n) M

-- The restriction functors have definitionally equal underlying section types.
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def integralScalarModuleStep (n : ℕ)
    (M : integralTowerModules l E Y) :
    (integralScalarRestrict l L Y (n + 1)).obj
        ((integralScalarReduction l E L ι Y (n + 1)).obj M) ⟶
      (integralScalarRestrict l L Y n).obj
        ((integralScalarReduction l E L ι Y n).obj M) :=
  (integralScalarRestrict l L Y (n + 1)).map
      (eqToHom (integralScalarReduction_obj l E L ι Y (n + 1) M)) ≫
    integralScalarModuleStepRaw l E L ι Y n M ≫
      (integralScalarRestrict l L Y n).map
        (eqToHom (integralScalarReduction_obj l E L ι Y n M).symm)

private theorem integralScalarModuleStep_tmul (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
    (x : M.val.obj U) :
    (integralScalarModuleStep l E L ι Y n M).val.app U
      (integralScalarTensorSection l E L ι Y (n + 1) M U s x) =
    integralScalarTensorSection l E L ι Y n M U
      ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  have hc : ∀ z :
      (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)}
        (integralScalarRho l E L ι Y (n + 1)) M).val.obj U,
      (eqToHom (integralScalarReduction_obj l E L ι Y (n + 1) M)).val.app U
        ((eqToHom (integralScalarReduction_obj l E L ι Y (n + 1) M).symm).val.app U z) = z := by
    intro z
    exact ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app U) (eqToHom_trans
        (integralScalarReduction_obj l E L ι Y (n + 1) M).symm
        (integralScalarReduction_obj l E L ι Y (n + 1) M))) z
  change (eqToHom (integralScalarReduction_obj l E L ι Y n M).symm).val.app U
    ((integralScalarModuleStepRaw l E L ι Y n M).val.app U
      ((eqToHom (integralScalarReduction_obj l E L ι Y (n + 1) M)).val.app U
        ((eqToHom (integralScalarReduction_obj l E L ι Y (n + 1) M).symm).val.app U _))) = _
  rw [hc]
  exact congrArg ((eqToHom (integralScalarReduction_obj l E L ι Y n M).symm).val.app U)
    (SheafOfModules.UnrestrictedTowerProof.sheafMap_tmul
      (integralScalarRho l E L ι Y (n + 1)) (integralScalarRho l E L ι Y n)
      (unrestrictedCoefficientStep l L Y n) (integralScalarRho_transition l E L ι Y n) M U s x)

private theorem integralScalarReduction_hom_ext (n : ℕ) (M : integralTowerModules l E Y)
    (N : integralTowerModules l L Y)
    (a b : (integralScalarRestrict l L Y n).obj
      ((integralScalarReduction l E L ι Y n).obj M) ⟶ N)
    (h : ∀ U s x, a.val.app U (integralScalarTensorSection l E L ι Y n M U s x) =
      b.val.app U (integralScalarTensorSection l E L ι Y n M U s x)) : a = b := by
  let e := (integralScalarRestrict l L Y n).map
    (eqToHom (integralScalarReduction_obj l E L ι Y n M).symm)
  have he : e ≫ a = e ≫ b := by
    apply (SheafOfModules.toSheaf _).map_injective
    apply Sheaf.hom_ext
    apply CategoryTheory.sheafify_hom_ext _ _ _ N.isSheaf
    ext U z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul s x => exact h U s x
    | add z w hz hw => simpa only [_root_.map_add] using congrArg₂ (· + ·) hz hw
  have hi := congrArg (fun k ↦ (integralScalarRestrict l L Y n).map
    (eqToHom (integralScalarReduction_obj l E L ι Y n M)) ≫ k) he
  dsimp only [e] at hi
  simp only [← Category.assoc, ← Functor.map_comp, eqToHom_trans, eqToHom_refl] at hi
  simpa only [(integralScalarRestrict l L Y n).map_id, Category.id_comp] using hi

attribute [local irreducible] integralScalarModuleStepRaw integralScalarModuleStep

private theorem integralScalarModuleStep_naturality (n : ℕ)
    {M N : integralTowerModules l E Y} (a : M ⟶ N) :
    (integralScalarRestrict l L Y (n + 1)).map
        ((integralScalarReduction l E L ι Y (n + 1)).map a) ≫
        integralScalarModuleStep l E L ι Y n N =
      integralScalarModuleStep l E L ι Y n M ≫
        (integralScalarRestrict l L Y n).map ((integralScalarReduction l E L ι Y n).map a) := by
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) M
  intro U s x
  have hm (k : ℕ) (t : (integralCoefficientCommRingSheaf l L Y k).obj.obj U) :
      ((integralScalarReduction l E L ι Y k).map a).val.app U
        (integralScalarTensorSection l E L ι Y k M U t x) =
      integralScalarTensorSection l E L ι Y k N U t (a.val.app U x) := by
    rw [integralScalarReduction_map]
    change (eqToHom (integralScalarReduction_obj l E L ι Y k N).symm).val.app U
      ((SheafOfModules.changeOfRingsHom (integralScalarRho l E L ι Y k) M a).val.app U
        ((eqToHom (integralScalarReduction_obj l E L ι Y k M)).val.app U
          ((eqToHom (integralScalarReduction_obj l E L ι Y k M).symm).val.app U _))) = _
    have hc := eqToHom_trans (integralScalarReduction_obj l E L ι Y k M).symm
      (integralScalarReduction_obj l E L ι Y k M)
    have hc' (z :
        (SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)}
          (integralScalarRho l E L ι Y k) M).val.obj U) :
        (eqToHom (integralScalarReduction_obj l E L ι Y k M)).val.app U
          ((eqToHom (integralScalarReduction_obj l E L ι Y k M).symm).val.app U z) = z :=
      ConcreteCategory.congr_hom (congrArg (fun f ↦ f.val.app U) hc) z
    rw [hc']
    exact congrArg ((eqToHom (integralScalarReduction_obj l E L ι Y k N).symm).val.app U)
      (SheafOfModules.UnrestrictedTowerProof.map_tensorSection
        (integralScalarRho l E L ι Y k) M a U t x)
  change (integralScalarModuleStep l E L ι Y n N).val.app U
      (((integralScalarReduction l E L ι Y (n + 1)).map a).val.app U _) =
    ((integralScalarReduction l E L ι Y n).map a).val.app U
      ((integralScalarModuleStep l E L ι Y n M).val.app U _)
  rw [hm, integralScalarModuleStep_tmul, integralScalarModuleStep_tmul, hm]

/-- The transition is the unique natural chain map sending s⊗x to red(s)⊗x.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: integralScalarQuotientMap_transition and functoriality of constant sheafification
make ρ_n equal to reduction after ρ_(n+1). The stated tensor formula is therefore
balanced. The target limit projections make it linear over the target completion.
It commutes with restrictions, differentials and maps in P; sheafification gives τ.
Pure tensors generate locally, so the formula determines τ uniquely. -/
theorem integralScalarTransition_existsUnique (n : ℕ) :
    ∃! τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (s : (integralCoefficientCommRingSheaf l L Y (n + 1)).obj.obj U)
        (x : (P.X i).val.obj U),
        ((τ.app P).f i).val.app U
          (integralScalarTensorSection l E L ι Y (n + 1) (P.X i) U s x) =
        integralScalarTensorSection l E L ι Y n (P.X i) U
          ((integralCoefficientSheafTransition l L Y n).hom.app U s) x := by
  let τ : integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n :=
    { app := fun P ↦
        { f := fun i ↦ integralScalarModuleStep l E L ι Y n (P.X i)
          comm' := fun i j _ ↦ (integralScalarModuleStep_naturality l E L ι Y n
            (P.d i j)).symm }
      naturality := fun P Q a ↦ by
        apply HomologicalComplex.hom_ext
        intro i
        exact integralScalarModuleStep_naturality l E L ι Y n (a.f i) }
  refine ⟨τ, (fun P i U s x ↦ integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x), ?_⟩
  intro τ' hτ'
  apply NatTrans.ext
  funext P
  apply HomologicalComplex.hom_ext
  intro i
  apply integralScalarReduction_hom_ext l E L ι Y (n + 1) (P.X i)
  intro U s x
  exact (hτ' P i U s x).trans (integralScalarModuleStep_tmul l E L ι Y n (P.X i) U s x).symm

end ScalarTransitions

/-- The canonical transition, selected from a theorem that determines it uniquely.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTransition (n : ℕ) :
    integralScalarLevel l E L ι Y (n + 1) ⟶ integralScalarLevel l E L ι Y n :=
  (integralScalarTransition_existsUnique l E L ι Y n).exists.choose

/-- The strict tower, including its action on all chain maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarTowerFunctor :=
  (Functor.ofOpSequence (X := fun n ↦ integralScalarLevel l E L ι Y n)
    (integralScalarTransition l E L ι Y)).flip

/-- The fixed Cone(1-s)[-1] functor with termwise products and diagonal cone maps.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarComplexFunctor :=
  integralScalarTowerFunctor l E L ι Y ⋙ integralOperationsRoosFunctor

/-- The specified Roos construction on K-flat flat-term representatives, localized.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarOnGood :=
  (integralOperationsGoodComplex l E Y).ι ⋙
    integralScalarComplexFunctor l E L ι Y ⋙ DerivedCategory.Q

/-- The constant section of the finite ring sheaf represented by a modulo ϖ_E^(n+1).
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarFiniteConstant (n : ℕ) (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (integralCoefficientSheaf l E Y n).obj.obj U :=
  ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    ((Functor.const Y.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app U)
        (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a))

/-- The constant section of the completion is determined by all its finite residues.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The displayed finite constant sections commute with reduction, because both
orders send a to its class. Limits of ring sheaves are sectionwise. Their universal
property supplies the compatible tuple, and the projections are jointly injective. -/
theorem integralScalarConstant_existsUnique (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    ∃! s : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U,
      ∀ n : ℕ,
        ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U) s =
          integralScalarFiniteConstant l E Y n U a := by
  let b : (integralConstantRingOfUniverses l E Y).obj.obj U :=
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U)
      (ULift.up a)
  let s := (integralConstantToCompletionOfUniverses l E Y).hom.app U b
  have hs : ∀ n : ℕ,
      ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U) s =
        integralScalarFiniteConstant l E Y n U a := by
    intro n
    have hπ := congrArg (fun f ↦ f.hom.app U)
      (limit.lift_π (integralConstantConeOfUniverses l E Y) (op n))
    have hcomp :
        (integralConstantToCompletionOfUniverses l E Y).hom.app U ≫
            (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U =
          ((integralConstantConeOfUniverses l E Y).π.app (op n)).hom.app U := by
      change (limit.lift (integralCoefficientSheafSystem l E Y)
          (integralConstantConeOfUniverses l E Y)).hom.app U ≫
          (limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U = _
      exact hπ
    have hb := congrArg (fun f ↦ f.hom b) hcomp
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U).hom
      (((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom b) = _ at hb
    change ((limit.π (integralCoefficientSheafSystem l E Y) (op n)).hom.app U).hom
      (((integralConstantToCompletionOfUniverses l E Y).hom.app U).hom b) = _
    refine hb.trans ?_
    let q := CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
    have hn := congrArg (fun f ↦ (f.app U).hom (ULift.up a))
      (toSheafify_naturality (AlgebraicGeometry.Scheme.ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).map q))
    exact hn.symm
  refine ⟨s, hs, ?_⟩
  intro s' hs'
  let h₁ := isLimitOfPreserves
    (sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat)
    (limit.isLimit (integralCoefficientSheafSystem l E Y))
  let h₂ := isLimitOfPreserves ((evaluation _ _).obj U) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  exact (hs' n.unop).trans (hs n.unop).symm

/-- The unique constant global section, restricted to the site object U.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarConstant (U : Y.ProEtᵒᵖ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U :=
  (integralScalarConstant_existsUnique l E Y U a).exists.choose

private theorem integralScalarConstant_naturality {U V : Y.ProEtᵒᵖ}
    (f : U ⟶ V) (a : Padic.coefficientExtensionIntegers l E) :
    (completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
      (integralScalarConstant l E Y U a) = integralScalarConstant l E Y V a := by
  let h₁ := isLimitOfPreserves
    (sheafToPresheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) RingCat)
    (limit.isLimit (integralCoefficientSheafSystem l E Y))
  let h₂ := isLimitOfPreserves ((evaluation _ _).obj V) h₁
  apply Concrete.isLimit_ext _ h₂
  intro n
  change ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
    ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      (integralScalarConstant l E Y V a)
  have hn := congrArg (fun k ↦ k.hom (integralScalarConstant l E Y U a))
    ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.naturality f)
  change ((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app V)
      ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.map f
        (integralScalarConstant l E Y U a)) =
      (integralCoefficientSheaf l E Y n.unop).obj.map f
        (((limit.π (integralCoefficientSheafSystem l E Y) n).hom.app U)
          (integralScalarConstant l E Y U a)) at hn
  rw [hn]
  erw [(integralScalarConstant_existsUnique l E Y U a).exists.choose_spec n.unop,
    (integralScalarConstant_existsUnique l E Y V a).exists.choose_spec n.unop]
  have h := congrArg
    (fun k ↦ k.hom
      (ULift.up ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))) a)))
    ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj
        (CommRingCat.of
          (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n.unop + 1)))))).naturality f)
  exact h.symm

/-- Multiplication by the constant section is a uniquely specified natural chain map.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: The sections from integralScalarConstant are compatible with restrictions by
their uniqueness and their finite residue formulas. Multiplication is linear over
the completed commutative ring. It commutes with differentials and module maps,
giving σ. Equality on every degree and every section proves uniqueness. -/
theorem integralScalarChainAction_existsUnique (a : Padic.coefficientExtensionIntegers l E) :
    ∃! σ : 𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
        𝟭 (CochainComplex (integralTowerModules l E Y) ℤ),
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (U : Y.ProEtᵒᵖ)
        (x : (P.X i).val.obj U),
        ((σ.app P).f i).val.app U x = integralScalarConstant l E Y U a • x := by
  let μ : ∀ M : integralTowerModules l E Y, M ⟶ M := fun M ↦
    { val :=
        { app := fun U ↦ by
            let : CommRing ((completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :=
              inferInstanceAs
                (CommRing ((completedIntegralCommRingSheafUnrestricted l E Y).obj.obj U))
            exact ModuleCat.ofHom
              { toFun := fun x ↦ integralScalarConstant l E Y U a • x
                map_add' := smul_add _
                map_smul' := fun r x ↦ smul_comm _ r x }
          naturality := by
            intro U V f
            ext x
            change integralScalarConstant l E Y V a • M.val.map f x =
              M.val.map f (integralScalarConstant l E Y U a • x)
            rw [M.val.map_smul, integralScalarConstant_naturality l E Y f a] } }
  have hμ : ∀ {M N : integralTowerModules l E Y} (f : M ⟶ N),
      f ≫ μ N = μ M ≫ f := by
    intro M N f
    ext U x
    exact ((f.val.app U).hom.map_smul (integralScalarConstant l E Y U a) x).symm
  let σ : 𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
      𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) :=
    { app := fun P ↦
        { f := fun i ↦ μ (P.X i)
          comm' := fun i j _ ↦ (hμ (P.d i j)).symm }
      naturality := by
        intro P Q f
        apply HomologicalComplex.hom_ext
        intro i
        exact hμ (f.f i) }
  refine ⟨σ, ?_, ?_⟩
  · intro P i U x
    rfl
  · intro σ' hσ'
    apply NatTrans.ext
    funext P
    apply HomologicalComplex.hom_ext
    intro i
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact hσ' P i U x

/-- The actual constant-section scalar endomorphism of the identity on complexes.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarChainAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) ⟶
      𝟭 (CochainComplex (integralTowerModules l E Y) ℤ) :=
  (integralScalarChainAction_existsUnique l E Y a).exists.choose

/-- The canonical scalar endomorphism after localization. Its composite with f is a f;
this is the constant-section action of lem-weil-linear-abelian-derived-category.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined). -/
noncomputable def integralScalarDerivedAction (a : Padic.coefficientExtensionIntegers l E) :
    𝟭 (DerivedCategory (integralTowerModules l E Y)) ⟶
      𝟭 (DerivedCategory (integralTowerModules l E Y)) :=
  (Localization.fullyFaithfulWhiskeringLeft
    (DerivedCategory.Q : CochainComplex (integralTowerModules l E Y) ℤ ⥤ _)
    (HomologicalComplex.quasiIso (integralTowerModules l E Y) (ComplexShape.up ℤ))
    (DerivedCategory (integralTowerModules l E Y))).preimage
      (whiskerRight (integralScalarChainAction l E Y a) DerivedCategory.Q)

/-- The three assertions: levelwise and Roos quasi-isomorphism invariance, additive
shift-compatible descent unique with its representative comparisons and derived-limit
values, and linearity for the actual constant-section actions.
Source: Bhatt--Scholze, Proposition 6.8.14(1); Stacks Tags 06YT and 08TC
(blueprint: lem-weil-integral-scalar-extension-well-defined).
Proof: 1. The extending absolute values agree, giving the integer inclusion and quotient
maps above. Their reductions commute; tensor transitions are the canonical balanced
formula, linear over the target completion.
2. Apply lem-pur-change-of-rings-kflat-quasi-iso to ρ_n. No flatness of the quotient
is needed. Restriction of scalars preserves cohomology, so all tower level maps
are quasi-isomorphisms and commute strictly with transitions.
3. Exact countable products (lem-weil-proetale-countable-products-exact) and
lem-weil-derived-limit-existence identify termwise products with derived products.
The rotated cone triangle is the Roos triangle of def-weil-derived-limit. The
diagonal product map is a triangle morphism; lem-weil-derived-limit-levelwise-iso
makes its first map invertible. Cohomology detects the asserted quasi-isomorphism.
4. Coefficient change, products, and diagonal cone maps preserve addition and
homotopies. For d(b,a)=(-db-(1-s)a,da), a compatible product homotopy h induces
H(b,a)=(-hb,ha); the cross terms cancel. Thus the construction factors through
the good homotopy representatives.
5. lem-weil-pbc-site-derived-tensor-descent identifies their quasi-isomorphism
localization with D(R). Descend using lem-weil-pbc-localization-universal-property.
Finite biproduct preservation proves additivity. Localization fully faithfulness
gives exactly the unique natural isomorphism compatible with e and e'.
6. Choose models by lem-pc-kflat-resolution. The comparison e_P and the inverse
image of q under F identify F(K) with the specified Roos value. Transport maps by
these comparisons; a second model choice gives their composite. The derived-limit
property transports along these isomorphisms. This needs no chain lift of a
derived morphism and asserts no uniqueness of arbitrary Roos-triangle fillers.
7. Shift preserves K-flatness and flat terms. The natural map (b,a)↦(-b,a)
identifies T(P[1]) with T(P)[1] with the displayed cone signs. Localization extends
it to the asserted shift comparison.
8. Constant sections act on the module category and descend to the canonical
action of lem-weil-linear-abelian-derived-category. Tensor balancing gives
(ax)⊗b=x⊗ι(a)b, also on every product and cone summand. Localization uniqueness
identifies the two natural endomorphisms on D(R). Compose with f to obtain the
displayed scalar-linearity equality; conjugation by the model comparisons preserves it. -/
theorem integralScalarExtensionWellDefined :
    (∀ (P P' : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (f : P.obj ⟶ P'.obj), QuasiIso f →
      (∀ n : ℕ, QuasiIso ((integralScalarFiniteComplex l E L ι Y n).map f)) ∧
        QuasiIso ((integralScalarComplexFunctor l E L ι Y).map f)) ∧
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l L Y))
      (e : integralOperationsGoodLocalization l E Y ⋙ F ≅ integralScalarOnGood l E L ι Y),
      F.Additive ∧ Nonempty (F.CommShift ℤ) ∧
      (∀ (F' : DerivedCategory (integralTowerModules l E Y) ⥤
          DerivedCategory (integralTowerModules l L Y))
        (e' : integralOperationsGoodLocalization l E Y ⋙ F' ≅
          integralScalarOnGood l E L ι Y),
        ∃! α : F ≅ F',
          isoWhiskerLeft (integralOperationsGoodLocalization l E Y) α ≪≫ e' = e) ∧
      (∀ (K : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (_q : DerivedCategory.Q.obj P.obj ≅ K),
        Nonempty (F.obj K ≅ DerivedCategory.Q.obj
          ((integralScalarComplexFunctor l E L ι Y).obj P.obj)) ∧
        integralOperationsDerivedLimitProperty l L Y
          ((integralScalarTowerFunctor l E L ι Y).obj P.obj) (F.obj K)) ∧
      (∀ (a : Padic.coefficientExtensionIntegers l E)
        (K K' : DerivedCategory (integralTowerModules l E Y)) (f : K ⟶ K'),
        F.map ((integralScalarDerivedAction l E Y a).app K ≫ f) =
          (integralScalarDerivedAction l L Y
            (integralScalarIntegerInclusion l E L ι a)).app (F.obj K) ≫ F.map f) := by
  sorry

end WeilConjectures
