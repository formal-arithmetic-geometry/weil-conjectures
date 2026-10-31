/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.Finite.FiniteDualizing
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionQuotientMultiplicationUnit

/-! Finite reduction of the multiplication unit on a dualizing object. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
attribute [local instance 5000] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem left_unit_transport
    {C I : Type*} [Category C]
    (F G : I → C ⥤ C) (a : ∀ i, F i ⊣ G i)
    (i i₀ : I) (h : i = i₀) (e : G i₀ ≅ 𝟭 C) :
    (a i).leftAdjointIdIso (eqToIso (congrArg G h) ≪≫ e) =
      eqToIso (congrArg F h) ≪≫ (a i₀).leftAdjointIdIso e := by
  subst i
  simp only [eqToIso_refl, Iso.refl_trans]

-- Compare the identity-extension normalization with the normalized DVR quotient.

private theorem restrictIdentity_refl {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose =
      eqToIso (rfl : pbcRestrict (𝟙 R) = 𝟭 (pbcModules X R)) := by
  apply (PurCompactSupport.restrictIdentity_existsUnique R).unique
  · exact (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
  · intro M U x
    rfl

private theorem derived_unit_heq
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    (F G : A ⥤ A) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (hF : F = 𝟭 A) (hG : G = 𝟭 A) :
    HEq (Functor.mapDerivedCategoryNatIso (eqToIso hF) ≪≫
      Functor.mapDerivedCategoryIdIso A)
      (Functor.mapDerivedCategoryNatIso (eqToIso hG) ≪≫
        Functor.mapDerivedCategoryIdIso A) := by
  subst F
  subst G
  rfl

private theorem derived_scalar_unit_eq {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (φ : R ⟶ R) (hφ : φ = 𝟙 R) :
    eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedRestrict (X := X) f) hφ) ≪≫
      Functor.mapDerivedCategoryNatIso
        (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _ =
    Functor.mapDerivedCategoryNatIso
      (eqToIso (show pbcRestrict φ = 𝟭 (pbcModules X R) by rw [hφ]; rfl)) ≪≫
      Functor.mapDerivedCategoryIdIso _ := by
  subst φ
  rw [restrictIdentity_refl]
  simp only [eqToIso_refl, Iso.refl_trans]

private theorem quotient_sheaf_id (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n = 𝟙 _ := by
  have hq : integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n =
      RingHom.id _ := by
    ext x
    rfl
  unfold integralScalarQuotientSheafMap
  rw [hq]
  convert (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map_id
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) using 1 <;> rfl

private theorem restriction_unit_heq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (n : ℕ) :
    HEq (eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedRestrict (X := X) f)
      (quotient_sheaf_id l E X n)) ≪≫
      Functor.mapDerivedCategoryNatIso
        (PurCompactSupport.restrictIdentity_existsUnique
          (integralCoefficientCommRingSheaf l E X n)).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _)
      (normalizedDVRResUnit l E X n) := by
  rw [derived_scalar_unit_eq _ _ (quotient_sheaf_id l E X n)]
  unfold normalizedDVRResUnit
  let := (normalizedDVRModuleRes_exact l E X (le_refl n)).1
  let := (normalizedDVRModuleRes_exact l E X (le_refl n)).2
  exact derived_unit_heq
    (pbcRestrict (integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n))
    (normalizedDVRModuleRes l E X (le_refl n))
    (by rw [quotient_sheaf_id]; rfl)
    (congrArg (fun f ↦ SheafOfModules.restrictScalars.{u + 1} f)
      ((integralCoefficientSheafSystem l E X).map_id (Opposite.op n)))

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem identity_base (n : ℕ) :
    integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n =
      finiteDualizingQuotientBase l E (le_refl n) := by
  ext x
  rfl

private theorem identity_restrict (n : ℕ) :
    pbcDerivedRestrict (integralScalarQuotientSheafMap l E E
      (AlgHom.id (Padic l) E) X n) = normalizedDVRRes l E X (le_refl n) := by
  change (finiteDualizingIntrinsicRes X
    (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n)).mapDerivedCategory = _
  rw [identity_base]
  unfold normalizedDVRRes
  congr 1
  exact (finiteDualizingRestriction_eq l E X (le_refl n)).symm

private theorem paste_identity_heq
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {U U' : C ⥤ B} {V : A ⥤ D} {G : D ⥤ F} {H : B ⥤ E}
    {S S' : A ⥤ C} {T T' : D ⥤ B} {R R' : F ⥤ E}
    (p : V ⋙ T ≅ S ⋙ U) (p' : V ⋙ T' ≅ S' ⋙ U')
    (q : G ⋙ R ≅ T ⋙ H) (q' : G ⋙ R' ≅ T' ⋙ H)
    (hU : U = U') (hS : S = S') (hT : T = T') (hR : R = R') (hp : HEq p p') (hq : HEq q q') :
    HEq
      (Functor.associator V G R ≪≫ Functor.isoWhiskerLeft V q ≪≫
        (Functor.associator V T H).symm ≪≫ Functor.isoWhiskerRight p H ≪≫
        Functor.associator S U H)
      (Functor.associator V G R' ≪≫ Functor.isoWhiskerLeft V q' ≪≫
        (Functor.associator V T' H).symm ≪≫ Functor.isoWhiskerRight p' H ≪≫
        Functor.associator S' U' H) := by
  subst U'
  subst S'
  subst T'
  subst R'
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

private theorem identity_realization (n : ℕ) :
    HEq (finiteRealizationRestriction l E E (AlgHom.id (Padic l) E) X n)
      (finiteDualizingRealizationRestriction l E X (le_refl n)) := by
  have hring : RingHom.ulift.{u + 1, u + 1}
      (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n) =
      finiteDualizingQuotient l E (le_refl n) :=
    congrArg RingHom.ulift (identity_base l E n)
  have hp : HEq (ProEtale.pbcDerivedComparisonRestrict X
      (RingHom.ulift.{u + 1, u + 1}
        (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n)))
      (ProEtale.pbcDerivedComparisonRestrict X (finiteDualizingQuotient l E (le_refl n))) := by
    rw [hring]
  have hq : HEq (finiteDualizingGenericDerivedRestriction X
      (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n))
      (finiteDualizingIntrinsicRestriction l E X (le_refl n)) := by
    rw [identity_base]
    exact (finiteDualizingIntrinsicRestriction_existsUnique l E X (le_refl n)).choose_spec.1.symm
  have hpaste := paste_identity_heq
    (ProEtale.pbcDerivedComparisonRestrict X
      (RingHom.ulift.{u + 1, u + 1}
        (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n)))
    (ProEtale.pbcDerivedComparisonRestrict X (finiteDualizingQuotient l E (le_refl n)))
    (finiteDualizingGenericDerivedRestriction X
      (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n))
    (finiteDualizingIntrinsicRestriction l E X (le_refl n)) rfl
    (congrArg (Sheaf.derivedRestrictScalars X.smallEtaleTopology) hring)
    (congrArg (Sheaf.derivedRestrictScalars (ProEt.topology X)) hring)
    (identity_restrict l E X n) hp hq
  exact hpaste

private theorem conjugated_transition_heq
    {C D : Type*} [Category C] [Category D]
    (F : D ⥤ C) (K : D) (M : C) (e : F.obj K ≅ M)
    (R S : C ⥤ C) (U V : D ⥤ D)
    (a : F ⋙ R ≅ U ⋙ F) (b : F ⋙ S ≅ V ⋙ F)
    (v : K ⟶ U.obj K) (w : K ⟶ V.obj K)
    (hR : R = S) (hU : U = V) (ha : HEq a b) (hv : HEq v w) :
    HEq (e.inv ≫ F.map v ≫ a.inv.app K ≫ R.map e.hom)
      (e.inv ≫ F.map w ≫ b.inv.app K ≫ S.map e.hom) := by
  subst S
  subst V
  cases eq_of_heq ha
  cases eq_of_heq hv
  rfl

private theorem identity_transition (n : ℕ) :
    HEq ((pbcDerivedScalarAdjunction (integralScalarQuotientSheafMap l E E
      (AlgHom.id (Padic l) E) X n)).homEquiv _ _
        (finiteU l E E (AlgHom.id (Padic l) E) X D n))
      (integralDualizingExceptionalTransition l E D X hl (le_refl n)) := by
  unfold finiteU
  rw [Equiv.apply_symm_apply]
  have hring : RingHom.ulift.{u + 1, u + 1}
      (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n) =
      finiteDualizingQuotient l E (le_refl n) :=
    congrArg RingHom.ulift (identity_base l E n)
  have hv : HEq
      ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology
        (RingHom.ulift.{u + 1, u + 1}
          (integralScalarQuotientMap l E E (AlgHom.id (Padic l) E) n)))).homEquiv _ _
        (finiteEtaleU l E E (AlgHom.id (Padic l) E) X D n))
      (finiteDualizingEtaleTransition l E D X (le_refl n)) := by
    unfold finiteDualizingEtaleTransition finiteEtaleU finiteDualizingEtaleComparison
    rw [hring]
  unfold integralDualizingExceptionalTransition
  exact conjugated_transition_heq _ _ _ _ _ _ _ _ _ _ _ _
    (identity_restrict l E X n)
    (congrArg (Sheaf.derivedRestrictScalars X.smallEtaleTopology) hring)
    (identity_realization l E X n) hv

private theorem transfer_unit
    {C : Type*} [Category C] (R S : C ⥤ C) (K : C)
    (v : K ⟶ R.obj K) (w : K ⟶ S.obj K)
    (e : R ≅ 𝟭 C) (f : S ≅ 𝟭 C)
    (hR : R = S) (hv : HEq v w) (he : HEq e f)
    (hw : w ≫ f.hom.app K = 𝟙 K) : v ≫ e.hom.app K = 𝟙 K := by
  subst S
  cases eq_of_heq hv
  cases eq_of_heq he
  exact hw

private theorem scalar_left_unit_eq {Y : Scheme.{u}}
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (φ : R ⟶ R) (hφ : φ = 𝟙 R) :
    (pbcDerivedScalarAdjunction φ).leftAdjointIdIso
      (eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedRestrict (X := Y) f) hφ) ≪≫
        Functor.mapDerivedCategoryNatIso
          (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _) =
      eqToIso (congrArg (fun f : R ⟶ R ↦ pbcDerivedExtend (X := Y) f) hφ) ≪≫
        PurCompactSupport.tensorIdentity R := by
  exact left_unit_transport
    (fun f : R ⟶ R ↦ pbcDerivedExtend (X := Y) f)
    (fun f : R ⟶ R ↦ pbcDerivedRestrict (X := Y) f)
    (fun f ↦ pbcDerivedScalarAdjunction f) φ (𝟙 R) hφ
    (Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.restrictIdentity_existsUnique R).exists.choose ≪≫
        Functor.mapDerivedCategoryIdIso _)

private theorem adjunct_unit
    {C : Type*} [Category C] {F R : C ⥤ C}
    (a : F ⊣ R) (e : R ≅ 𝟭 C) (K : C) :
    a.homEquiv K K ((a.leftAdjointIdIso e).hom.app K) = e.inv.app K := by
  change a.unit.app K ≫ R.map ((a.leftAdjointIdIso e).hom.app K) = e.inv.app K
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) a (a.leftAdjointIdIso e).hom K
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at h
  change 𝟙 K ≫ e.inv.app K = a.unit.app K ≫ R.map _ at h
  erw [Category.id_comp] at h
  exact h.symm

private theorem adjunct_inverse_unit
    {C : Type*} [Category C] {F R : C ⥤ C}
    (a : F ⊣ R) (e : R ≅ 𝟭 C) (K : C) (v : F.obj K ⟶ K)
    (hv : a.homEquiv K K v ≫ e.hom.app K = 𝟙 K) :
    v = (a.leftAdjointIdIso e).hom.app K := by
  apply (a.homEquiv K K).injective
  rw [adjunct_unit]
  apply (cancel_mono (e.hom.app K)).mp
  exact hv.trans (Iso.inv_hom_id_app e K).symm

include hl in
private theorem finiteU_unit (n : ℕ) :
    finiteU l E E (AlgHom.id (Padic l) E) X D n =
      (eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedExtend (X := X) f)
      (quotient_sheaf_id l E X n)) ≪≫
        PurCompactSupport.tensorIdentity (integralCoefficientCommRingSheaf l E X n)).hom.app
          (integralDualizingFiniteTerm l E D X n) := by
  let φ := integralScalarQuotientSheafMap l E E (AlgHom.id (Padic l) E) X n
  let a := pbcDerivedScalarAdjunction φ
  let M := integralDualizingFiniteTerm l E D X n
  let e := eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedRestrict (X := X) f)
      (quotient_sheaf_id l E X n)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (PurCompactSupport.restrictIdentity_existsUnique
        (integralCoefficientCommRingSheaf l E X n)).exists.choose ≪≫
    Functor.mapDerivedCategoryIdIso _
  have ht := transfer_unit (pbcDerivedRestrict φ) (normalizedDVRRes l E X (le_refl n)) M
    (a.homEquiv M M (finiteU l E E (AlgHom.id (Padic l) E) X D n))
    (integralDualizingExceptionalTransition l E D X hl (le_refl n))
    e (normalizedDVRResUnit l E X n) (identity_restrict l E X n)
    (identity_transition l E X D hl n) (restriction_unit_heq l E X n)
    ((finiteDualizingCoefficientComparisons l E D X hl).2.2.2.2.1 n)
  calc
    _ = (a.leftAdjointIdIso e).hom.app M :=
      adjunct_inverse_unit a e M (finiteU l E E (AlgHom.id (Padic l) E) X D n) ht
    _ = _ := congrArg
      (fun i : pbcDerivedExtend φ ≅
          𝟭 (DerivedCategory (pbcModules X (integralCoefficientCommRingSheaf l E X n))) ↦
        i.hom.app M)
      (scalar_left_unit_eq (Y := X) (integralCoefficientCommRingSheaf l E X n)
        φ (quotient_sheaf_id l E X n))

/-- The multiplication unit satisfies each defining finite dualizing square.
Source: current blueprint lem-coef-integral-finite-extension, final paragraph,
unit equations transported from the finite comparisons.
(blueprint: lem-sf-integral-finite-extension-unit-reduction)

Proof: expand quotient into the inverse completion comparison, the finite
reduction comparison and the coefficient tensor square. Naturality of the
finite-reduction comparison cancels the completion factors against those
in unit. The identity coefficient map acts as identity on every quotient.
The finite exceptional comparison is the adjunction transpose of scalar
extension of its counit, hence equals the multiplication unit by the
adjunction triangle identities. Its realization on the pro-etale site
preserves that normalization. Substitute this identity into the tensor
square. What remains is naturality of the multiplication unit with respect
to (wE.reduction n).hom. This is a calculation at one finite level; it
uses neither reconstruction nor detection of integral morphisms. The same
calculation covers n=0, a zero dualizing object, and empty X. -/
theorem unit_dualizing_reduction
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E)
    (n : ℕ) :
    (scalarReductionDerivedExtension l E X n).map
        (unit l E X wE.omega.obj wE.omega.property.1).hom ≫ (wE.reduction n).hom =
      (quotient l E E (AlgHom.id (Padic l) E) X n
          wE.omega.obj wE.omega.property.1).hom ≫
        (pbcDerivedExtend (integralScalarQuotientSheafMap l E E
          (AlgHom.id (Padic l) E) X n)).map (wE.reduction n).hom ≫
        finiteU l E E (AlgHom.id (Padic l) E) X D n := by
  let e := eqToIso (congrArg (fun f : integralCoefficientCommRingSheaf l E X n ⟶
        integralCoefficientCommRingSheaf l E X n ↦ pbcDerivedExtend (X := X) f)
      (quotient_sheaf_id l E X n)) ≪≫
    PurCompactSupport.tensorIdentity (integralCoefficientCommRingSheaf l E X n)
  rw [finiteU_unit l E X D hl n]
  rw [show (pbcDerivedExtend (integralScalarQuotientSheafMap l E E
      (AlgHom.id (Padic l) E) X n)).map (wE.reduction n).hom ≫
        e.hom.app (integralDualizingFiniteTerm l E D X n) =
      e.hom.app ((scalarReductionDerivedExtension l E X n).obj wE.omega.obj) ≫
        (wE.reduction n).hom from e.hom.naturality (wE.reduction n).hom]
  rw [← Category.assoc, ← quotient_multiplication_unit l E X n (quotient_sheaf_id l E X n)]

end WeilConjectures.IntegralFiniteExtension
