/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor

/-! # Normalized finite-field stages and their coherence

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-stage-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace CategoryTheory.Functor

/-- Associativity of comparison isomorphisms transfers along componentwise
normalizations `N : R ≅ S` of all functors involved. -/
theorem conjugateComp_assoc {C₀ C₁ C₂ C₃ : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category C₃]
    {R₀₁ S₀₁ : C₀ ⥤ C₁} {R₁₂ S₁₂ : C₁ ⥤ C₂} {R₂₃ S₂₃ : C₂ ⥤ C₃}
    {R₀₂ S₀₂ : C₀ ⥤ C₂} {R₁₃ S₁₃ : C₁ ⥤ C₃} {R₀₃ S₀₃ : C₀ ⥤ C₃}
    (N₀₁ : R₀₁ ≅ S₀₁) (N₁₂ : R₁₂ ≅ S₁₂) (N₂₃ : R₂₃ ≅ S₂₃) (N₀₂ : R₀₂ ≅ S₀₂)
    (N₁₃ : R₁₃ ≅ S₁₃) (N₀₃ : R₀₃ ≅ S₀₃)
    (c₀₁₂ : R₀₁ ⋙ R₁₂ ≅ R₀₂) (c₀₂₃ : R₀₂ ⋙ R₂₃ ≅ R₀₃) (c₁₂₃ : R₁₂ ⋙ R₂₃ ≅ R₁₃)
    (c₀₁₃ : R₀₁ ⋙ R₁₃ ≅ R₀₃)
    (h : ∀ K, R₂₃.map (c₀₁₂.hom.app K) ≫ c₀₂₃.hom.app K =
      c₁₂₃.hom.app (R₀₁.obj K) ≫ c₀₁₃.hom.app K) (K : C₀) :
    S₂₃.map ((isoWhiskerRight N₀₁.symm S₁₂ ≪≫ isoWhiskerLeft R₀₁ N₁₂.symm ≪≫
        c₀₁₂ ≪≫ N₀₂).hom.app K) ≫
      (isoWhiskerRight N₀₂.symm S₂₃ ≪≫ isoWhiskerLeft R₀₂ N₂₃.symm ≪≫
        c₀₂₃ ≪≫ N₀₃).hom.app K =
    (isoWhiskerRight N₁₂.symm S₂₃ ≪≫ isoWhiskerLeft R₁₂ N₂₃.symm ≪≫
        c₁₂₃ ≪≫ N₁₃).hom.app (S₀₁.obj K) ≫
      (isoWhiskerRight N₀₁.symm S₁₃ ≪≫ isoWhiskerLeft R₀₁ N₁₃.symm ≪≫
        c₀₁₃ ≪≫ N₀₃).hom.app K := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Category.assoc]
  rw [← S₂₃.map_comp_assoc (N₀₂.hom.app K), Iso.hom_inv_id_app, S₂₃.map_id,
    Category.id_comp, NatTrans.naturality_assoc, reassoc_of% (h K),
    ← N₁₃.hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    ← c₁₂₃.hom.naturality_assoc, Functor.comp_map, ← N₂₃.inv.naturality_assoc,
    ← S₂₃.map_comp_assoc (N₁₂.inv.app (S₀₁.obj K)), ← N₁₂.inv.naturality,
    S₂₃.map_comp_assoc]
  rfl

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme
section AmbientAssoc

/-- The adjunction normalization of scalar extensions is
`Adjunction.leftAdjointCompIso` evaluated at an object.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcReductionNormalization_hom_eq {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ)
    (M : DerivedCategory (pbcModules T R)) :
    (pbcReductionNormalization φ ψ χ h M).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
        (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
        (pbcDerivedRestrictComp φ ψ χ h)).hom.app M := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [asIso_hom, Adjunction.leftAdjointCompIso_hom_app,
    Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]

/-- Adjunction normalizations of scalar extensions satisfy associativity.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: the ordinary restriction comparisons are associative on sections; exact
derivation and the adjoint-composition associativity transport this. -/
theorem pbcReductionNormalization_assoc {T : Scheme.{u}}
    {R S B D : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ D)
    (ab : R ⟶ B) (bc : S ⟶ D) (abc : R ⟶ D)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : a ≫ bc = abc) (hab_c : ab ≫ c = abc)
    (M : DerivedCategory (pbcModules T R)) :
    (pbcDerivedExtend c).map ((pbcReductionNormalization a b ab hab M).hom) ≫
        (pbcReductionNormalization ab c abc hab_c M).hom =
      (pbcReductionNormalization b c bc hbc ((pbcDerivedExtend a).obj M)).hom ≫
        (pbcReductionNormalization a bc abc habc M).hom := by
  let eab := pbcRestrictComp a b ab hab
  let ebc := pbcRestrictComp b c bc hbc
  let eabc := pbcRestrictComp a bc abc habc
  let eab_c := pbcRestrictComp ab c abc hab_c
  have he : Functor.isoWhiskerLeft (pbcRestrict c) eab ≪≫ eab_c =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ebc (pbcRestrict a) ≪≫ eabc := by
    apply Iso.ext
    ext M U x
    change (eab_c.hom.app M).val.app U ((eab.hom.app ((pbcRestrict c).obj M)).val.app U x) =
      (eabc.hom.app M).val.app U ((ebc.hom.app M).val.app U x)
    erw [(pbcRestrictComp_exists a b ab hab).exists.choose_spec,
      (pbcRestrictComp_exists ab c abc hab_c).exists.choose_spec,
      (pbcRestrictComp_exists b c bc hbc).exists.choose_spec,
      (pbcRestrictComp_exists a bc abc habc).exists.choose_spec]
  have hd := SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    (pbcRestrict a) (pbcRestrict b) (pbcRestrict c)
    (pbcRestrict ab) (pbcRestrict bc) (pbcRestrict abc) eab ebc eabc eab_c he
  have hh := Adjunction.leftAdjointCompIso_assoc
    (pbcDerivedScalarAdjunction a) (pbcDerivedScalarAdjunction b)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ab)
    (pbcDerivedScalarAdjunction bc) (pbcDerivedScalarAdjunction abc)
    (pbcDerivedRestrictComp a b ab hab) (pbcDerivedRestrictComp b c bc hbc)
    (pbcDerivedRestrictComp a bc abc habc) (pbcDerivedRestrictComp ab c abc hab_c) hd
  have hx := congrArg (fun e ↦ e.hom.app M) hh
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at hx
  simpa only [pbcReductionNormalization_hom_eq] using hx.symm

/-- Restriction along an identity followed by another restriction is the whiskered
identity comparison, when both are the identity on sections. -/
theorem pbcRestrictComp_id_left {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : R ⟶ S) (h : 𝟙 R ≫ ψ = ψ)
    (e : pbcRestrict (𝟙 R) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp (𝟙 R) ψ ψ h = isoWhiskerLeft (pbcRestrict ψ) e ≪≫ rightUnitor _ := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp (𝟙 R) ψ ψ h).hom.app M).val.app U x =
    (e.hom.app ((pbcRestrict ψ).obj M)).val.app U x
  erw [he]
  exact (pbcRestrictComp_exists (𝟙 R) ψ ψ h).exists.choose_spec M U x

/-- A restriction followed by restriction along an identity is the whiskered identity
comparison, when both are the identity on sections. -/
theorem pbcRestrictComp_id_right {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) (h : φ ≫ 𝟙 S = φ)
    (e : pbcRestrict (𝟙 S) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules T S) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp φ (𝟙 S) φ h = isoWhiskerRight e (pbcRestrict φ) ≪≫ leftUnitor _ := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp φ (𝟙 S) φ h).hom.app M).val.app U x =
    ((pbcRestrict φ).map (e.hom.app M)).val.app U x
  erw [he]
  exact (pbcRestrictComp_exists φ (𝟙 S) φ h).exists.choose_spec M U x

/-- Derived version of `pbcRestrictComp_id_left`. -/
theorem pbcDerivedRestrictComp_id_left {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (ψ : R ⟶ S) (h : 𝟙 R ≫ ψ = ψ)
    (e : pbcRestrict (𝟙 R) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules T R) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcDerivedRestrictComp (𝟙 R) ψ ψ h = isoWhiskerLeft (pbcDerivedRestrict ψ)
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _) ≪≫
        rightUnitor _ := by
  apply Iso.ext
  unfold pbcDerivedRestrictComp pbcDerivedRestrict
  rw [pbcRestrictComp_id_left ψ h e he, Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp,
    Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft (pbcRestrict ψ) e),
    reassoc_of% (Functor.mapDerivedCategoryCompIso_comp_id (pbcRestrict ψ))]
  congr 1
  exact Functor.mapDerivedCategoryNatIso_refl

/-- Derived version of `pbcRestrictComp_id_right`. -/
theorem pbcDerivedRestrictComp_id_right {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S) (h : φ ≫ 𝟙 S = φ)
    (e : pbcRestrict (𝟙 S) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules T S) (U : T.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcDerivedRestrictComp φ (𝟙 S) φ h = isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)
        (pbcDerivedRestrict φ) ≪≫ leftUnitor _ := by
  apply Iso.ext
  unfold pbcDerivedRestrictComp pbcDerivedRestrict
  rw [pbcRestrictComp_id_right φ h e he, Iso.trans_hom, Iso.symm_hom, Iso.inv_comp_eq,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.whiskerRight_comp,
    Category.assoc]
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight e (pbcRestrict φ)),
    reassoc_of% (Functor.mapDerivedCategoryCompIso_id_comp (pbcRestrict φ))]
  congr 1
  exact Functor.mapDerivedCategoryNatIso_refl

variable (l : ℕ) [Fact l.Prime]
variable (E F G H : Type u) [Field E] [Field F] [Field G] [Field H]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
variable [Algebra (Padic l) H]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G] [FiniteDimensional (Padic l) H]

/-- The ambient balancing comparisons satisfy the pentagon (associativity) law.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcAmbientScalarComp_assoc (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (T : Scheme.{u}) (M : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcEmbeddingAmbientTensor l G H k T).map
        ((pbcAmbientScalarComp l E F G i j T).hom.app M) ≫
      (pbcAmbientScalarComp l E G H (j.comp i) k T).hom.app M =
    (pbcAmbientScalarComp l F G H j k T).hom.app
        ((pbcEmbeddingAmbientTensor l E F i T).obj M) ≫
      (pbcAmbientScalarComp l E F H i (k.comp j) T).hom.app M := by
  unfold pbcAmbientScalarComp
  simp only [NatIso.ofComponents_hom_app]
  exact pbcReductionNormalization_assoc _ _ _ _ _ _ _ _ _ _ M

end AmbientAssoc

section RationalAssoc
attribute [-instance] ULift.module

variable (l : ℕ) [Fact l.Prime]
variable (E F G H : Type u) [Field E] [Field F] [Field G] [Field H]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G]
variable [Algebra (Padic l) H]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G] [FiniteDimensional (Padic l) H]
variable (T : Scheme.{u}) [IsNoetherian T] (hDim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational scalar extension sends a localized integral morphism to the localization
of its integral scalar extension.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcRationalScalarExtension_map_rationalization (i : E →ₐ[Padic l] F)
    {K L : PbcIntegralCategory l E T hDim hInv} (g : K ⟶ L) :
    (pbcRationalScalarExtension l E F i T hDim hInv).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map g) =
      (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T hDim hInv).map g) := by
  change pbcRationalScalarHom l E F i T hDim hInv K L (1 ⊗ₜ[PbcIntegralRing l E] g) =
    (1 : Localization.Away (pbcUniformizer l F)) ⊗ₜ[PbcIntegralRing l F] _
  rw [pbcRationalScalarHom_tmul]
  simp only [map_one]

/-- The rational balancing comparisons satisfy the pentagon (associativity) law.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcRationalScalarComp_assoc (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l G H k T hDim hInv).map
        ((pbcRationalScalarComp l E F G i j T hDim hInv).hom.app K) ≫
      (pbcRationalScalarComp l E G H (j.comp i) k T hDim hInv).hom.app K =
    (pbcRationalScalarComp l F G H j k T hDim hInv).hom.app
        ((pbcRationalScalarExtension l E F i T hDim hInv).obj K) ≫
      (pbcRationalScalarComp l E F H i (k.comp j) T hDim hInv).hom.app K := by
  unfold pbcRationalScalarComp
  simp only [NatIso.ofComponents_hom_app]
  unfold pbcRationalScalarCompComponent
  simp only [Functor.mapIso_hom]
  erw [pbcRationalScalarExtension_map_rationalization]
  refine ((Functor.map_comp _ _ _).symm.trans ?_).trans (Functor.map_comp _ _ _)
  congr 1
  apply ObjectProperty.hom_ext
  exact pbcAmbientScalarComp_assoc l E F G H i j k T K.obj.obj

/-- Rational balancing associativity, with the composite embeddings named and the
target identified by `eqToIso`.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcRationalScalarComp_eqToIso_assoc (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (k : G →ₐ[Padic l] H) (ij : E →ₐ[Padic l] G) (jk : F →ₐ[Padic l] H)
    (ijk : E →ₐ[Padic l] H) (hij : j.comp i = ij) (hjk : k.comp j = jk)
    (hij_k : k.comp ij = ijk) (hi_jk : jk.comp i = ijk)
    (K : PbcRationalDerivedCategory l E T hDim hInv) :
    (pbcRationalScalarExtension l G H k T hDim hInv).map
        ((pbcRationalScalarComp l E F G i j T hDim hInv ≪≫ eqToIso (congrArg
          (fun a ↦ pbcRationalScalarExtension l E G a T hDim hInv) hij)).hom.app K) ≫
      (pbcRationalScalarComp l E G H ij k T hDim hInv ≪≫ eqToIso (congrArg
          (fun a ↦ pbcRationalScalarExtension l E H a T hDim hInv) hij_k)).hom.app K =
    (pbcRationalScalarComp l F G H j k T hDim hInv ≪≫ eqToIso (congrArg
          (fun a ↦ pbcRationalScalarExtension l F H a T hDim hInv) hjk)).hom.app
        ((pbcRationalScalarExtension l E F i T hDim hInv).obj K) ≫
      (pbcRationalScalarComp l E F H i jk T hDim hInv ≪≫ eqToIso (congrArg
          (fun a ↦ pbcRationalScalarExtension l E H a T hDim hInv) hi_jk)).hom.app K := by
  subst hij hjk hij_k
  have e : (pbcRationalScalarComp l E F H i (k.comp j) T hDim hInv ≪≫ eqToIso (congrArg
      (fun a ↦ pbcRationalScalarExtension l E H a T hDim hInv) hi_jk)).hom.app K =
      (pbcRationalScalarComp l E F H i (k.comp j) T hDim hInv).hom.app K :=
    Category.comp_id _
  rw [e]
  simp only [eqToIso_refl, Iso.trans_refl]
  exact pbcRationalScalarComp_assoc l E F G H T hDim hInv i j k K

end RationalAssoc

section NestedFields
attribute [local irreducible] pbcRationalScalarHom
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual finite subfields, in a common ambient field; no algebraic closure
hypothesis is needed for this finite tower. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcCoefficientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalDerivedCategory l E.val T dim.out inv.out

/-- A nested finite subfield inclusion, with its actual algebra homomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcSubfieldInclusion {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    E.val →ₐ[Padic l] F.val := IntermediateField.inclusion h

/-- Identity inclusions are the actual algebra identity.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps fix every element of the subfield. -/
theorem pbcSubfieldInclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcSubfieldInclusion l Ω (le_refl E) = AlgHom.id (Padic l) E.val := by
  rfl

/-- Actual inclusions compose as direct inclusions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps send each subfield element to its same ambient scalar. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  rfl

/-- The actual rational tensor before literal identity normalization.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcStageRaw {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F :=
  pbcRationalScalarExtension l E.val F.val (pbcSubfieldInclusion l Ω h) T dim.out inv.out

/-- Equal coefficient fields use the literal identity functor.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcStageTransition {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F := by
  classical
  exact if e : E = F then e ▸ 𝟭 (pbcCoefficientStage l Ω T E)
    else pbcStageRaw l Ω T h

/-- The stage transition along a reflexive inclusion is the literal identity functor.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcStageTransition_refl (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageTransition l Ω T (le_refl E) = 𝟭 _ := by
  unfold pbcStageTransition
  rw [dif_pos rfl]

/-- Normalization uses precisely the ordinary tensor multiplication unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageNormalization {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcStageRaw l Ω T h ≅ pbcStageTransition l Ω T h := by
  classical
  by_cases e : E = F
  · subst F
    exact eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val E.val i T dim.out inv.out)
      (pbcSubfieldInclusion_id l Ω E)) ≪≫
        pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
          eqToIso (by unfold pbcStageTransition; rw [dif_pos rfl])
  · exact eqToIso (by simp only [pbcStageTransition, dif_neg e])

/-- Balancing, conjugated by the specified tensor units, is the chosen associator.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageAssociator {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    pbcStageTransition l Ω T h ⋙ pbcStageTransition l Ω T h' ≅
      pbcStageTransition l Ω T (h.trans h') :=
  isoWhiskerRight (pbcStageNormalization l Ω T h).symm _ ≪≫
    isoWhiskerLeft _ (pbcStageNormalization l Ω T h').symm ≪≫
    pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
    eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h')) ≪≫
    pbcStageNormalization l Ω T (h.trans h')

/-- The normalized stage associators satisfy the four-field pentagon.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcStageAssociator_assoc {E F G H : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H) (K : pbcCoefficientStage l Ω T E) :
    (pbcStageTransition l Ω T h'').map ((pbcStageAssociator l Ω T h h').hom.app K) ≫
        (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
      (pbcStageAssociator l Ω T h' h'').hom.app ((pbcStageTransition l Ω T h).obj K) ≫
        (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K := by
  unfold pbcStageAssociator
  have := Functor.conjugateComp_assoc (pbcStageNormalization l Ω T h)
    (pbcStageNormalization l Ω T h') (pbcStageNormalization l Ω T h'')
    (pbcStageNormalization l Ω T (h.trans h')) (pbcStageNormalization l Ω T (h'.trans h''))
    (pbcStageNormalization l Ω T (h.trans (h'.trans h'')))
    (pbcRationalScalarComp l E.val F.val G.val
        (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
      eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
        (pbcSubfieldInclusion_comp l Ω h h')))
    (pbcRationalScalarComp l E.val G.val H.val
        (pbcSubfieldInclusion l Ω (h.trans h')) (pbcSubfieldInclusion l Ω h'') T dim.out
          inv.out ≪≫
      eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val H.val i T dim.out inv.out)
        (pbcSubfieldInclusion_comp l Ω (h.trans h') h'')))
    (pbcRationalScalarComp l F.val G.val H.val
        (pbcSubfieldInclusion l Ω h') (pbcSubfieldInclusion l Ω h'') T dim.out inv.out ≪≫
      eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l F.val H.val i T dim.out inv.out)
        (pbcSubfieldInclusion_comp l Ω h' h'')))
    (pbcRationalScalarComp l E.val F.val H.val
        (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω (h'.trans h'')) T dim.out
          inv.out ≪≫
      eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val H.val i T dim.out inv.out)
        (pbcSubfieldInclusion_comp l Ω h (h'.trans h''))))
    (pbcRationalScalarComp_eqToIso_assoc l E.val F.val G.val H.val T dim.out inv.out _ _ _
      _ _ _ (pbcSubfieldInclusion_comp l Ω h h') (pbcSubfieldInclusion_comp l Ω h' h'')
      (pbcSubfieldInclusion_comp l Ω (h.trans h') h'')
      (pbcSubfieldInclusion_comp l Ω h (h'.trans h''))) K
  simpa only [Iso.trans_assoc] using this

/-- Normalized tensor balancing satisfies both units and the four-field pentagon.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: on a K-flat complex both paths send the three nested scalar factors to
their product, with the same remaining tensor factor. Associativity gives equality
before localization. Multiplication by one gives each unit equation. The two
localizations preserve these equations, including coincident adjacent fields. -/
theorem pbcStageAssociator_laws :
    (∀ {E F G H : Padic.FiniteCoefficientFields l Ω}
      (h : E ≤ F) (h' : F ≤ G) (h'' : G ≤ H)
      (K : pbcCoefficientStage l Ω T E),
      (pbcStageTransition l Ω T h'').map
          ((pbcStageAssociator l Ω T h h').hom.app K) ≫
        (pbcStageAssociator l Ω T (h.trans h') h'').hom.app K =
      (pbcStageAssociator l Ω T h' h'').hom.app
          ((pbcStageTransition l Ω T h).obj K) ≫
        (pbcStageAssociator l Ω T h (h'.trans h'')).hom.app K) ∧
    (∀ E : Padic.FiniteCoefficientFields l Ω,
      pbcStageTransition l Ω T (le_refl E) = 𝟭 _) ∧
    (∀ {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F),
      HEq (pbcStageAssociator l Ω T (le_refl E) h)
        (Functor.leftUnitor (pbcStageTransition l Ω T h)) ∧
      HEq (pbcStageAssociator l Ω T h (le_refl F))
        (Functor.rightUnitor (pbcStageTransition l Ω T h))) := by
  sorry

end NestedFields
end AlgebraicGeometry.Scheme
