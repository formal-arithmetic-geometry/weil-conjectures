/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarIdentityUnit
import all WeilConjectures.SmoothPurity.CompletedScalarAssociator.CompletedScalarAssociator
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Ordinary coherence of the completed scalar extensions

Source: Stacks 06YY, 07A4; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
-/

@[expose] public noncomputable section
set_option Elab.async false
attribute [local instance 5000] CategoryTheory.HasSheafify.isRightAdjoint
attribute [local instance 5000] Algebra.toModule
attribute [local irreducible] Padic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
namespace WeilConjectures
namespace CompletedLineTensor

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)
variable (G : Type u) [Field G] [Algebra ℚ_[l] G] [FiniteDimensional ℚ_[l] G]
  (j : F →ₐ[ℚ_[l]] G)

section CounitNaturality

attribute [local semireducible] completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedOrdinaryScalarComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The universal counit of the ordinary derived scalar extension is natural in chain maps.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: it is the component of a natural transformation at the homotopy quotient. -/
theorem completedScalarCounit_naturality
    {P P' : CochainComplex (integralTowerModules l E X) ℤ} (f : P ⟶ P') :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map f) ≫
        completedScalarCounit l E F ι X P' =
      completedScalarCounit l E F ι X P ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map f) := by
  simpa only [completedScalarCounit, completedOrdinaryScalarComplex] using
    homotopyCounit_naturality
      (completedOrdinaryScalarExtension l E F ι X)
      (completedDerivedScalarExtension l E F ι X)
      ((completedScalarChangeData l E F ι X).choose_spec.choose_spec.choose_spec
        |>.choose_spec.2.2.choose_spec.choose) f

end CounitNaturality

attribute [local semireducible] completedOrdinaryScalarComplex

/-- Natural transformations into an ordinary derived scalar extension are determined
after composing with the universal counits at good complexes.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: specialize the corresponding statement for normalized associators to the
identity first transition. -/
theorem completedDerivedScalarExtension_hom_ext
    {H : DerivedCategory (integralTowerModules l E X) ⥤
      DerivedCategory (integralTowerModules l F X)}
    (f g : H ⟶ completedDerivedScalarExtension l E F ι X)
    (h : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      f.app (DerivedCategory.Q.obj P.obj) ≫ completedScalarCounit l E F ι X P.obj =
        g.app (DerivedCategory.Q.obj P.obj) ≫ completedScalarCounit l E F ι X P.obj) :
    f = g :=
  CompletedScalarAssociator.counit_hom_ext l E X E (AlgHom.id ℚ_[l] E) F ι f g h

/-- The inverse of a normalized ordinary associator on a pure tensor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: apply the normalization with inner scalar one and cancel the isomorphism. -/
theorem completedOrdinaryAssociator_inv_tensorSection
    (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G (j.comp ι) X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x)
    (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U) :
    (o.inv.app M).val.app U (completedScalarTensorSection l E G (j.comp ι) X M U t x) =
      completedScalarTensorSection l F G j X _ U t
        (completedScalarTensorSection l E F ι X M U 1 x) := by
  let z := completedScalarTensorSection l F G j X _ U t
    (completedScalarTensorSection l E F ι X M U 1 x)
  have hz : (o.hom.app M).val.app U z =
      completedScalarTensorSection l E G (j.comp ι) X M U t x := by
    rw [ho M U 1 t x, map_one, mul_one]
  calc
    _ = (o.inv.app M).val.app U ((o.hom.app M).val.app U z) :=
      congrArg (fun y ↦ (o.inv.app M).val.app U y) hz.symm
    _ = z := congrArg (fun f ↦ f.val.app U z) (o.hom_inv_id_app M)

/-- The inverse of the identity multiplication sends a section x to 1 tensor x.
Source: Bhatt--Scholze, Definition 3.4.10
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: multiplication sends 1 tensor x to x; cancel the isomorphism. -/
theorem completedScalarIdentityMultiplication_inv_apply
    (P : CochainComplex (integralTowerModules l E X) ℤ) (i : ℤ) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) :
    (((completedScalarIdentityMultiplication l E X).inv.app P).f i).val.app U x =
      completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X (P.X i) U 1 x := by
  let μ := completedScalarIdentityMultiplication l E X
  let z := completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X (P.X i) U 1 x
  have hz : ((μ.hom.app P).f i).val.app U z = x := by
    rw [completedScalarIdentityMultiplication_spec l E X P i U 1 x]
    exact one_smul (((sheafCompose (AlgebraicGeometry.Scheme.ProEt.topology X)
      (forget₂ CommRingCat RingCat)).obj
        (completedIntegralCommRingSheafUnrestricted l E X)).obj.obj U) x
  conv_lhs => rw [← hz]
  exact congrArg (fun f ↦ (f.f i).val.app U z) (μ.hom_inv_id_app P)

/-- A normalized ordinary associator satisfies its counit formula on every complex.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: the normalizations determine the pair uniquely, and the canonical pair
constructed from the composed presentations satisfies the formula on all complexes. -/
theorem completedDerivedAssociator_counit_formula
    (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X)
    (d : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G (j.comp ι) X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x)
    (hd : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P.obj) ≫
          completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
          DerivedCategory.Q.map
            ((scalarAssociatorComplex l E X F ι G j o).hom.app P.obj) =
        d.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E G (j.comp ι) X P.obj)
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P) ≫
        completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
        DerivedCategory.Q.map ((scalarAssociatorComplex l E X F ι G j o).hom.app P) =
      d.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit l E G (j.comp ι) X P := by
  obtain ⟨o₀, d₀, ho₀, hd₀, hu, hv⟩ := CompletedScalarAssociator.exists_normalized l E X F ι G j
  obtain rfl := hu o ho
  obtain rfl := hv d (fun P ↦ (hd P).symm.trans (hd₀ P.obj))
  exact hd₀ P

/-- The ordinary identity unitor satisfies its counit formula on every complex.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: good complexes determine the unitor by localization, and the unitor
constructed on all complexes satisfies the same formula on good complexes. -/
theorem completedDerivedUnitor_counit_formula
    (e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _)
    (he : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      e.hom.app (DerivedCategory.Q.obj P.obj) =
        completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj))
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    e.hom.app (DerivedCategory.Q.obj P) =
      completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P ≫
        DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  obtain ⟨e₀, he₀⟩ := ordinaryUnitOnComplexes_exists l E X
  have : e = e₀ := by
    let Q := integralOperationsGoodLocalization l E X
    let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
      (integralOperationsGoodComplex l E X).ι
    have : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
    apply Iso.ext
    apply (Localization.fullyFaithfulWhiskeringLeft Q W _).map_injective
    apply NatTrans.ext
    funext P
    exact (he P).trans (he₀ P.obj).symm
  rw [this]
  exact he₀ P

/-- A morphism with a left inverse that is also a right inverse of another morphism
equals that morphism. Source: elementary category theory
(blueprint: lem-pur-completed-line-tensor-coherence). -/
private theorem eq_of_comp_eq_id {C : Type*} [Category C] {A B : C} {a b : A ⟶ B}
    {ν : B ⟶ A} (h₁ : ν ≫ a = 𝟙 B) (h₂ : b ≫ ν = 𝟙 A) : a = b := by
  rw [← Category.id_comp a, ← h₂, Category.assoc, h₁, Category.comp_id]


/-- The ordinary associator for an identity first transition is the extension of the
identity multiplication, on every complex.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: precompose with the extension of x ↦ 1 tensor x; both composites fix every
pure tensor s tensor x, so they agree by tensor generation. -/
theorem scalarAssociatorComplex_source_unit
    (o : completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) X ⋙
        completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F (ι.comp (AlgHom.id ℚ_[l] E)) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l E F ι X _ U t
            (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X M U s x)) =
        completedScalarTensorSection l E F (ι.comp (AlgHom.id ℚ_[l] E)) X M U
          (t * (completedCoefficientMap l E F ι X).hom.app U s) x)
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (scalarAssociatorComplex l E X E (AlgHom.id ℚ_[l] E) F ι o).hom.app P =
      (completedOrdinaryScalarComplex l E F ι X).map
        ((completedScalarIdentityMultiplication l E X).hom.app P) := by
  ext i : 1
  let μ := completedScalarIdentityMultiplication l E X
  let T := completedOrdinaryScalarExtension l E F ι X
  have ha : ((scalarAssociatorComplex l E X E (AlgHom.id ℚ_[l] E) F ι o).hom.app P).f i =
      o.hom.app (P.X i) := rfl
  have hb : ((completedOrdinaryScalarComplex l E F ι X).map (μ.hom.app P)).f i =
      T.map ((μ.hom.app P).f i) := rfl
  have h1 : T.map ((μ.inv.app P).f i) ≫ o.hom.app (P.X i) = 𝟙 _ := by
    apply completedScalar_tensor_ext l E F ι X
    intro U s x
    have hn := completedScalarTensorSection_naturality l E F ι X ((μ.inv.app P).f i) U s x
    rw [completedScalarIdentityMultiplication_inv_apply] at hn
    have hc := ho (P.X i) U 1 s x
    rw [map_one, mul_one] at hc
    exact (congrArg ((o.hom.app (P.X i)).val.app U) hn).trans hc
  have h2 : T.map ((μ.hom.app P).f i) ≫ T.map ((μ.inv.app P).f i) = 𝟙 _ := by
    rw [← T.map_comp, ← HomologicalComplex.comp_f, μ.hom_inv_id_app, HomologicalComplex.id_f,
      T.map_id]
  rw [ha, hb]
  exact eq_of_comp_eq_id h1 h2

/-- The ordinary associator for an identity second transition is the identity
multiplication of the extended complex.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: precompose with y ↦ 1 tensor y; the identity coefficient map is the identity,
so both composites fix every pure tensor s tensor x. -/
theorem scalarAssociatorComplex_target_unit
    (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅
      completedOrdinaryScalarExtension l E F ((AlgHom.id ℚ_[l] F).comp ι) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l F F (AlgHom.id ℚ_[l] F) X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E F ((AlgHom.id ℚ_[l] F).comp ι) X M U
          (t * (completedCoefficientMap l F F (AlgHom.id ℚ_[l] F) X).hom.app U s) x)
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (scalarAssociatorComplex l E X F ι F (AlgHom.id ℚ_[l] F) o).hom.app P =
      (completedScalarIdentityMultiplication l F X).hom.app
        ((completedOrdinaryScalarComplex l E F ι X).obj P) := by
  ext i : 1
  let μ := completedScalarIdentityMultiplication l F X
  let P' := (completedOrdinaryScalarComplex l E F ι X).obj P
  have ha : ((scalarAssociatorComplex l E X F ι F (AlgHom.id ℚ_[l] F) o).hom.app P).f i =
      o.hom.app (P.X i) := rfl
  have h1 : (μ.inv.app P').f i ≫ o.hom.app (P.X i) = 𝟙 _ := by
    apply completedScalar_tensor_ext l E F ι X
    intro U s x
    have hn := completedScalarIdentityMultiplication_inv_apply l F X P' i U
      (completedScalarTensorSection l E F ι X (P.X i) U s x)
    have hc := ho (P.X i) U s 1 x
    rw [completedCoefficientMap_id, one_mul] at hc
    exact (congrArg ((o.hom.app (P.X i)).val.app U) hn).trans hc
  have h2 : (μ.hom.app P').f i ≫ (μ.inv.app P').f i = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, μ.hom_inv_id_app, HomologicalComplex.id_f]
  rw [ha]
  exact eq_of_comp_eq_id h1 h2

/-- Normalized ordinary associators satisfy the pentagon on every module.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compare inverses. Both inverse routes send the pure tensor v tensor x to
v tensor (1 tensor (1 tensor x)); pure tensors generate. -/
theorem completedOrdinaryAssociator_pentagon_app
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H)
    (o₁ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X)
    (o₂ : completedOrdinaryScalarExtension l E G (j.comp ι) X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l E H (k.comp (j.comp ι)) X)
    (o₃ : completedOrdinaryScalarExtension l F G j X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l F H (k.comp j) X)
    (o₄ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F H (k.comp j) X ≅
      completedOrdinaryScalarExtension l E H ((k.comp j).comp ι) X)
    (ho₁ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o₁.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G (j.comp ι) X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x)
    (ho₂ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₂.hom.app M).val.app U
          (completedScalarTensorSection l G H k X _ U t
            (completedScalarTensorSection l E G (j.comp ι) X M U s x)) =
        completedScalarTensorSection l E H (k.comp (j.comp ι)) X M U
          (t * (completedCoefficientMap l G H k X).hom.app U s) x)
    (ho₃ : ∀ (M : integralTowerModules l F X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₃.hom.app M).val.app U
          (completedScalarTensorSection l G H k X _ U t
            (completedScalarTensorSection l F G j X M U s x)) =
        completedScalarTensorSection l F H (k.comp j) X M U
          (t * (completedCoefficientMap l G H k X).hom.app U s) x)
    (ho₄ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₄.hom.app M).val.app U
          (completedScalarTensorSection l F H (k.comp j) X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E H ((k.comp j).comp ι) X M U
          (t * (completedCoefficientMap l F H (k.comp j) X).hom.app U s) x)
    (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M) ≫ o₂.hom.app M =
      o₃.hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≫ o₄.hom.app M := by
  let T := completedOrdinaryScalarExtension l G H k X
  have key : (T.mapIso (o₁.app M) ≪≫ o₂.app M).inv =
      (o₃.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≪≫ o₄.app M).inv := by
    apply completedScalar_tensor_ext l E H (k.comp (j.comp ι)) X
    intro U v x
    refine (((congrArg ((T.map (o₁.inv.app M)).val.app U)
      (completedOrdinaryAssociator_inv_tensorSection l E X G (j.comp ι) H k o₂ ho₂ M U v x)).trans
      (completedScalarTensorSection_naturality l G H k X (o₁.inv.app M) U v _)).trans
      (congrArg (completedScalarTensorSection l G H k X _ U v)
        (completedOrdinaryAssociator_inv_tensorSection l E X F ι G j o₁ ho₁ M U 1 x))).trans ?_
    exact ((congrArg ((o₃.inv.app ((completedOrdinaryScalarExtension l E F ι X).obj M)).val.app U)
      (completedOrdinaryAssociator_inv_tensorSection l E X F ι H (k.comp j) o₄ ho₄ M U v x)).trans
      (completedOrdinaryAssociator_inv_tensorSection l F X G j H k o₃ ho₃ _ U v _)).symm
  exact (Iso.inv_eq_inv _ _).mp key

/-- Normalized ordinary associators satisfy the pentagon on every complex.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compare degreewise using `completedOrdinaryAssociator_pentagon_app`. -/
theorem scalarAssociatorComplex_pentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H)
    (o₁ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X)
    (o₂ : completedOrdinaryScalarExtension l E G (j.comp ι) X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l E H (k.comp (j.comp ι)) X)
    (o₃ : completedOrdinaryScalarExtension l F G j X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l F H (k.comp j) X)
    (o₄ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F H (k.comp j) X ≅
      completedOrdinaryScalarExtension l E H ((k.comp j).comp ι) X)
    (h : ∀ M : integralTowerModules l E X,
      (completedOrdinaryScalarExtension l G H k X).map (o₁.hom.app M) ≫ o₂.hom.app M =
        o₃.hom.app ((completedOrdinaryScalarExtension l E F ι X).obj M) ≫ o₄.hom.app M)
    (P : CochainComplex (integralTowerModules l E X) ℤ) :
    (completedOrdinaryScalarComplex l G H k X).map
        ((scalarAssociatorComplex l E X F ι G j o₁).hom.app P) ≫
      (scalarAssociatorComplex l E X G (j.comp ι) H k o₂).hom.app P =
    (scalarAssociatorComplex l F X G j H k o₃).hom.app
        ((completedOrdinaryScalarComplex l E F ι X).obj P) ≫
      (scalarAssociatorComplex l E X F ι H (k.comp j) o₄).hom.app P := by
  ext i : 1
  exact h (P.X i)

/-- The derived associator for an identity first transition is the extension of the
derived identity unitor.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compare after the universal counit at good complexes. The normalizations,
naturality of the counit in chain maps and the complex-level identity agree. -/
theorem completedDerivedAssociator_source_unit
    (o : completedOrdinaryScalarExtension l E E (AlgHom.id ℚ_[l] E) X ⋙
        completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F (ι.comp (AlgHom.id ℚ_[l] E)) X)
    (d : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ⋙
        completedDerivedScalarExtension l E F ι X ≅
      completedDerivedScalarExtension l E F (ι.comp (AlgHom.id ℚ_[l] E)) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l E F ι X _ U t
            (completedScalarTensorSection l E E (AlgHom.id ℚ_[l] E) X M U s x)) =
        completedScalarTensorSection l E F (ι.comp (AlgHom.id ℚ_[l] E)) X M U
          (t * (completedCoefficientMap l E F ι X).hom.app U s) x)
    (hd : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l E F ι X).map
          (completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj) ≫
        completedScalarCounit l E F ι X
          ((completedOrdinaryScalarComplex l E E (AlgHom.id ℚ_[l] E) X).obj P.obj) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X E (AlgHom.id ℚ_[l] E) F ι o).hom.app P.obj) =
      d.hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E F (ι.comp (AlgHom.id ℚ_[l] E)) X P.obj)
    (e : completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) X ≅ 𝟭 _)
    (he : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      e.hom.app (DerivedCategory.Q.obj P.obj) =
        completedScalarCounit l E E (AlgHom.id ℚ_[l] E) X P.obj ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication l E X).hom.app P.obj))
    (K : DerivedCategory (integralTowerModules l E X)) :
    d.hom.app K = (completedDerivedScalarExtension l E F ι X).map (e.hom.app K) := by
  let g := Functor.whiskerRight e.hom (completedDerivedScalarExtension l E F ι X) ≫
    (Functor.leftUnitor (completedDerivedScalarExtension l E F ι X)).hom
  have hg (K : DerivedCategory (integralTowerModules l E X)) :
      g.app K = (completedDerivedScalarExtension l E F ι X).map (e.hom.app K) :=
    Category.comp_id _
  have h : d.hom = g := by
    apply completedDerivedScalarExtension_hom_ext l E X F ι
    intro P
    rw [hg]
    refine (hd P).symm.trans ?_
    rw [he P, Functor.map_comp, Category.assoc]
    exact (congrArg (fun x ↦ _ ≫ _ ≫ DerivedCategory.Q.map x)
      (scalarAssociatorComplex_source_unit l E X F ι o ho P.obj)).trans
      (congrArg (_ ≫ ·) (completedScalarCounit_naturality l E X F ι _).symm)
  rw [h, hg]

/-- The derived associator for an identity second transition is the derived
identity unitor of the extension.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compare after the universal counit at good complexes, using naturality of the
unitor and its counit formula on the (not necessarily good) extended complex. -/
theorem completedDerivedAssociator_target_unit
    (o : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅
      completedOrdinaryScalarExtension l E F ((AlgHom.id ℚ_[l] F).comp ι) X)
    (d : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅
      completedDerivedScalarExtension l E F ((AlgHom.id ℚ_[l] F).comp ι) X)
    (ho : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U) (x : M.val.obj U),
      (o.hom.app M).val.app U
          (completedScalarTensorSection l F F (AlgHom.id ℚ_[l] F) X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E F ((AlgHom.id ℚ_[l] F).comp ι) X M U
          (t * (completedCoefficientMap l F F (AlgHom.id ℚ_[l] F) X).hom.app U s) x)
    (hd : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X).map
          (completedScalarCounit l E F ι X P.obj) ≫
        completedScalarCounit l F F (AlgHom.id ℚ_[l] F) X
          ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
        DerivedCategory.Q.map
          ((scalarAssociatorComplex l E X F ι F (AlgHom.id ℚ_[l] F) o).hom.app P.obj) =
      d.hom.app (DerivedCategory.Q.obj P.obj) ≫
        completedScalarCounit l E F ((AlgHom.id ℚ_[l] F).comp ι) X P.obj)
    (e : completedDerivedScalarExtension l F F (AlgHom.id ℚ_[l] F) X ≅ 𝟭 _)
    (he : ∀ P : (integralOperationsGoodComplex l F X).FullSubcategory,
      e.hom.app (DerivedCategory.Q.obj P.obj) =
        completedScalarCounit l F F (AlgHom.id ℚ_[l] F) X P.obj ≫
          DerivedCategory.Q.map ((completedScalarIdentityMultiplication l F X).hom.app P.obj))
    (K : DerivedCategory (integralTowerModules l E X)) :
    d.hom.app K = e.hom.app ((completedDerivedScalarExtension l E F ι X).obj K) := by
  let g := Functor.whiskerLeft (completedDerivedScalarExtension l E F ι X) e.hom ≫
    (Functor.rightUnitor (completedDerivedScalarExtension l E F ι X)).hom
  have hg (K : DerivedCategory (integralTowerModules l E X)) :
      g.app K = e.hom.app ((completedDerivedScalarExtension l E F ι X).obj K) :=
    Category.comp_id _
  have h : d.hom = g := by
    apply completedDerivedScalarExtension_hom_ext l E X F ι
    intro P
    rw [hg]
    refine (hd P).symm.trans ?_
    have hn := e.hom.naturality (completedScalarCounit l E F ι X P.obj)
    rw [Functor.id_map] at hn
    rw [← hn, completedDerivedUnitor_counit_formula l F X e he]
    exact congrArg (fun x ↦ _ ≫ _ ≫ DerivedCategory.Q.map x)
      (scalarAssociatorComplex_target_unit l E X F ι o ho P.obj)
  rw [h, hg]

/-- Normalized derived associators satisfy the pentagon.
Source: Stacks 06YY, 07A4 (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compare after the universal counit at good complexes. Both routes reduce,
by the counit normalizations (on all complexes for the middle associator), naturality
of the counits and of the associator, to the complex-level pentagon. -/
theorem completedDerivedAssociator_pentagon
    (H : Type u) [Field H] [Algebra ℚ_[l] H] [FiniteDimensional ℚ_[l] H]
    (k : G →ₐ[ℚ_[l]] H)
    (o₁ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F G j X ≅
      completedOrdinaryScalarExtension l E G (j.comp ι) X)
    (o₂ : completedOrdinaryScalarExtension l E G (j.comp ι) X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l E H (k.comp (j.comp ι)) X)
    (o₃ : completedOrdinaryScalarExtension l F G j X ⋙
        completedOrdinaryScalarExtension l G H k X ≅
      completedOrdinaryScalarExtension l F H (k.comp j) X)
    (o₄ : completedOrdinaryScalarExtension l E F ι X ⋙
        completedOrdinaryScalarExtension l F H (k.comp j) X ≅
      completedOrdinaryScalarExtension l E H ((k.comp j).comp ι) X)
    (d₁ : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F G j X ≅
      completedDerivedScalarExtension l E G (j.comp ι) X)
    (d₂ : completedDerivedScalarExtension l E G (j.comp ι) X ⋙
        completedDerivedScalarExtension l G H k X ≅
      completedDerivedScalarExtension l E H (k.comp (j.comp ι)) X)
    (d₃ : completedDerivedScalarExtension l F G j X ⋙
        completedDerivedScalarExtension l G H k X ≅
      completedDerivedScalarExtension l F H (k.comp j) X)
    (d₄ : completedDerivedScalarExtension l E F ι X ⋙
        completedDerivedScalarExtension l F H (k.comp j) X ≅
      completedDerivedScalarExtension l E H ((k.comp j).comp ι) X)
    (ho₁ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U) (x : M.val.obj U),
      (o₁.hom.app M).val.app U
          (completedScalarTensorSection l F G j X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E G (j.comp ι) X M U
          (t * (completedCoefficientMap l F G j X).hom.app U s) x)
    (ho₂ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₂.hom.app M).val.app U
          (completedScalarTensorSection l G H k X _ U t
            (completedScalarTensorSection l E G (j.comp ι) X M U s x)) =
        completedScalarTensorSection l E H (k.comp (j.comp ι)) X M U
          (t * (completedCoefficientMap l G H k X).hom.app U s) x)
    (ho₃ : ∀ (M : integralTowerModules l F X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l G X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₃.hom.app M).val.app U
          (completedScalarTensorSection l G H k X _ U t
            (completedScalarTensorSection l F G j X M U s x)) =
        completedScalarTensorSection l F H (k.comp j) X M U
          (t * (completedCoefficientMap l G H k X).hom.app U s) x)
    (ho₄ : ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (t : (completedIntegralCommRingSheafUnrestricted l H X).obj.obj U) (x : M.val.obj U),
      (o₄.hom.app M).val.app U
          (completedScalarTensorSection l F H (k.comp j) X _ U t
            (completedScalarTensorSection l E F ι X M U s x)) =
        completedScalarTensorSection l E H ((k.comp j).comp ι) X M U
          (t * (completedCoefficientMap l F H (k.comp j) X).hom.app U s) x)
    (hd₁ : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l F G j X).map (completedScalarCounit l E F ι X P.obj) ≫
          completedScalarCounit l F G j X ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
          DerivedCategory.Q.map ((scalarAssociatorComplex l E X F ι G j o₁).hom.app P.obj) =
        d₁.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E G (j.comp ι) X P.obj)
    (hd₂ : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l G H k X).map
          (completedScalarCounit l E G (j.comp ι) X P.obj) ≫
          completedScalarCounit l G H k X
            ((completedOrdinaryScalarComplex l E G (j.comp ι) X).obj P.obj) ≫
          DerivedCategory.Q.map
            ((scalarAssociatorComplex l E X G (j.comp ι) H k o₂).hom.app P.obj) =
        d₂.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E H (k.comp (j.comp ι)) X P.obj)
    (hd₃ : ∀ P : (integralOperationsGoodComplex l F X).FullSubcategory,
      (completedDerivedScalarExtension l G H k X).map (completedScalarCounit l F G j X P.obj) ≫
          completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l F G j X).obj P.obj) ≫
          DerivedCategory.Q.map ((scalarAssociatorComplex l F X G j H k o₃).hom.app P.obj) =
        d₃.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l F H (k.comp j) X P.obj)
    (hd₄ : ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
      (completedDerivedScalarExtension l F H (k.comp j) X).map
          (completedScalarCounit l E F ι X P.obj) ≫
          completedScalarCounit l F H (k.comp j) X
            ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
          DerivedCategory.Q.map
            ((scalarAssociatorComplex l E X F ι H (k.comp j) o₄).hom.app P.obj) =
        d₄.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E H ((k.comp j).comp ι) X P.obj)
    (K : DerivedCategory (integralTowerModules l E X)) :
    (completedDerivedScalarExtension l G H k X).map (d₁.hom.app K) ≫ d₂.hom.app K =
      d₃.hom.app ((completedDerivedScalarExtension l E F ι X).obj K) ≫ d₄.hom.app K := by
  let CEF := completedDerivedScalarExtension l E F ι X
  let CFG := completedDerivedScalarExtension l F G j X
  let CGH := completedDerivedScalarExtension l G H k X
  let f := Functor.whiskerRight d₁.hom CGH ≫ d₂.hom
  let g := Functor.whiskerLeft CEF d₃.hom ≫ d₄.hom
  have hf (K : DerivedCategory (integralTowerModules l E X)) :
      f.app K = CGH.map (d₁.hom.app K) ≫ d₂.hom.app K := rfl
  have hg (K : DerivedCategory (integralTowerModules l E X)) :
      g.app K = d₃.hom.app (CEF.obj K) ≫ d₄.hom.app K := rfl
  have h : f = g := by
    apply completedDerivedScalarExtension_hom_ext l E X H (k.comp (j.comp ι))
    intro P
    have hpent := scalarAssociatorComplex_pentagon l E X F ι G j H k o₁ o₂ o₃ o₄
      (completedOrdinaryAssociator_pentagon_app l E X F ι G j H k o₁ o₂ o₃ o₄ ho₁ ho₂ ho₃ ho₄) P.obj
    have hL : CGH.map (d₁.hom.app (DerivedCategory.Q.obj P.obj)) ≫
        d₂.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E H (k.comp (j.comp ι)) X P.obj =
        CGH.map (CFG.map (completedScalarCounit l E F ι X P.obj)) ≫
          CGH.map (completedScalarCounit l F G j X
            ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) ≫
          completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l F G j X).obj
            ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) ≫
          DerivedCategory.Q.map ((completedOrdinaryScalarComplex l G H k X).map
            ((scalarAssociatorComplex l E X F ι G j o₁).hom.app P.obj) ≫
            (scalarAssociatorComplex l E X G (j.comp ι) H k o₂).hom.app P.obj) := by
      rw [← hd₂ P, ← Functor.map_comp_assoc, ← hd₁ P]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% (completedScalarCounit_naturality l G X H k
        ((scalarAssociatorComplex l E X F ι G j o₁).hom.app P.obj))]
    have hR : d₃.hom.app (CEF.obj (DerivedCategory.Q.obj P.obj)) ≫
        d₄.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedScalarCounit l E H ((k.comp j).comp ι) X P.obj =
        CGH.map (CFG.map (completedScalarCounit l E F ι X P.obj)) ≫
          CGH.map (completedScalarCounit l F G j X
            ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) ≫
          completedScalarCounit l G H k X ((completedOrdinaryScalarComplex l F G j X).obj
            ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) ≫
          DerivedCategory.Q.map ((scalarAssociatorComplex l F X G j H k o₃).hom.app
              ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
            (scalarAssociatorComplex l E X F ι H (k.comp j) o₄).hom.app P.obj) := by
      have hn := d₃.hom.naturality (completedScalarCounit l E F ι X P.obj)
      rw [Functor.comp_map] at hn
      rw [← hd₄ P, ← reassoc_of% hn, ← reassoc_of% (completedDerivedAssociator_counit_formula
        l F X G j H k o₃ d₃ ho₃ hd₃ ((completedOrdinaryScalarComplex l E F ι X).obj P.obj))]
      simp only [Functor.map_comp]
      rfl
    rw [hf, hg]
    exact (Category.assoc _ _ _).trans (hL.trans
      ((congrArg (fun x ↦ _ ≫ _ ≫ _ ≫ DerivedCategory.Q.map x) hpent).trans
        (hR.symm.trans (Category.assoc _ _ _).symm)))
  rw [← hf, ← hg, h]

end CompletedLineTensor
end WeilConjectures
