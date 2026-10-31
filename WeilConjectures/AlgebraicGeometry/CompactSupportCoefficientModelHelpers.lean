/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.FiniteFreeCompletedScalarComparison
import all WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.AlgebraicGeometry.IntegralScalarExtensionWellDefined
import WeilConjectures.NumberTheory.Padics.LocalFieldIntegralBasis
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Coefficient-model balancing and proof helpers

Source: Bhatt--Scholze, Definition 6.7.6 and Lemmas 6.7.7, 6.8.2(1);
Weil blueprint, purity transport, coefficient extension step
(blueprint: lem-pur-compact-support-coefficient-models).

The proved balancing comparison and its private helpers are split out to keep
each consumer compile below 60 seconds.
The arithmetic basis is fixed before passing to quotients. The scalar comparisons
are the published normalized comparisons, and the arbitrary ramified quotient is
handled by derived tensor balancing rather than a flatness assumption.
The native associator and unit clause is not restated: it is the proved
`RingedDerivedNative.associator_square`, `leftUnitor_square` and `rightUnitor_square`
of the cited node lem-sf-ringed-derived-native-tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] WeilConjectures.completedScalarComparison
  WeilConjectures.completedScalarChainComparison
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.mapDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped BigOperators
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

private theorem coefficientExtensionTensor_naturality
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    [HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1}]
    [(ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (φ : R ⟶ S) {M N : pbcModules W R} (f : M ⟶ N)
    (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    ((pbcExtend φ).map f).val.app U (pbcTensorSection φ M U s x) =
      pbcTensorSection φ N U s (f.val.app U x) := by
  exact witnessTensor_naturality φ (pbcExtend φ)
    (pbcExtensionExistence φ).choose_spec.choose
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose f U s x


private theorem coefficientIntegralBasis :
    let := i.toAlgebra
    let := (integralScalarIntegerInclusion l E F i).toAlgebra
    Nonempty (Module.Basis (Fin (Module.finrank E F))
      (Padic.coefficientExtensionIntegers l E) (Padic.coefficientExtensionIntegers l F)) := by
  classical
  let := i.toAlgebra
  let := (integralScalarIntegerInclusion l E F i).toAlgebra
  let A := Padic.coefficientExtensionIntegers l E
  let B := Padic.coefficientExtensionIntegers l F
  have : FiniteDimensional E F := Module.Finite.right ℚ_[l] E F
  obtain ⟨b, hb, hex⟩ := Padic.exists_integral_basis l E F
    (integralScalar_absoluteValue l E F i)
  let v : Fin (Module.finrank E F) → B := fun j ↦ ⟨b j, hb j⟩
  let f : (Fin (Module.finrank E F) → A) →ₗ[A] B :=
    ∑ j, (LinearMap.proj j).smulRight (v j)
  have hf (c : Fin (Module.finrank E F) → A) :
      (f c : F) = ∑ j, i (c j) * b j := by
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
    change B.subtype (∑ j, c j • v j) = _
    rw [map_sum]
    rfl
  have hbije : Function.Bijective f := by
    constructor
    · intro c c' h
      obtain ⟨a, ha, huniq⟩ := hex (f c) (f c).property
      have hc : (fun j ↦ (c j : E)) = a := huniq _
        ⟨fun j ↦ (c j).property, hf c⟩
      have hc' : (fun j ↦ (c' j : E)) = a := huniq _
        ⟨fun j ↦ (c' j).property, (congrArg (fun z : B ↦ (z : F)) h).trans (hf c')⟩
      funext j
      apply Subtype.ext
      exact congrFun (hc.trans hc'.symm) j
    · intro x
      obtain ⟨a, ha, _⟩ := hex x x.property
      let c : Fin (Module.finrank E F) → A := fun j ↦ ⟨a j, ha.1 j⟩
      refine ⟨c, Subtype.ext ?_⟩
      exact (hf c).trans ha.2.symm
  exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective f hbije).symm⟩

private theorem coefficientQuotientBasis
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (d : ℕ) (b : Module.Basis (Fin d) A B) (I : Ideal A) (K : Ideal B)
    (hK : K = I.map (algebraMap A B)) (h : I ≤ K.comap (algebraMap A B)) :
    letI := Ideal.Quotient.algebraQuotientOfLEComap h
    ∃ c : Module.Basis (Fin d) (A ⧸ I) (B ⧸ K),
      ∀ j : Fin d, c j = Ideal.Quotient.mk K (b j) := by
  subst K
  let c := (b.baseChange (A ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.toLinearEquiv
  refine ⟨c, ?_⟩
  intro j
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).injective
  simp [c]


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionIdeal Padic.coefficientExtensionUniformizer
open CategoryTheory.MonoidalCategory

set_option backward.isDefEq.respectTransparency false in
private abbrev coefficientSectionModule
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M : pbcModules W R) (V : W.ProEtᵒᵖ) : Module (R.obj.obj V) (M.val.obj V) :=
  ModuleCat.isModule (M.val.obj V)

attribute [local instance] coefficientSectionModule

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientTensor_hom_ext
    (W : Scheme.{u}) (R : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (M N H : pbcModules W R)
    (v w : ((proEtaleOrdinaryTensor W R).obj M).obj N ⟶ H)
    (h : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U) (y : N.val.obj U),
      v.val.app U (proEtaleTensorPair W R M N U x y) =
        w.val.app U (proEtaleTensorPair W R M N U x y)) : v = w := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv).mp
  apply (adj.homEquiv _ H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  ext t
  change v.val.app U ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t)) =
    w.val.app U ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      M N).inv.val.app U
      ((adj.unit.app (M.val ⊗ N.val)).app U t))
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => exact h U x y
  | add t s ht hs => simp only [map_add, ht, hs]

private theorem tensorCancellationUnique
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules W R) (N L : pbcModules W S)
    (t : ∀ (U : W.ProEtᵒᵖ), S.obj.obj U → M.val.obj U → L.val.obj U)
    (β : ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N) ≅
      (pbcRestrict φ).obj (((proEtaleOrdinaryTensor W S).obj L).obj N))
    (hβsec : ∀ (U : W.ProEtᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) (z : N.val.obj U),
      β.inv.val.app U (proEtaleTensorPair W S L N U (t U s x) z) =
        proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z)) :
    ∃! β' : (pbcRestrict φ).obj (((proEtaleOrdinaryTensor W S).obj L).obj N) ≅
      ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N),
      ∀ (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) (z : N.val.obj U),
        β'.hom.val.app U (proEtaleTensorPair W S L N U (t U s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z) := by
  refine ⟨β.symm, ?_, ?_⟩
  · intro U s x z
    exact hβsec U x s z
  · intro β' hβ'
    apply Iso.ext
    apply (cancel_epi β.hom).mp
    simp only [Iso.symm_hom, Iso.hom_inv_id]
    apply coefficientTensor_hom_ext W _ M ((pbcRestrict φ).obj N)
    intro U x z
    let zN : N.val.obj U := z
    have hs := hβsec U x 1 zN
    have hz : (1 : S.obj.obj U) • zN = zN := by
      exact (ModuleCat.isModule (N.val.obj U)).one_smul zN
    rw [hz] at hs
    have hi := congrArg (β.hom.val.app U) hs
    have hid := congrArg (fun f ↦ f.val.app U
      (proEtaleTensorPair W _ L N U
        (t U 1 x) z)) β.inv_hom_id
    have hi' : β.hom.val.app U
        (proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z) =
      proEtaleTensorPair W _ L N U
        (t U 1 x) z := by
        change _ = _ at hid
        exact hi.symm.trans hid
    change β'.hom.val.app U (β.hom.val.app U
      (proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z)) = _
    rw [hi']
    change β'.hom.val.app U
      (proEtaleTensorPair W _ L N U
        (t U 1 x) z) =
      proEtaleTensorPair W _ M ((pbcRestrict φ).obj N) U x z
    simpa only [hz] using hβ' U 1 x zN

/-- The local tensor formula fixes the natural cancellation comparison uniquely.
Source: Stacks 03EK, 06YY; Bhatt--Scholze 6.8.2(1), coefficient-model argument Step 7.
(blueprint: lem-pur-compact-support-coefficient-balancing-natural-iso).

Proof: specialize the existing ordinary tensor-cancellation isomorphism to the
recorded extension functor, using its object and map formulas. Its inverse sends
`(s tensor x) tensor z` to `x tensor sz`. The cancellation comparison is natural
in both inputs; with the second input fixed, conjugating its naturality square
by its inverse builds the asserted natural isomorphism. To prove uniqueness,
precompose each component with the forward cancellation map. Local tensors in
the source generate after sheafification. On such a generator, use s = 1 in the
normalization to identify both maps. Componentwise equality and natural
transformation extensionality identify the natural isomorphisms. No flatness
assumption enters this ordinary tensor argument. -/
theorem compactSupportCoefficientModels_balancing_existsUnique
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) :
    ∃! α : pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N),
      ∀ (M : pbcModules W R) (V : W.ProEtᵒᵖ) (s : S.obj.obj V)
        (x : M.val.obj V) (z : N.val.obj V),
        (α.hom.app M).val.app V
            (proEtaleTensorPair W S ((pbcExtend φ).obj M) N V
              (pbcTensorSection φ M V s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) V x
            (@SMul.smul _ _ (N.val.obj V).isModule.toSMul s z) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hobj : ∀ M : pbcModules W R,
      (pbcExtend φ).obj M = SheafOfModules.changeOfRings φ M :=
    (pbcExtensionExistence φ).choose_spec.choose
  have hmap : ∀ {M M' : pbcModules W R} (f : M ⟶ M'),
      (pbcExtend φ).map f = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj M').symm :=
    (pbcExtensionExistence φ).choose_spec.choose_spec.choose
  obtain ⟨b, hb, hbsec⟩ := CategoryTheory.ordinaryTensorCancellation.{u + 1, u, u + 1}
    φ (pbcExtend φ) hobj hmap
  let α : pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N) :=
    NatIso.ofComponents (fun M ↦ (b M N).symm) (by
      intro M M' f
      have h := hb f (𝟙 N)
      rw [(siteTensorRestriction φ).map_id, tensorHom_id, tensorHom_id] at h
      change ((proEtaleOrdinaryTensor W R).map f).app ((pbcRestrict φ).obj N) ≫
        (b M' N).hom = (b M N).hom ≫
          (pbcRestrict φ).map
            (((proEtaleOrdinaryTensor W S).map ((pbcExtend φ).map f)).app N) at h
      change (pbcRestrict φ).map
        (((proEtaleOrdinaryTensor W S).map ((pbcExtend φ).map f)).app N) ≫ (b M' N).inv =
          (b M N).inv ≫ ((proEtaleOrdinaryTensor W R).map f).app ((pbcRestrict φ).obj N)
      apply (cancel_epi (b M N).hom).mp
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
        Category.comp_id] using congrArg (fun k ↦ k ≫ (b M' N).inv) h.symm)
  refine ⟨α, ?_, ?_⟩
  · intro M V s x z
    exact hbsec M N V x s z
  · intro α' hα'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    have hu := tensorCancellationUnique W φ M N ((pbcExtend φ).obj M)
      (pbcTensorSection φ M) (b M N) (hbsec M N)
    have hc : α'.app M = α.app M := by
      apply hu.unique
      · exact hα' M
      · intro V s x z
        exact hbsec M N V x s z
    exact congrArg Iso.hom hc

/-- The natural comparison is fixed by its unique local tensor formula. -/
@[irreducible] private def coefficientBalancingNaturalIso
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) :
    pbcExtend φ ⋙ (proEtaleOrdinaryTensor W S).flip.obj N ⋙ pbcRestrict φ ≅
      (proEtaleOrdinaryTensor W R).flip.obj ((pbcRestrict φ).obj N) :=
  (compactSupportCoefficientModels_balancing_existsUnique W φ N).exists.choose

private theorem coefficientBalancingNaturalIso_tmul
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) (M : pbcModules W R) (V : W.ProEtᵒᵖ)
    (s : S.obj.obj V) (x : M.val.obj V) (z : N.val.obj V) :
    ((coefficientBalancingNaturalIso W φ N).hom.app M).val.app V
        (proEtaleTensorPair W S ((pbcExtend φ).obj M) N V
          (pbcTensorSection φ M V s x) z) =
      proEtaleTensorPair W R M ((pbcRestrict φ).obj N) V x (s • z) := by
  unfold coefficientBalancingNaturalIso
  exact (compactSupportCoefficientModels_balancing_existsUnique W φ N).exists.choose_spec M V s x z

private theorem coefficientModuleBalancing
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (M : pbcModules W R) (N : pbcModules W S) :
    ∃! β : (pbcRestrict φ).obj
        (((proEtaleOrdinaryTensor W S).obj ((pbcExtend φ).obj M)).obj N) ≅
      ((proEtaleOrdinaryTensor W R).obj M).obj ((pbcRestrict φ).obj N),
      ∀ (U : W.ProEtᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) (z : N.val.obj U),
        β.hom.val.app U
          (proEtaleTensorPair W S ((pbcExtend φ).obj M) N U
            (pbcTensorSection φ M U s x) z) =
          proEtaleTensorPair W R M ((pbcRestrict φ).obj N) U x (s • z) := by
  let : HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} W
  let : (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} W
  let : EssentiallySmall.{u + 1} W.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  exact tensorCancellationUnique W φ M N ((pbcExtend φ).obj M)
    (pbcTensorSection φ M) ((coefficientBalancingNaturalIso W φ N).app M).symm
    (by
      intro V x s z
      exact coefficientBalancingNaturalIso_tmul W φ N M V s x z)


private theorem coefficientBalancingNaturalIso_app
    (W : Scheme.{u}) {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (N : pbcModules W S) (M : pbcModules W R) :
    (coefficientBalancingNaturalIso W φ N).app M =
      (coefficientModuleBalancing W φ M N).exists.choose := by
  have h := coefficientModuleBalancing W φ M N
  apply h.unique
  · intro V s x z
    exact coefficientBalancingNaturalIso_tmul W φ N M V s x z
  · exact h.exists.choose_spec

private theorem coefficientLocalizationUnique
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    (Q : CochainComplex C ℤ ⥤ D) {X Y H : CochainComplex C ℤ} {Z : D}
    (q : Z ≅ Q.obj X) (a : X ≅ H) (b : Y ≅ H)
    (f : ∀ k : ℤ, X.X k ⟶ H.X k) (hf : ∀ k : ℤ, f k = a.hom.f k) :
    ∃! δ : Z ≅ Q.obj Y, ∃ γ : X ≅ Y,
      δ = q ≪≫ Q.mapIso γ ∧ ∀ k : ℤ, f k = γ.hom.f k ≫ b.hom.f k := by
  let γ := a ≪≫ b.symm
  have h : γ.hom ≫ b.hom = a.hom := by
    change (a.hom ≫ b.inv) ≫ b.hom = a.hom
    rw [Category.assoc, b.inv_hom_id, Category.comp_id]
  have hγ (k : ℤ) : f k = γ.hom.f k ≫ b.hom.f k :=
    (hf k).trans (congrArg (fun t ↦ t.f k) h).symm
  refine ⟨q ≪≫ Q.mapIso γ, ⟨γ, rfl, hγ⟩, ?_⟩
  rintro δ' ⟨γ', rfl, hγ'⟩
  have hγeq : γ' = γ := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro k
    apply (cancel_mono (b.hom.f k)).mp
    exact (hγ' k).symm.trans (hγ k)
  rw [hγeq]


end WeilConjectures
