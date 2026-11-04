/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedLineTensorOrdinaryData
public import WeilConjectures.Algebra.Homology.Signed.SignedLineScalarTensorTower
public import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChangeData
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison

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
universe uC vC w t u
open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace SheafOfModules

section Generic

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Tensoring with an isomorphism in the second factor is an isomorphism.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def siteSheafTensorSecondIso {R : Sheaf J CommRingCat.{w}}
    (M : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    {N N' : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (g : N ≅ N') : (siteSheafTensorRight N).obj M ≅ (siteSheafTensorRight N').obj M where
  hom := siteSheafTensorSecondMap M g.hom
  inv := siteSheafTensorSecondMap M g.inv
  hom_inv_id := by
    apply scalarTensor_hom_ext
    intro U x y
    rw [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, scalarTensor_second_tmul,
      scalarTensor_second_tmul]
    exact congrArg (siteSheafTensorTmul M N U x) (congrArg (fun f ↦ f.val.app U y) g.hom_inv_id)
  inv_hom_id := by
    apply scalarTensor_hom_ext
    intro U x y
    rw [comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, scalarTensor_second_tmul,
      scalarTensor_second_tmul]
    exact congrArg (siteSheafTensorTmul M N' U x) (congrArg (fun f ↦ f.val.app U y) g.inv_hom_id)

/-- Tensor powers of an isomorphism are isomorphisms.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: induction on the exponent, using functoriality in the first factor and
`siteSheafTensorSecondIso` in the second. -/
theorem isIso_scalarTensorPowerMap {R : Sheaf J CommRingCat.{w}}
    {M N : SheafOfModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : M ≅ N) : ∀ n : ℕ, IsIso (scalarTensorPowerMap R f.hom n)
  | 0 => (Iso.refl (scalarTensorPower R M 0)).isIso_hom
  | 1 => f.isIso_hom
  | n + 2 => by
    have h := isIso_scalarTensorPowerMap f (n + 1)
    exact IsIso.comp_isIso'
      ((siteSheafTensorRight M).mapIso (asIso (scalarTensorPowerMap R f.hom (n + 1)))).isIso_hom
      (siteSheafTensorSecondIso (scalarTensorPower R N (n + 1)) f).isIso_hom

end Generic

section Dual

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC w} RingCat.{max uC vC w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC w}]
  [HasWeakSheafify J AddCommGrpCat.{max uC vC w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{max uC vC w}]

/-- Precomposition with an isomorphism, as an isomorphism of internal duals.
Source: Stacks 0GMX (blueprint: lem-pur-completed-line-tensor-coherence). -/
def homObjUnitIsoOfIso {S : Sheaf J CommRingCat.{max uC vC w}}
    {M N : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)}
    (φ : M ≅ N) :
    homObj M (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) ≅
      homObj N (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)) :=
  (((homFunctor S).mapIso φ.op).app
    (unit _)).symm

/-- The scalar extension of the dual of a positive tensor power of a line is the dual of
any identification of the scalar-extended power, uniquely by the evaluation formula.
Source: Stacks 0GMX and 04TT (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: compose the canonical dual comparison, invertible for lines, with precomposition
by the inverse identification. Evaluation cancels the inverse. Uniqueness: after
precomposing with the identification both maps agree on scalar-extension pure sections
evaluated on pure sections, hence agree by `scalarExtensionDual_hom_ext`. -/
theorem existsUnique_scalarExtensionDualIso [HasFiniteLimits C]
    {R S : Sheaf J CommRingCat.{max uC vC w}} (α : R ⟶ S)
    (L : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (hL : ∃ (I : Type uC) (X : I → C), J.CoversTop X ∧
      ∀ i : I, Nonempty (L.over (X i) ≅
        unit (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over (X i))))
    (n : ℕ)
    (Q : SheafOfModules.{max uC vC w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (φ : changeOfRingsOfUniverses α (scalarTensorPower R L (n + 1)) ≅ Q) :
    ∃! ψ : changeOfRingsOfUniverses α (homObj (scalarTensorPower R L (n + 1))
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅
        homObj Q (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)),
      ∀ (U : Cᵒᵖ) (s t : S.obj.obj U)
        (f : (homObj (scalarTensorPower R L (n + 1))
          (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U)
        (x : (scalarTensorPower R L (n + 1)).val.obj U),
        (ψ.hom.val.app U (scalarExtensionSection α _ U s f)).app (op (Over.mk (𝟙 U.unop)))
            (φ.hom.val.app U (scalarExtensionSection α _ U t x)) =
          s * t * α.hom.app U (f.app (op (Over.mk (𝟙 U.unop))) x) := by
  have hD := signedLineDual_isIso.{uC, vC, w} α L hL n
  let D := asIso (scalarExtensionDualMap α (scalarTensorPower R L (n + 1)))
  have key (ψ : changeOfRingsOfUniverses α (homObj (scalarTensorPower R L (n + 1))
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅
        homObj Q (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)))
      (U : Cᵒᵖ) (s t : S.obj.obj U)
      (f : (homObj (scalarTensorPower R L (n + 1))
        (unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).val.obj U)
      (x : (scalarTensorPower R L (n + 1)).val.obj U) :
      ((ψ.hom ≫ (homObjUnitIsoOfIso φ).inv).val.app U (scalarExtensionSection α _ U s f)).app
          (op (Over.mk (𝟙 U.unop))) (scalarExtensionSection α _ U t x) =
        (ψ.hom.val.app U (scalarExtensionSection α _ U s f)).app (op (Over.mk (𝟙 U.unop)))
          (φ.hom.val.app U (scalarExtensionSection α _ U t x)) := rfl
  refine ⟨D ≪≫ homObjUnitIsoOfIso φ, ?_, ?_⟩
  · intro U s t f x
    rw [← key]
    simp only [Iso.trans_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact scalarExtensionDualMap_tmul α _ U s t f x
  · intro ψ hψ
    apply Iso.ext
    rw [Iso.trans_hom, ← Iso.comp_inv_eq]
    apply scalarExtensionDual_hom_ext
    intro U s t f x
    rw [key, hψ]
    exact (scalarExtensionDualMap_tmul α _ U s t f x).symm

end Dual

end SheafOfModules

namespace WeilConjectures
namespace CompletedLineTensor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (ι : E →ₐ[ℚ_[l]] F)

-- Copied from the private `evaluationOverLocallyBijective` in
-- `CompletedLineTensorOrdinaryData`.
/-- Slices of the pro-etale site have locally bijective abelian sheafification.
Source: Stacks 00XP (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem overLocallyBijective (U : X.ProEt) :
    ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := by
  let : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

attribute [local instance 5000] overLocallyBijective

/-- A rank-one locally free module is trivial on a covering family.
Source: Stacks 03DN (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem line_cover {E : Type u} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1] :
    ∃ (I : Type (t + 1)) (V : I → X.ProEt),
      (AlgebraicGeometry.Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (L.over (V i) ≅ SheafOfModules.unit
        ((SheafOfModules.derivedChangeRingIndependentCoefficients
          (AlgebraicGeometry.Scheme.ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X)).over (V i))) := by
  classical
  obtain ⟨I, V, hV, e⟩ :=
    (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free (M := L) (r := 1)).mp
      inferInstance
  exact ⟨I, V, hV, fun i ↦ ⟨(e i).some ≪≫ SheafOfModules.freeUniqueIso _⟩⟩

/-- The positive signed-power comparison: binary tensor powers followed by powers of b.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def positiveLine (L : integralTowerModules l E X)
    (N : integralTowerModules l F X)
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) (n : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L (Int.ofNat n)) ≅
        power l F X N (Int.ofNat n) :=
  (binary l E X F ι).power L n ≪≫
    @asIso _ _ _ _ (SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l F X) b.hom n)
      (SheafOfModules.isIso_scalarTensorPowerMap b n)
/-- The negative signed-power comparison, fixed by evaluation against `positiveLine`.
Source: Stacks 0GMX (blueprint: lem-pur-completed-line-tensor-coherence). -/
def negativeLine (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X)
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) (n : ℕ) :
    SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L (Int.negSucc n)) ≅
        power l F X N (Int.negSucc n) :=
  (SheafOfModules.existsUnique_scalarExtensionDualIso.{t + 1, t, max u (t + 1)}
    (completedCoefficientMap l E F ι X) L (line_cover l X L) n
    (power l F X N (Int.ofNat (n + 1))) (positiveLine l E X F ι L N b (n + 1))).exists.choose

/-- All signed-power comparisons. Source: Stacks 03EK, 0GMX
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def lineFamily (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X)
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∀ m : ℤ, SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m
  | .ofNat n => positiveLine l E X F ι L N b n
  | .negSucc n => negativeLine l E X F ι L N b n

/-- The signed-power comparisons are uniquely fixed by the positive power formula and the
negative evaluation formula. Source: Stacks 03EK, 0GMX
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: positive powers are prescribed. Negative powers are the unique dual comparison of
`existsUnique_scalarExtensionDualIso` relative to the positive ones. -/
theorem lineFamily_existsUnique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X)
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃! ℓ : ∀ m : ℤ,
        SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) (power l E X L m) ≅ power l F X N m,
      (∀ n : ℕ,
        (ℓ (Int.ofNat n)).hom = ((binary l E X F ι).power L n).hom ≫
          SheafOfModules.scalarTensorPowerMap.{t + 1, t, max u (t + 1)}
            (completedIntegralCommRingSheafUnrestricted l F X) b.hom n) ∧
      (∀ (n : ℕ) (U : X.ProEtᵒᵖ)
          (s t : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
          (f : (power l E X L (-Int.ofNat (n + 1))).val.obj U)
          (x : (power l E X L (Int.ofNat (n + 1))).val.obj U),
        pairing l F X N (Int.ofNat (n + 1)) U
          ((ℓ (Int.ofNat (n + 1))).hom.val.app U
            (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
              (completedCoefficientMap l E F ι X) _ U t x))
          ((ℓ (-Int.ofNat (n + 1))).hom.val.app U
            (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
              (completedCoefficientMap l E F ι X) _ U s f)) =
          s * t * (completedCoefficientMap l E F ι X).hom.app U
            (pairing l E X L (Int.ofNat (n + 1)) U x f)) := by
  have hneg (n : ℕ) :=
    SheafOfModules.existsUnique_scalarExtensionDualIso.{t + 1, t, max u (t + 1)}
    (completedCoefficientMap l E F ι X) L (line_cover l X L) n
    (power l F X N (Int.ofNat (n + 1))) (positiveLine l E X F ι L N b (n + 1))
  refine ⟨lineFamily l E X F ι L N b, ⟨fun n ↦ rfl, ?_⟩, ?_⟩
  · intro n U s t f x
    exact (hneg n).exists.choose_spec U s t f x
  · intro ℓ ⟨h₁, h₂⟩
    have hpos (n : ℕ) : ℓ (Int.ofNat n) = positiveLine l E X F ι L N b n :=
      Iso.ext (h₁ n)
    funext m
    cases m with
    | ofNat n => exact hpos n
    | negSucc n =>
      refine (hneg n).unique ?_ (hneg n).exists.choose_spec
      intro U s t f x
      have h := h₂ n U s t f x
      rw [hpos] at h
      exact h

section OrdinarySheaf

/-- The recorded ordinary extension is the actual change of rings on objects.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem completedOrdinaryScalarExtension_obj_eq (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l E F ι X).obj M =
      SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
        (completedCoefficientMap l E F ι X) M :=
  completedOrdinaryScalarExtension_obj l E F ι X M

/-- Maps out of the ordinary extension of a sheafified tensor are fixed on the sections
`s ⊗ (x ⊗ a)`. Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: transport along the recorded equality with the actual change of rings and apply
the pure-tensor extensionality of scalar extension. -/
theorem ordinaryExtension_tensor_hom_ext (M P : integralTowerModules l E X)
    {H : integralTowerModules l F X}
    (f g : (completedOrdinaryScalarExtension l E F ι X).obj
      ((SheafOfModules.siteSheafTensorRight P).obj M) ⟶ H)
    (h : ∀ (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
      (x : M.val.obj U) (a : P.val.obj U),
      f.val.app U (completedScalarTensorSection l E F ι X _ U s
        (SheafOfModules.siteSheafTensorTmul M P U x a)) =
      g.val.app U (completedScalarTensorSection l E F ι X _ U s
        (SheafOfModules.siteSheafTensorTmul M P U x a))) : f = g := by
  apply (cancel_epi (eqToIso (completedOrdinaryScalarExtension_obj l E F ι X
    ((SheafOfModules.siteSheafTensorRight P).obj M))).inv).1
  apply SheafOfModules.scalarExtension_tensor_hom_ext (completedCoefficientMap l E F ι X) M P
  intro U s x a
  exact h U s x a

/-- The ordinary comparison for tensoring with a module whose scalar extension is
identified with a given module. Source: Stacks 03EK
(blueprint: lem-pur-completed-line-tensor-coherence). -/
def ordinaryTensorComparisonApp (P : integralTowerModules l E X)
    (P' : integralTowerModules l F X)
    (c : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) P ≅ P') (M : integralTowerModules l E X) :
    (completedOrdinaryScalarExtension l E F ι X).obj
        ((SheafOfModules.siteSheafTensorRight P).obj M) ≅
      (SheafOfModules.siteSheafTensorRight P').obj
        ((completedOrdinaryScalarExtension l E F ι X).obj M) :=
  eqToIso (completedOrdinaryScalarExtension_obj_eq l E X F ι _) ≪≫
    (binary l E X F ι).tensorComparison M P ≪≫
    (SheafOfModules.siteSheafTensorRight (SheafOfModules.changeOfRingsOfUniverses.{t, t + 1,
      max u (t + 1), max u (t + 1)} (completedCoefficientMap l E F ι X) P)).mapIso
      (eqToIso (completedOrdinaryScalarExtension_obj_eq l E X F ι M).symm) ≪≫
    SheafOfModules.siteSheafTensorSecondIso ((completedOrdinaryScalarExtension l E F ι X).obj M) c

/-- Pure-tensor formula for `ordinaryTensorComparisonApp`.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem ordinaryTensorComparisonApp_tmul (P : integralTowerModules l E X)
    (P' : integralTowerModules l F X)
    (c : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) P ≅ P') (M : integralTowerModules l E X)
    (U : X.ProEtᵒᵖ) (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
    (x : M.val.obj U) (a : P.val.obj U) :
    (ordinaryTensorComparisonApp l E X F ι P P' c M).hom.val.app U
        (completedScalarTensorSection l E F ι X _ U s
          (SheafOfModules.siteSheafTensorTmul M P U x a)) =
      SheafOfModules.siteSheafTensorTmul _ P' U
        (completedScalarTensorSection l E F ι X M U s x)
        (c.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
          max u (t + 1)} (completedCoefficientMap l E F ι X) P U 1 a)) := by
  have h₀ : (ordinaryTensorComparisonApp l E X F ι P P' c M).hom.val.app U
        (completedScalarTensorSection l E F ι X _ U s
          (SheafOfModules.siteSheafTensorTmul M P U x a)) =
      ((eqToIso (completedOrdinaryScalarExtension_obj_eq l E X F ι _)).inv ≫
          (ordinaryTensorComparisonApp l E X F ι P P' c M).hom).val.app U
        (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1), max u (t + 1)}
          (completedCoefficientMap l E F ι X) _ U s
          (SheafOfModules.siteSheafTensorTmul M P U x a)) := rfl
  rw [h₀, ordinaryTensorComparisonApp]
  simp only [Iso.trans_hom, Iso.inv_hom_id_assoc, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [(binary l E X F ι).tensor_tmul, Functor.mapIso_hom]
  refine (congrArg (fun z ↦ (SheafOfModules.siteSheafTensorSecondIso
    ((completedOrdinaryScalarExtension l E F ι X).obj M) c).hom.val.app U z)
    (SheafOfModules.scalarTensor_first_tmul.{t + 1, t, max u (t + 1)} _ _ U _ _)).trans ?_
  exact SheafOfModules.scalarTensor_second_tmul.{t + 1, t, max u (t + 1)} _ c.hom U _ _

/-- Naturality of `ordinaryTensorComparisonApp` in the module.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: both composites send s ⊗ (x ⊗ a) to (s ⊗ f x) ⊗ c(a ⊗ 1). -/
theorem ordinaryTensorComparisonApp_naturality (P : integralTowerModules l E X)
    (P' : integralTowerModules l F X)
    (c : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) P ≅ P') {M M' : integralTowerModules l E X}
    (f : M ⟶ M') :
    (completedOrdinaryScalarExtension l E F ι X).map
        ((SheafOfModules.siteSheafTensorRight P).map f) ≫
      (ordinaryTensorComparisonApp l E X F ι P P' c M').hom =
    (ordinaryTensorComparisonApp l E X F ι P P' c M).hom ≫
      (SheafOfModules.siteSheafTensorRight P').map
        ((completedOrdinaryScalarExtension l E F ι X).map f) := by
  apply ordinaryExtension_tensor_hom_ext
  intro U s x a
  rw [SheafOfModules.comp_val, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    PresheafOfModules.comp_app, ModuleCat.comp_apply, ModuleCat.comp_apply,
    completedScalarTensorSection_naturality, ordinaryTensorComparisonApp_tmul]
  refine (congrArg (fun z ↦ (ordinaryTensorComparisonApp l E X F ι P P' c M').hom.val.app U
    (completedScalarTensorSection l E F ι X _ U s z))
    (SheafOfModules.scalarTensor_first_tmul.{t + 1, t, max u (t + 1)} f P U x a)).trans ?_
  rw [ordinaryTensorComparisonApp_tmul]
  refine Eq.trans ?_ (SheafOfModules.scalarTensor_first_tmul.{t + 1, t, max u (t + 1)}
    ((completedOrdinaryScalarExtension l E F ι X).map f) P' U _ _).symm
  rw [completedScalarTensorSection_naturality]

/-- The ordinary comparison for tensoring with a module identified after scalar
extension. Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence). -/
def ordinaryTensorComparison (P : integralTowerModules l E X)
    (P' : integralTowerModules l F X)
    (c : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) P ≅ P') :
    SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)} P ⋙
        completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙
        SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)} P' :=
  NatIso.ofComponents (ordinaryTensorComparisonApp l E X F ι P P' c)
    (fun f ↦ ordinaryTensorComparisonApp_naturality l E X F ι P P' c f)

/-- The ordinary tensor comparison is uniquely determined by its pure-tensor formula.
Source: Stacks 03EK (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: `ordinaryTensorComparison` satisfies it; two solutions agree componentwise by
`ordinaryExtension_tensor_hom_ext`. -/
theorem ordinaryTensorComparison_existsUnique (P : integralTowerModules l E X)
    (P' : integralTowerModules l F X)
    (c : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) P ≅ P') :
    ∃! e : SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)} P ⋙
        completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙
        SheafOfModules.siteSheafTensorRight.{t, t + 1, max u (t + 1), max u (t + 1)} P',
      ∀ (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
        (s : (completedIntegralCommRingSheafUnrestricted l F X).obj.obj U)
        (x : M.val.obj U) (a : P.val.obj U),
        (e.hom.app M).val.app U
            (completedScalarTensorSection l E F ι X _ U s
              (SheafOfModules.siteSheafTensorTmul M P U x a)) =
          SheafOfModules.siteSheafTensorTmul _ P' U
            (completedScalarTensorSection l E F ι X M U s x)
            (c.hom.val.app U (SheafOfModules.scalarExtensionSection.{t + 1, t, max u (t + 1),
              max u (t + 1)} (completedCoefficientMap l E F ι X) P U 1 a)) := by
  refine ⟨ordinaryTensorComparison l E X F ι P P' c,
    fun M U s x a ↦ ordinaryTensorComparisonApp_tmul l E X F ι P P' c M U s x a, ?_⟩
  intro e he
  apply Iso.ext
  ext M : 2
  apply ordinaryExtension_tensor_hom_ext
  intro U s x a
  exact (he M U s x a).trans (ordinaryTensorComparisonApp_tmul l E X F ι P P' c M U s x a).symm

end OrdinarySheaf


section Derived

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  integralScalarExtensionOfUniverses

/-- Transport of the naturality of a counit along equalities of functors.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem natural_of_model {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    {T T' : DerivedCategory A ⥤ DerivedCategory B}
    {G G' : CochainComplex A ℤ ⥤ CochainComplex B ℤ}
    (ε : DerivedCategory.Q ⋙ T ⟶ G ⋙ DerivedCategory.Q) (hT : T = T') (hG : G = G')
    (c : ∀ P : CochainComplex A ℤ,
      T'.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (G'.obj P))
    (hc : ∀ P, HEq (ε.app P) (c P)) {P P' : CochainComplex A ℤ} (g : P ⟶ P') :
    T'.map (DerivedCategory.Q.map g) ≫ c P' = c P ≫ DerivedCategory.Q.map (G'.map g) := by
  subst hT hG
  rw [← eq_of_heq (hc P), ← eq_of_heq (hc P')]
  exact ε.naturality g

/-- Naturality of the universal counit of the recorded derived scalar extension.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem completedScalarCounit_natural
    {A B : CochainComplex (integralTowerModules l E X) ℤ} (g : A ⟶ B) :
    (completedDerivedScalarExtension l E F ι X).map (DerivedCategory.Q.map g) ≫
        completedScalarCounit l E F ι X B =
      completedScalarCounit l E F ι X A ≫
        DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map g) := by
  exact natural_of_model (completedScalarCochainModel l E F ι X).ε rfl rfl
    (completedScalarCounit l E F ι X)
    (fun P ↦ heq_of_eq (completedScalarCochainModel_counit l E F ι X P)) g
/-- Transport of invertibility of a counit along equalities of functors.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem isIso_of_model {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    {T T' : DerivedCategory A ⥤ DerivedCategory B}
    {G G' : CochainComplex A ℤ ⥤ CochainComplex B ℤ}
    (ε : DerivedCategory.Q ⋙ T ⟶ G ⋙ DerivedCategory.Q) (hT : T = T') (hG : G = G')
    (c : ∀ P : CochainComplex A ℤ,
      T'.obj (DerivedCategory.Q.obj P) ⟶ DerivedCategory.Q.obj (G'.obj P))
    (hc : ∀ P, HEq (ε.app P) (c P)) (P : CochainComplex A ℤ) (h : IsIso (ε.app P)) :
    IsIso (c P) := by
  subst hT hG
  rw [← eq_of_heq (hc P)]
  exact h

/-- The universal counit is invertible on K-flat complexes.
Source: Stacks 06YY (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem completedScalarCounit_isIso
    (P : CochainComplex (integralTowerModules l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    IsIso (completedScalarCounit l E F ι X P) :=
  isIso_of_model (completedScalarCochainModel l E F ι X).ε rfl rfl
    (completedScalarCounit l E F ι X)
    (fun P ↦ heq_of_eq (completedScalarCochainModel_counit l E F ι X P)) P
    ((completedScalarCochainModel l E F ι X).computes P hP)

-- Copied from the private `localization_descent_with_comparison` in
-- `FiniteFreeCompletedScalarComparison`.
/-- Natural transformations out of a localization are fixed by a comparison on the source.
Source: Stacks 05Q2 (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem localization_descent_with_comparison
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Λ : C ⥤ D) (W : MorphismProperty C) [Λ.IsLocalization W]
    (F G : D ⥤ H) (V : C ⥤ H) (e : Λ ⋙ G ≅ V) (α : Λ ⋙ F ⟶ V) :
    ∃! χ : F ⟶ G, ∀ P : C, χ.app (Λ.obj P) ≫ e.hom.app P = α.app P := by
  let ff := Localization.fullyFaithfulWhiskeringLeft Λ W H
  let χ : F ⟶ G := ff.preimage (α ≫ e.inv)
  have hχ : Functor.whiskerLeft Λ χ = α ≫ e.inv := ff.map_preimage _
  refine ⟨χ, ?_, ?_⟩
  · intro P
    have h := NatTrans.congr_app hχ P
    change χ.app (Λ.obj P) = α.app P ≫ e.inv.app P at h
    rw [h, Category.assoc, e.inv_hom_id_app, Category.comp_id]
  · intro χ' hχ'
    apply ff.map_injective
    change Functor.whiskerLeft Λ χ' = Functor.whiskerLeft Λ χ
    rw [hχ]
    ext P
    apply (cancel_mono (e.hom.app P)).1
    change χ'.app (Λ.obj P) ≫ e.hom.app P =
      (α.app P ≫ e.inv.app P) ≫ e.hom.app P
    rw [hχ' P, Category.assoc, e.inv_hom_id_app, Category.comp_id]

open MonoidalCategory in
/-- Termwise tensor with a signed line preserves K-flat complexes.
Source: Stacks 06YN (blueprint: lem-pur-completed-line-tensor-coherence). -/
theorem complex_isKFlat (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (m : ℤ) (P : CochainComplex (integralTowerModules l E X) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) P) :
    CochainComplex.IsKFlatIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := completedIntegralCommRingSheafUnrestricted l E X) ((complex l E X L m).obj P) := by
  let A := completedIntegralCommRingSheafUnrestricted l E X
  let : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  let M := integralTowerModules l E X
  have (Y : M) : PreservesColimitsOfSize.{max u (t + 1), max u (t + 1)} (tensorLeft Y) :=
    SheafOfModules.tensorLeft_preservesColimits_independentCoefficients A Y
  have (Y : M) : PreservesColimitsOfSize.{0, 0} (tensorLeft Y) :=
    preservesColimitsOfSize_shrink (tensorLeft Y)
  have (Y : M) : PreservesColimitsOfSize.{0, 0} (tensorRight Y) :=
    preservesColimits_of_natIso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z)
        (fun f ↦ BraidedCategory.braiding_naturality_right Y f))
  have (Y : M) : (tensorLeft Y).Additive :=
    SheafOfModules.tensorLeft_additive_independent A Y
  have (Y : M) : (tensorRight Y).Additive :=
    Functor.additive_of_iso (F := tensorLeft Y)
      (NatIso.ofComponents (fun Z ↦ β_ Y Z)
        (fun f ↦ BraidedCategory.braiding_naturality_right Y f))
  let : MonoidalPreadditive M :=
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }
  let S := (CochainComplex.singleFunctor M 0).obj (power l E X L m)
  let c := SheafOfModules.SignedLineDerivedBaseChange.collapse.{t + 1, t, u} A (power l E X L m)
  have hS (K : CochainComplex M ℤ) (hK : K.Acyclic) (i : ℤ) : (K ⊗ S).ExactAt i :=
    have h1 : (((sheaf l E X L m).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt i :=
      (hK i).map (sheaf l E X L m)
    h1.of_iso (c.app K).symm
  intro K hK i
  have h := (hS _ (hP K hK) i).of_iso (HomologicalComplex.associator K P S)
  exact h.of_iso ((MonoidalCategory.tensorLeft K).mapIso (c.app P))

variable {E F}

/-- Existence and uniqueness of the derived signed-line comparison induced by an
ordinary one, normalized through the universal counits on good complexes.
Source: Stacks 06YY, 05Q2 (blueprint: lem-pur-completed-line-tensor-coherence).
Proof: on good complexes the source counit and the exact localization comparison
are invertible, so the displayed equation defines a comparison on the good
localization, which descends uniquely. Tensor by a line preserves K-flatness, so the
other counit is invertible as well and the descended map is an isomorphism. -/
theorem ordinary_existsUnique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1] (m : ℤ)
    (e : sheaf l E X L m ⋙ completedOrdinaryScalarExtension l E F ι X ≅
      completedOrdinaryScalarExtension l E F ι X ⋙ sheaf l F X N m) :
    ∃! d : tensor l E X L m ⋙ completedDerivedScalarExtension l E F ι X ≅
        completedDerivedScalarExtension l E F ι X ⋙ tensor l F X N m,
      ∀ P : (integralOperationsGoodComplex l E X).FullSubcategory,
        HEq ((completedDerivedScalarExtension l E F ι X).map
            ((factors l E X L m).hom.app P.obj) ≫
            completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
            DerivedCategory.Q.map
              ((comparisonComplex l E X F ι L N m e).hom.app P.obj))
          (d.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (tensor l F X N m).map (completedScalarCounit l E F ι X P.obj) ≫
            (factors l F X N m).hom.app
              ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) := by
  let G := integralOperationsGoodComplex l E X
  let Λ := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage G.ι
  have : Λ.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  let D := completedDerivedScalarExtension l E F ι X
  let V := G.ι ⋙ completedOrdinaryScalarComplex l E F ι X ⋙ complex l F X N m ⋙
    DerivedCategory.Q
  have hgood (P : G.FullSubcategory) : IsIso (completedScalarCounit l E F ι X P.obj) :=
    completedScalarCounit_isIso l E X F ι P.obj P.property.1
  let eC : Λ ⋙ D ⋙ tensor l F X N m ≅ V :=
    NatIso.ofComponents (fun P ↦ (tensor l F X N m).mapIso
        (@asIso _ _ _ _ (completedScalarCounit l E F ι X P.obj) (hgood P)) ≪≫
          (factors l F X N m).app ((completedOrdinaryScalarComplex l E F ι X).obj P.obj))
      (fun {P P'} f ↦ by
        let g := G.ι.map f
        have hc : D.map (DerivedCategory.Q.map g) ≫ completedScalarCounit l E F ι X P'.obj =
            completedScalarCounit l E F ι X P.obj ≫
              DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map g) :=
          completedScalarCounit_natural l E X F ι g
        have hfac : (tensor l F X N m).map (DerivedCategory.Q.map
            ((completedOrdinaryScalarComplex l E F ι X).map g)) ≫
            (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P'.obj) =
          (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P.obj) ≫
            DerivedCategory.Q.map ((complex l F X N m).map
              ((completedOrdinaryScalarComplex l E F ι X).map g)) :=
          (factors l F X N m).hom.naturality _
        have key : (tensor l F X N m).map (D.map (DerivedCategory.Q.map g)) ≫
            (tensor l F X N m).map (completedScalarCounit l E F ι X P'.obj) ≫
            (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P'.obj) =
          ((tensor l F X N m).map (completedScalarCounit l E F ι X P.obj) ≫
            (factors l F X N m).hom.app ((completedOrdinaryScalarComplex l E F ι X).obj P.obj)) ≫
            DerivedCategory.Q.map ((complex l F X N m).map
              ((completedOrdinaryScalarComplex l E F ι X).map g)) := by
          rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc, hfac,
            Category.assoc]
        exact key)
  let α : Λ ⋙ tensor l E X L m ⋙ D ⟶ V :=
    { app := fun P ↦ D.map ((factors l E X L m).hom.app P.obj) ≫
        completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
        DerivedCategory.Q.map ((comparisonComplex l E X F ι L N m e).hom.app P.obj)
      naturality := fun {P P'} f ↦ by
        let g := G.ι.map f
        have h1 : (tensor l E X L m).map (DerivedCategory.Q.map g) ≫
            (factors l E X L m).hom.app P'.obj =
          (factors l E X L m).hom.app P.obj ≫
            DerivedCategory.Q.map ((complex l E X L m).map g) :=
          (factors l E X L m).hom.naturality g
        have h2 : D.map (DerivedCategory.Q.map ((complex l E X L m).map g)) ≫
            completedScalarCounit l E F ι X ((complex l E X L m).obj P'.obj) =
          completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
            DerivedCategory.Q.map ((completedOrdinaryScalarComplex l E F ι X).map
              ((complex l E X L m).map g)) :=
          completedScalarCounit_natural l E X F ι ((complex l E X L m).map g)
        have h3 : (completedOrdinaryScalarComplex l E F ι X).map ((complex l E X L m).map g) ≫
            (comparisonComplex l E X F ι L N m e).hom.app P'.obj =
          (comparisonComplex l E X F ι L N m e).hom.app P.obj ≫
            (complex l F X N m).map ((completedOrdinaryScalarComplex l E F ι X).map g) :=
          (comparisonComplex l E X F ι L N m e).hom.naturality g
        have key : D.map ((tensor l E X L m).map (DerivedCategory.Q.map g)) ≫
            (D.map ((factors l E X L m).hom.app P'.obj) ≫
              completedScalarCounit l E F ι X ((complex l E X L m).obj P'.obj) ≫
              DerivedCategory.Q.map ((comparisonComplex l E X F ι L N m e).hom.app P'.obj)) =
          (D.map ((factors l E X L m).hom.app P.obj) ≫
              completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj) ≫
              DerivedCategory.Q.map ((comparisonComplex l E X F ι L N m e).hom.app P.obj)) ≫
            DerivedCategory.Q.map ((complex l F X N m).map
              ((completedOrdinaryScalarComplex l E F ι X).map g)) := by
          rw [← D.map_comp_assoc, h1, D.map_comp_assoc, reassoc_of% h2,
            ← Functor.map_comp, h3, Functor.map_comp]
          simp only [Category.assoc]
        exact key }
  obtain ⟨χ, hχ, hu⟩ := localization_descent_with_comparison Λ W
    (tensor l E X L m ⋙ D) (D ⋙ tensor l F X N m) V eC α
  have happ (P : G.FullSubcategory) : IsIso (χ.app (Λ.obj P)) := by
    have h : χ.app (Λ.obj P) = α.app P ≫ eC.inv.app P := by
      rw [← hχ P, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    rw [h]
    have : IsIso (completedScalarCounit l E F ι X ((complex l E X L m).obj P.obj)) :=
      completedScalarCounit_isIso l E X F ι _ (complex_isKFlat l E X L m P.obj P.property.1)
    exact IsIso.comp_isIso' (IsIso.comp_isIso' (D.mapIso ((factors l E X L m).app P.obj)).isIso_hom
      (IsIso.comp_isIso' this (DerivedCategory.Q.mapIso
        ((comparisonComplex l E X F ι L N m e).app P.obj)).isIso_hom)) (eC.app P).isIso_inv
  have : Λ.EssSurj := Localization.essSurj Λ W
  have hiso : IsIso χ := by
    have : ∀ K, IsIso (χ.app K) := by
      intro K
      have := happ (Λ.objPreimage K)
      exact (NatTrans.isIso_app_iff_of_iso χ (Λ.objObjPreimageIso K)).1 this
    exact NatIso.isIso_of_isIso_app χ
  refine ⟨asIso χ, fun P ↦ heq_of_eq (hχ P).symm, ?_⟩
  intro d hd
  apply Iso.ext
  apply hu
  intro P
  exact (eq_of_heq (hd P)).symm

end Derived

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted completedCoefficientMap
  completedOrdinaryScalarExtension completedDerivedScalarExtension
  completedScalarCounit completedScalarTensorSection integralScalarExtensionOfUniverses
  completedScalarChangeData completedOrdinaryScalarComplex

/-- Existence and uniqueness of all ordinary signed-line comparisons with their
representative formulas. Source: Stacks 03EL, 03EO, 06YY; blueprint Proof (3)
(blueprint: lem-pur-completed-line-tensor-coherence).
Proof: tensor powers of b use the canonical binary comparison, including its
multiplication unitor at zero. The negative map is uniquely determined by evaluation
and becomes an isomorphism after trivializing the line. Define the ordinary comparison
on pure tensors by ((x tensor a) tensor s) mapped to (x tensor s) tensor b_m(a tensor 1).
Balancedness and sheafification give an isomorphism natural in the module. A line is
flat; tensor with it preserves flat-term K-flat complexes. Apply the K-flat localization
equivalence, using the specified universal counits. The displayed equation fixes the
derived comparison uniquely and proves independence from the representative. -/
theorem pairData_existsUnique (L : integralTowerModules l E X) [L.IsFiniteLocallyFreeOfRank 1]
    (N : integralTowerModules l F X) [N.IsFiniteLocallyFreeOfRank 1]
    (b : SheafOfModules.changeOfRingsOfUniverses.{t, t + 1, max u (t + 1), max u (t + 1)}
      (completedCoefficientMap l E F ι X) L ≅ N) :
    ∃! p : PairData l E X F ι L N, IsPairNormalized l E X F ι L N b p := by
  obtain ⟨ℓ, ⟨h₁, h₂⟩, hℓ⟩ := lineFamily_existsUnique l E X F ι L N b
  choose σ hσ hσu using fun m : ℤ ↦
    ordinaryTensorComparison_existsUnique l E X F ι (power l E X L m) (power l F X N m) (ℓ m)
  choose δ hδ hδu using fun m : ℤ ↦ ordinary_existsUnique l X ι L N m (σ m)
  refine ⟨(ℓ, σ, δ), ⟨h₁, h₂, hσ, hδ⟩, ?_⟩
  rintro ⟨ℓ', σ', δ'⟩ ⟨h₁', h₂', h₃', h₄'⟩
  obtain rfl : ℓ' = ℓ := hℓ ℓ' ⟨h₁', h₂'⟩
  obtain rfl : σ' = σ := funext fun m ↦ hσu m (σ' m) (h₃' m)
  obtain rfl : δ' = δ := funext fun m ↦ hδu m (δ' m) (h₄' m)
  rfl

end CompletedLineTensor
end WeilConjectures
