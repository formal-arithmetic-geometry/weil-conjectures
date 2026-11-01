/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalOperations.RationalOperationsData
public import WeilConjectures.SixFunctors.CoefDualFormulaScalarTranspose.CoefDualFormulaScalarTranspose
import WeilConjectures.SixFunctors.Integral.IntegralResidueTor
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomModelsExist
import WeilConjectures.SixFunctors.RationalOperations.IntegralDualFormulaComparison
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.Adjunction

/-! # The normalized adjunction for the rational dual formula

Source: the exceptional-adjunction and coefficient-localization argument in
lem-coef-rational-operations, steps 10--11
(blueprint: lem-sf-rational-dual-formula-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open scoped TensorProduct
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem localizeAdjunction
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    (QX : C ⥤ C') (WX : MorphismProperty C) [QX.IsLocalization WX]
    (QY : D ⥤ D') (WY : MorphismProperty D) [QY.IsLocalization WY]
    (F' : C' ⥤ D') (G' : D' ⥤ C')
    (hF : F ⋙ QY = QX ⋙ F') (hG : G ⋙ QX = QY ⋙ G') :
    ∃ a : F' ⊣ G', ∀ M : D,
      HEq (a.counit.app (QY.obj M)) (QY.map (adj.counit.app M)) := by
  let : CatCommSq F QX QY F' := ⟨eqToIso hF⟩
  let : CatCommSq G QY QX G' := ⟨eqToIso hG⟩
  refine ⟨adj.localization QX WX QY WY F' G', ?_⟩
  intro M
  rw [Adjunction.localization_counit_app]
  change HEq (F'.map ((eqToIso hG).inv.app M) ≫
    (eqToIso hF).inv.app (G.obj M) ≫ QY.map (adj.counit.app M)) _
  simp only [eqToIso.inv, eqToHom_app, eqToHom_map]
  exact (eqToHom_comp_heq _ _).trans (eqToHom_comp_heq _ _)

namespace WeilConjectures.RationalOperations
open ConstructibleExceptionalCoefficients

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  {Y : Scheme.{u}} [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f) (F : FieldStage.{u} l)
  (wX : IntegralFiniteExtension.DualizingDatum l X D hl F.carrier)
  (wY : IntegralFiniteExtension.DualizingDatum l Y D hl F.carrier)
  (A : RationalVerdier.Datum D l hl X F.carrier wX)
  (B : RationalVerdier.Datum D l hl Y F.carrier wY)

/-- The integral representative of the dual-pullback-dual functor, using the supplied
duality presentations and the prescribed completed pullback.
Source: lem-coef-rational-operations, step 11
(blueprint: lem-sf-rational-dual-formula-adjunction). -/
abbrev integralDualFormula :=
  (IntegralVerdier.restrictedDual l F.carrier Y wY.omega.obj B.preserves).rightOp ⋙
    (@constructibleIntegralPullback l _ F.carrier _ _ _ X Y f
      (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)).op ⋙
    IntegralVerdier.restrictedDual l F.carrier X wX.omega.obj A.preserves

private theorem dual_localization
    {W : Scheme.{u}} [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))]
    (w : IntegralFiniteExtension.DualizingDatum l W D hl F.carrier)
    (V : RationalVerdier.Datum D l hl W F.carrier w) :
    (IntegralVerdier.restrictedDual l F.carrier W w.omega.obj V.preserves) ⋙
        sfRationalConstructibleLocalization l F.carrier W =
      (sfRationalConstructibleLocalization l F.carrier W).op ⋙ V.dual := by
  apply Functor.hext
  · intro K
    exact (V.objects ((sfRationalConstructibleLocalization l F.carrier W).obj K.unop)).symm
  · intro K L g
    exact (V.pure L.unop K.unop g.unop 1).symm

set_option linter.unusedSectionVars false in
private theorem pull_localization :
    (@constructibleIntegralPullback l _ F.carrier _ _ _ X Y f
      (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)) ⋙
        sfRationalConstructibleLocalization l F.carrier X =
      sfRationalConstructibleLocalization l F.carrier Y ⋙
        (@rationalDerivedPullback l _ F.carrier _ _ _ X Y f
          (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)) := by
  let := RationalVerdier.units D l hl X
  let := RationalVerdier.units D l hl Y
  have h := (rationalDerivedPullback_existsUnique l F.carrier f).exists.choose_spec
  apply Functor.hext
  · intro K
    exact (h.2.1 _).symm
  · intro K L g
    exact (h.2.2 K L g 1).symm

private theorem formula_localization :
    integralDualFormula D l hl X (f := f) F wX wY A B ⋙
        sfRationalConstructibleLocalization l F.carrier X =
      sfRationalConstructibleLocalization l F.carrier Y ⋙
        dualFormula l X D hl (f := f) F wX wY A B := by
  let QX := sfRationalConstructibleLocalization l F.carrier X
  let QY := sfRationalConstructibleLocalization l F.carrier Y
  let dX := IntegralVerdier.restrictedDual l F.carrier X wX.omega.obj A.preserves
  let dY := IntegralVerdier.restrictedDual l F.carrier Y wY.omega.obj B.preserves
  let p := @constructibleIntegralPullback l _ F.carrier _ _ _ X Y f
    (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)
  let q := @rationalDerivedPullback l _ F.carrier _ _ _ X Y f
    (RationalVerdier.units D l hl X) (RationalVerdier.units D l hl Y)
  have hX : dX ⋙ QX = QX.op ⋙ A.dual := dual_localization D l hl F wX A
  have hY : dY.rightOp ⋙ QY.op = QY ⋙ B.dual.rightOp :=
    congrArg Functor.rightOp (dual_localization D l hl F wY B)
  have hp : p.op ⋙ QX.op = QY.op ⋙ q.op :=
    congrArg Functor.op (pull_localization D l hl X F)
  change dY.rightOp ⋙ p.op ⋙ (dX ⋙ QX) = _
  rw [hX]
  change dY.rightOp ⋙ (p.op ⋙ QX.op) ⋙ A.dual = _
  rw [hp]
  change (dY.rightOp ⋙ QY.op) ⋙ q.op ⋙ A.dual = _
  rw [hY]
  rfl

omit [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))] in
private theorem support_localization :
    sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⋙
          sfRationalConstructibleLocalization l F.carrier Y =
      sfRationalConstructibleLocalization l F.carrier X ⋙
        sfCompactSupportFiniteFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier := by
  apply Functor.hext
  · intro K
    rfl
  · intro K L g
    let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).1
    let := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).2
    apply heq_of_eq
    change (1 : Localization.Away (Padic.coefficientExtensionUniformizer l F.carrier))
      ⊗ₜ[Padic.coefficientExtensionIntegers l F.carrier]
        (sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).map g = _
    exact (LinearMap.baseChange_tmul
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier).mapLinearMap
          (Padic.coefficientExtensionIntegers l F.carrier)) 1 g).symm

private theorem rationalAdjunction_of_integral
    (adj : sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
        integralDualFormula D l hl X (f := f) F wX wY A B) :
    ∃ a : sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
          dualFormula l X D hl (f := f) F wX wY A B,
      ∀ M : sfIntegralConstructibleCategory l F.carrier Y,
        HEq (a.counit.app ((sfRationalConstructibleLocalization l F.carrier Y).obj M))
          ((sfRationalConstructibleLocalization l F.carrier Y).map (adj.counit.app M)) := by
  let R := Padic.coefficientExtensionIntegers l F.carrier
  let t := Padic.coefficientExtensionUniformizer l F.carrier
  let CX := sfIntegralConstructibleCategory l F.carrier X
  let CY := sfIntegralConstructibleCategory l F.carrier Y
  have : ∀ n : ℤ, (shiftFunctor CX n).Linear R :=
    ScalarLocalization.semilinear_all_shift_linear _ _
  have : ∀ n : ℤ, (shiftFunctor CY n).Linear R :=
    ScalarLocalization.semilinear_all_shift_linear _ _
  have : (sfRationalConstructibleLocalization l F.carrier X).IsLocalization
      (Rationalization.W (Submonoid.powers t) CX) :=
    ScalarLocalization.semilinear_localization_isLocalization R CX t
  have : (sfRationalConstructibleLocalization l F.carrier Y).IsLocalization
      (Rationalization.W (Submonoid.powers t) CY) :=
    ScalarLocalization.semilinear_localization_isLocalization R CY t
  exact localizeAdjunction adj
    (sfRationalConstructibleLocalization l F.carrier X)
      (Rationalization.W (Submonoid.powers t) CX)
    (sfRationalConstructibleLocalization l F.carrier Y)
      (Rationalization.W (Submonoid.powers t) CY) _ _
    (support_localization D l hl X c F) (formula_localization D l hl X F wX wY A B)

private noncomputable def integralEquivalence
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of D.k))] [QuasiCompact (W ↘ Spec (.of D.k))]
    [IsSeparated (W ↘ Spec (.of D.k))] :
    finiteTorConstructibleIntegralCategory l F.carrier W ≌
      sfIntegralConstructibleCategory l F.carrier W := by
  let := RationalVerdier.units D l hl W
  let i := PurCompactSupport.finiteTorIntegralInclusion l F.carrier W
  have hi : i.FullyFaithful :=
    { preimage := fun g ↦ ObjectProperty.homMk g.hom }
  have : i.Full := hi.full
  have : i.Faithful := hi.faithful
  have : i.EssSurj := ⟨fun K ↦ by
    refine ⟨⟨K.obj, ?_⟩, ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩
    rw [← (integral_residue_tor D l hl F.carrier W).2]
    exact K.property⟩
  have : i.IsEquivalence := {}
  exact i.asEquivalence

private theorem integralAdjunction_exists
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (S : System l Ω D hl (f := f)) :
    ∃ G : sfIntegralConstructibleCategory l F.carrier Y ⥤
        sfIntegralConstructibleCategory l F.carrier X,
      Nonempty (sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣ G) := by
  let eX : C l Ω X (.integral F) ≌ sfIntegralConstructibleCategory l F.carrier X :=
    integralEquivalence D l hl F X
  let eY : C l Ω Y (.integral F) ≌ sfIntegralConstructibleCategory l F.carrier Y :=
    integralEquivalence D l hl F Y
  let adj := (eX.symm.toAdjunction.comp
    (S.ring.operation c (.integral F)).adjunction).comp eY.toAdjunction
  let iso := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft eX.inverse (S.ring.integralLeft c F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eX.counitIso _ ≪≫ (Functor.leftUnitor _)
  exact ⟨_, ⟨adj.ofNatIsoLeft iso⟩⟩

/-- The counit is the localization of the integral counit whose trace/evaluation
characterization makes the identity the integral formula comparison. This pins the
adjunction independently of any exceptional coefficient system or comparison isomorphism.
Source: lem-coef-rational-operations, steps 10--11, and the canonical integral formula
(blueprint: lem-sf-rational-dual-formula-adjunction). -/
def DualFormulaAdjunctionNormalized
    (adj : sfCompactSupportFiniteFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
        dualFormula l X D hl (f := f) F wX wY A B) : Prop :=
  ∃ aZ : IntegralHom.TensorPresentation.{u, u} c.Z
      (completedIntegralCommRingSheafUnrestricted l F.carrier c.Z),
    ∃ adjI : sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
          integralDualFormula D l hl X F wX wY A B,
      (∀ M : sfIntegralConstructibleCategory l F.carrier Y,
        CoefDualFormulaScalarTranspose.FormulaNormalized D l hl F.carrier f c
          wX wY A.ordinary aZ B.ordinary A.symmetry
          (integralDualFormula D l hl X F wX wY A B) adjI M (Iso.refl _)) ∧
      ∀ M : sfIntegralConstructibleCategory l F.carrier Y,
        HEq (adj.counit.app ((sfRationalConstructibleLocalization l F.carrier Y).obj M))
          ((sfRationalConstructibleLocalization l F.carrier Y).map (adjI.counit.app M))

/-- The dual formula has an adjunction with its trace-normalized, localized counit.
This assertion concerns one coefficient field and does not choose an isomorphism from
the right adjoint of a coefficient system.
Source: lem-coef-rational-operations, steps 10--11
(blueprint: lem-sf-rational-dual-formula-adjunction).

Proof: use the supplied coefficient system for its integral exceptional adjunction
at the fixed compactification. The theorem
integral_residue_tor identifies its finite-Tor integral categories with the entire
integral constructible categories. Transport across these full-category equivalences
and integralLeft to obtain an adjunction for the prescribed integral compact support.
For the supplied dualizing objects, use the canonical integral dual formula.
Its components are characterized by FormulaNormalized: evaluate into omega_X, apply
the ordinary projection map and the quotient-normalized completion augmentation, and
then apply the relative structural trace. Currying and the inverse biduality map give
the inverse Hom bijection, so these components are natural isomorphisms. Transport the
integral exceptional adjunction along that isomorphism. The identity now satisfies
FormulaNormalized for the transported adjunction. Choose the ordinary derived tensor
presentation on c.Z; its representative normalization makes the projection map the same
one used in this characterization. The integral Hom bijection is O_F-linear, since
both dualities and completed pullback are linear. Tensor it and its inverse with the
fraction field. Objects are unchanged; the triangle equations localize, giving a
rational adjunction. The object and pure-map equations in A and B identify its right
functor with the stated dualFormula, and the coefficient-passage definition identifies
its left functor with the stated compact support. Its counit on an integral object is
the integral counit tensored with one, which is exactly the displayed HEq. Empty schemes,
zero objects and torsion objects require no change to these constructions. -/
theorem rationalDualFormulaAdjunction_exists
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (S : System l Ω D hl (f := f)) :
    ∃ adj : sfCompactSupportFiniteFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c F.carrier ⊣
          dualFormula l X D hl (f := f) F wX wY A B,
      DualFormulaAdjunctionNormalized D l hl X c F wX wY A B adj := by
  obtain ⟨G, ⟨adj⟩⟩ := integralAdjunction_exists D l hl X c F Ω S
  obtain ⟨aZ, _⟩ := IntegralHom.models_exist l F.carrier c.Z D hl
  obtain ⟨e, he⟩ := integralDualFormulaComparison D l hl X c F.carrier wX wY
    A.preserves B.preserves A.ordinary aZ B.ordinary A.symmetry G adj
  let adjI := adj.ofNatIsoRight e
  obtain ⟨adjQ, hQ⟩ := rationalAdjunction_of_integral D l hl X c F wX wY A B adjI
  exact ⟨adjQ, aZ, adjI, he, hQ⟩

end WeilConjectures.RationalOperations
