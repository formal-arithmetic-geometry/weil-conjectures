/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierCompletion
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierSignedKFlat
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedExact
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierLocalizedEvaluation
import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationBiduality

/-! # K-flat part of the rationalization of an integral Verdier conclusion

This is the coefficient-localization part of the rational Verdier construction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped TensorProduct

namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem equivalence_of_bidual {C : Type*} [Category* C]
    (F : Cᵒᵖ ⥤ C) (e : 𝟭 C ≅ F.rightOp ⋙ F) : F.IsEquivalence := by
  let : (F.rightOp ⋙ F).IsEquivalence := Functor.isEquivalence_of_iso e
  let : F.rightOp.Faithful := Functor.Faithful.of_comp F.rightOp F
  have : F.Faithful := by
    constructor
    intro X Y f g h
    apply Quiver.Hom.unop_inj
    apply F.rightOp.map_injective
    exact congrArg Quiver.Hom.op h
  have : F.rightOp.Full := Functor.Full.of_comp_faithful F.rightOp F
  have : F.Full := by
    constructor
    intro X Y f
    refine ⟨(F.rightOp.preimage f.op).op, ?_⟩
    exact Quiver.Hom.op_inj (F.rightOp.map_preimage f.op)
  have : F.EssSurj := by
    constructor
    intro X
    exact ⟨F.rightOp.obj X, ⟨(e.app X).symm⟩⟩
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

-- The unchanged statement names its K-flat witnesses although its equation does not use them.
set_option linter.unusedVariables false in
/-- Localizing a fixed integral Verdier conclusion supplies the rational datum and the
Koszul naturality equation on K-flat representatives. Passing from this representative
equation to arbitrary derived maps is a separate descent step.
Source: blueprint thm-coef-rational-verdier, proof steps 2--5
(blueprint: lem-coef-rational-verdier-datum-kflat).

Proof: retain the integral tensor presentation and its signed representative, localize
the internal-Hom maps on pure tensors, and extend by additivity over the raw scalar
localization. Localized distinguished triangles give exactness and localized integral
delta gives the actual biduality isomorphism. The normalized completion comparison is
transported through the ordinary presentation; its naturality transports evaluation.
The Koszul representative formula is natural for K-flat chain maps; this theorem records
only that representative equation. -/
theorem datum_of_integral_kflat
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (wE : IntegralFiniteExtension.DualizingDatum l X D hl E)
    (h : IntegralVerdier.Conclusion l E X D hl wE.omega wE.reduction) :
    ∃ A : Datum D l hl X E wE,
      ∀ (P P' Q Q' : CochainComplex (IntegralHom.Modules.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X)) ℤ)
        (hP : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P)
        (hP' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) P')
        (hQ : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q)
        (hQ' : IntegralHom.flat.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X) Q')
        (f : P ⟶ P') (g : Q ⟶ Q'),
        A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map f)
          (DerivedCategory.Q.map g)) ≫
            (A.symmetry.swap (DerivedCategory.Q.obj P') (DerivedCategory.Q.obj Q')).hom =
          (A.symmetry.swap (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
            A.ordinary.tensor.map (Prod.mkHom (DerivedCategory.Q.map g)
              (DerivedCategory.Q.map f)) := by
  classical
  obtain ⟨a, s, reduction, finiteSymmetry, _, hp, _, hex, comparisons, _, _, _, _, _, _,
    hdelta, hnaturality⟩ := h
  let F₀ := IntegralVerdier.restrictedDual l E X wE.omega.obj hp
  have hd (K : sfIntegralConstructibleCategory l E X) :
      IsIso (ObjectProperty.homMk
        (IntegralVerdier.delta X a s wE.omega.obj K.obj) : K ⟶
          (F₀.rightOp ⋙ F₀).obj K) := by
    exact (ObjectProperty.isIso_hom_iff _).mp (hdelta K)
  let b₀ : 𝟭 (sfIntegralConstructibleCategory l E X) ≅ F₀.rightOp ⋙ F₀ :=
    NatIso.ofComponents
      (fun K ↦ @asIso _ _ _ _ (ObjectProperty.homMk
        (IntegralVerdier.delta X a s wE.omega.obj K.obj)) (hd K)) (by
          intro K M f
          apply ObjectProperty.hom_ext
          exact hnaturality K M f)
  let F := localizedDual l E X wE.omega hp
  obtain ⟨ho, ha, hlinear, hm⟩ := localizedDual_spec l E X wE.omega hp
  let : F.Additive := ha
  obtain ⟨b, hb⟩ := ScalarLocalization.biduality
    (Padic.coefficientExtensionUniformizer l E) F₀ F ho hm b₀
  obtain ⟨c⟩ := completion_exists D l hl X E a
  refine ⟨{
    ordinary := a
    symmetry := s
    completion := c
    preserves := hp
    dual := F
    objects := ho
    additive := ha
    linear := fun K M f z ↦ hlinear K M f ((sfRationalCoefficientEquiv l E).symm z)
    pure := hm
    equivalence := equivalence_of_bidual F b
    exact := localizedDual_exact l E X wE.omega hp hex
    bidual := b
    bidual_integral := fun K ↦ hb ((sfRationalConstructibleLocalization l E X).obj K)
    evaluation := localizedEvaluation D l hl X E wE.omega hp a c
    evaluation_integral := ?_
    evaluation_natural := localizedEvaluation_natural D l hl X E wE.omega hp a c
  }, ?_⟩
  · intro K
    exact eqToHom_comp_heq
      ((sfRationalConstructibleLocalization l E X).map
        (integralEvaluation D l hl X E wE.omega hp a c K))
      (localizedEvaluation_source D l hl X E wE.omega hp
        ((sfRationalConstructibleLocalization l E X).obj K))
  · intro P P' Q Q' hP hP' hQ hQ' f g
    exact signed_kflat_natural X _ a s P P' Q Q' hP hP' hQ hQ' f g

end WeilConjectures.RationalVerdier
