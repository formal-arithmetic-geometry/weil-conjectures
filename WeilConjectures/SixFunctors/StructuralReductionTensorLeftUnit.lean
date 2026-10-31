/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReductionData
import WeilConjectures.SixFunctors.SubstitutedWordCompletionIsomorphism
import all WeilConjectures.SixFunctors.TensorAdjunctionReductionSquares

/-! Constructor case for structural word substitution.
Source: current blueprint fix-prop-coherence, structural substitution step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.OpenInterchangeReduction

private theorem transported_left_unitor_naturality
    {A : Type*} [Category A] {H : Aᵒᵖ × A ⥤ A}
    (TA : CoefficientClosedStructure H) (T : A × A ⥤ A) (e : T = TA.tensor)
    {X Y : A} (f : X ⟶ Y) :
    T.map (Prod.mkHom (𝟙 TA.monoidal.tensorUnit) f) ≫
        (eqToIso (congrArg (fun U : A × A ⥤ A ↦
          U.obj (TA.monoidal.tensorUnit, Y)) e)).hom ≫
        (TA.monoidal.leftUnitor Y).hom =
      (eqToIso (congrArg (fun U : A × A ⥤ A ↦
        U.obj (TA.monoidal.tensorUnit, X)) e)).hom ≫
        (TA.monoidal.leftUnitor X).hom ≫ f := by
  subst T
  let := TA.monoidal
  simpa only [eqToIso_refl, Iso.refl_hom, Category.id_comp,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.id_tensorHom] using MonoidalCategory.leftUnitor_naturality f

set_option synthInstance.maxSize 4096 in
/-- The structuralReductionTensorLeftUnit component of structural word substitution.
Source: current blueprint fix-prop-coherence, maps-used sentence, scalar-unit case.
(blueprint: lem-sf-structural-reduction-word-substitution-tensorleftunit)

Proof: completion transport is invertible on every recursively admissible word.
Left-unitor naturality cancels the child's completion map in the definition of
the integral generator. The resulting integral map is inverse tensor completion
followed by the ordinary left unitor at the integral child. Expand the recursive
coefficient map, apply the specified unit normalization, and use left-unitor
naturality at the child's coefficient map. All factors are actual whole-system
maps. No bound on the substituted child is required.
-/
theorem structuralReductionTensorLeftUnit
    {D : FiniteFieldDatum.{u}} (coeff : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic coeff.l) E]
    [FiniteDimensional (Padic coeff.l) E]
    (o : GeneratorReduction.Operations coeff.l E)
    (_hShort : ∀ {S : Type s} (W : S → Scheme.{u})
      (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
      {I : Type i} (location : I → S)
      {a : S} {B C : GeneratorReduction.Word W location a}
      (g : GeneratorReduction.GeneratorKind W location B C),
      Structural g → B.length ≤ 3 → C.length ≤ 3 →
      ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
        (lo hi torLo torHi : ℤ),
        (∀ k : I, GeneratorReduction.Admissible coeff.l E
          (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
          lo hi torLo torHi) →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi B →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi C →
        GeneratorReduction.Assertion coeff.l E W location o K g)
    {S : Type s} (W : S → Scheme.{u})
    (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S}
    {B : GeneratorReduction.Word W location a}
    (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, GeneratorReduction.Admissible coeff.l E
      (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hB : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
    (GeneratorReduction.Word.tensor (GeneratorReduction.Word.unit a) B))
    (hC : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
    B) :
    GeneratorReduction.Assertion coeff.l E W location o K
    (GeneratorReduction.GeneratorKind.tensorLeftUnit B) := by
  have hc := GeneratorReduction.substitutedWordCompletion_isIso coeff.l E W location o B K
    lo hi torLo torHi _hAdm hC
  have ht := GeneratorReduction.substitutedWordCompletion_isIso coeff.l E W location o
    (.tensor (.unit a) B) K lo hi torLo torHi _hAdm hB
  have hm : IsIso ((o.ringed.tensor (W a)).ordinary.tensor.map
      (Prod.mkHom
        (𝟙 (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit)
        (B.completionMap coeff.l E W location o K))) := by
    have : IsIso (Prod.mkHom
        (𝟙 (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit)
        (B.completionMap coeff.l E W location o K)) :=
      (Iso.prod (Iso.refl _) (asIso _)).isIso_hom
    infer_instance
  have hchi : IsIso ((GeneratorReduction.tensorCompletion coeff.l E o (W a)).app
      ((IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit,
        B.integralValue coeff.l E W location o K)) := by
    let U :=
      (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit
    have hfull : IsIso
        ((o.ringed.tensor (W a)).ordinary.tensor.map
          (Prod.mkHom
            (𝟙 U)
            (B.completionMap coeff.l E W location o K)) ≫
          (GeneratorReduction.tensorCompletion coeff.l E o (W a)).app
          ((IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit,
              B.integralValue coeff.l E W location o K)) := by
      simpa only [U, GeneratorReduction.Word.completionMap,
        GeneratorReduction.Word.integralValue, GeneratorReduction.Word.ringedValue] using ht
    exact IsIso.of_isIso_comp_left
      ((o.ringed.tensor (W a)).ordinary.tensor.map
        (Prod.mkHom
          (𝟙
            (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit)
          (B.completionMap coeff.l E W location o K))) _
  have hn := transported_left_unitor_naturality
    (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed
    (o.ringed.tensor (W a)).ordinary.tensor (o.ringed.tensorClosed (W a))
    (B.completionMap coeff.l E W location o K)
  have hi : (GeneratorReduction.GeneratorKind.tensorLeftUnit B).integralMap
      coeff.l E W location o K =
      inv ((GeneratorReduction.tensorCompletion coeff.l E o (W a)).app
        ((IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit,
          B.integralValue coeff.l E W location o K)) ≫
        (eqToIso (congrArg (fun T ↦ T.obj
          ((IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.tensorUnit,
            B.integralValue coeff.l E W location o K))
          (o.ringed.tensorClosed (W a)))).hom ≫
        ((IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed.monoidal.leftUnitor
          (B.integralValue coeff.l E W location o K)).hom := by
    dsimp only [GeneratorReduction.GeneratorKind.integralMap]
    rw [GeneratorReduction.inverseOrZero_eq_inv]
    apply (cancel_epi ((GeneratorReduction.Word.tensor
      (GeneratorReduction.Word.unit a) B).completionMap coeff.l E W location o K)).1
    simp only [IsIso.hom_inv_id_assoc]
    dsimp only [GeneratorReduction.Word.completionMap, GeneratorReduction.Word.integralValue,
      GeneratorReduction.GeneratorKind.ringedMap, GeneratorReduction.Word.ringedValue]
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hn.symm
  unfold GeneratorReduction.Assertion
  rw [hi]
  dsimp only [GeneratorReduction.Word.r, GeneratorReduction.Word.integralValue,
    GeneratorReduction.GeneratorKind.systemMap, GeneratorReduction.tensorR]
  rw [GeneratorReduction.inverseOrZero_eq_inv]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc]
  congr 1
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp,
    eqToIso.hom, eqToHom_app, Category.assoc] using
    GeneratorReduction.comparison_left_unitor
      (IntegralSystemRealization.calculus coeff.l E (W a)).integralClosed
      (IntegralSystemRealization.calculus coeff.l E (W a)).systemClosed
      (IntegralSystemRealization.calculus coeff.l E (W a)).reduction
      (IntegralSystemRealization.calculus coeff.l E (W a)).reductionTensor
      (o.unitReduction (W a)) (o.unitNormalization (W a))
      (o.ringed.tensor (W a)).ordinary.tensor (o.ringed.tensorClosed (W a))
      (B.integralValue coeff.l E W location o K)
      (B.systemValue coeff.l E W location o
        (GeneratorReduction.inputReduction coeff.l E W location K))
      (B.r coeff.l E W location o K)

end WeilConjectures.OpenInterchangeReduction
