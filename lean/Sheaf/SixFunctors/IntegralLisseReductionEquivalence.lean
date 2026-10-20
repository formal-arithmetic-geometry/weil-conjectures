/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionData
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.SixFunctors.IntegralLisseFiniteConstants
import Sheaf.SixFunctors.IntegralLisseCoefficientLimit
import Sheaf.SixFunctors.IntegralLisseCoefficientQuotients
import Sheaf.SixFunctors.IntegralLisseLocalization
import Sheaf.SixFunctors.IntegralLisseReductionNormalized
import Sheaf.SixFunctors.IntegralLisseTowerEffective

/-!
# Integral lisse modules and their normalized reduction towers

Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(1),
pp. 58--59 (blueprint: lem-sfb-integral-lisse-reduction-equivalence).

The finite coefficient sheaves are first presented as continuous functions into the quotient
rings, with their quotient topology. The statement identifies these with constant sheaves.
Towers are written in the integral module category by restriction of scalars. Normalization
is the cokernel universal property for multiplication by the relevant power of the uniformizer;
this is precisely the induced sheaf tensor quotient, not invertibility of the transition itself.
-/


@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Integral lisse modules and normalized positive reduction towers are canonically equivalent,
with the coefficient identities, inverse-limit quasi-inverse, and natural unit and counit.
Source: Bhatt--Scholze, Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(1), pp. 58--59
(blueprint: lem-sfb-integral-lisse-reduction-equivalence).

Proof: identify finite constant sheaves with continuous finite coefficient functions.
Use the normalized profinite integer tower for the coefficient limit, the sectionwise
coefficient quotient calculation for scalar cokernels, and bounded-denominator descent
for the localization colimit. Construct the functor by actual scalar cokernels. Its
normalization and completeness follow from finite free local charts and descent.
Compatible local bases of a normalized tower identify its actual limit locally with a
finite free integral module; the limit comparison equations and preservation of cokernels
on slices show that each projection is the prescribed scalar quotient. These calculations
give full faithfulness and essential surjectivity of the fixed cokernel functor. Transport
the complete quotient cone along the equivalence counit, and use quotient naturality and
the triangle identity to prove all completion and unit/counit projection equations. -/
theorem integral_lisse_reduction_equivalence (l : ℕ) [Fact l.Prime] (E : Type (u + 1))
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u}) :
    Nonempty (IntegralLisseReductionEquivalence l E X) := by
  let ht := fun M ↦ (integralLisseCokernel_complete l E X M).1
  let hc := fun M ↦ (integralLisseCokernel_complete l E X M).2
  let R := integralLisseReductionFunctor l E X ht
  let ff := integralLisseReductionFunctor_fullyFaithful l E X ht hc
  have : R.Full := ff.full
  have : R.Faithful := ff.faithful
  have : R.EssSurj := integralLisseReductionFunctor_essSurj l E X ht
    (integralLisseTower_effective l E X)
  have : R.IsEquivalence := {}
  let e := R.asEquivalence
  let q := fun M : IntegralLisseModule l E X ↦ integralLisseCokernelCone l E X M.obj
  let c := fun F : IntegralReductionTower l E X ↦
    q (e.inverse.obj F) ≫ (e.counitIso.hom.app F).hom
  have qnat {M N : IntegralLisseModule l E X} (f : M ⟶ N) (n : ℕ) :
      f.hom ≫ (q N).app (op n) =
        (q M).app (op n) ≫ (e.functor.map f).hom.app (op n) :=
    integralLisseCokernelCone_natural l E X f.hom n
  refine ⟨{
    finiteConstant := fun n ↦ (integralLisseFiniteConstant_exists l E X n).choose
    finiteConstant_sections := ?_
    coefficientCone := integralLisseCoefficientCone l E X
    coefficientCone_app := fun _ ↦ rfl
    coefficientLimit := (integralLisseCoefficient_isLimit l E X).some
    coefficientQuotient := integralLisseCoefficient_quotients l E X
    localizationCocone := integralLisseLocalizationCocone l E X
    localizationPoint := Iso.refl _
    localization_app := fun _ ↦ Category.comp_id _
    localizationColimit := (integralLisseLocalization_isColimit l E X).some
    equivalence := e
    reduction := q
    reductionQuotient := fun M ↦ integralLisseCokernelCone_quotient l E X M.obj
    reduction_natural := qnat
    completion := c
    completionLimit := ?_
    completion_natural := ?_
    unit_projection := ?_
    counit_projection := fun _ _ ↦ rfl }⟩
  · intro n U a
    exact (integralLisseFiniteConstant_exists l E X n).choose_spec U a
  · intro F
    exact (IsLimit.postcomposeHomEquiv
      ((ObjectProperty.ι (IsIntegralReductionTower l E X)).mapIso (e.counitIso.app F))
      (Cone.mk _ (q (e.inverse.obj F)))).symm (hc (e.inverse.obj F)).some
  · intro F G f n
    change (e.inverse.map f).hom ≫
        ((q (e.inverse.obj G)).app (op n) ≫ (e.counitIso.hom.app G).hom.app (op n)) =
      ((q (e.inverse.obj F)).app (op n) ≫ (e.counitIso.hom.app F).hom.app (op n)) ≫
        f.hom.app (op n)
    rw [← Category.assoc, qnat, Category.assoc, Category.assoc]
    congr 1
    exact congrArg (fun g ↦ g.hom.app (op n)) (e.counitIso.hom.naturality f)
  · intro M n
    change (e.unitIso.hom.app M).hom ≫
        ((q (e.inverse.obj (e.functor.obj M))).app (op n) ≫
          (e.counitIso.hom.app (e.functor.obj M)).hom.app (op n)) = _
    have hn := qnat (e.unitIso.hom.app M) n
    have ht := congrArg (fun f ↦ f.hom.app (op n)) (e.functor_unitIso_comp M)
    change (e.functor.map (e.unitIso.hom.app M)).hom.app (op n) ≫
      (e.counitIso.hom.app (e.functor.obj M)).hom.app (op n) = 𝟙 _ at ht
    calc
      _ = ((e.unitIso.hom.app M).hom ≫
          (q (e.inverse.obj (e.functor.obj M))).app (op n)) ≫
          (e.counitIso.hom.app (e.functor.obj M)).hom.app (op n) :=
        (Category.assoc _ _ _).symm
      _ = ((q M).app (op n) ≫
          (e.functor.map (e.unitIso.hom.app M)).hom.app (op n)) ≫
          (e.counitIso.hom.app (e.functor.obj M)).hom.app (op n) :=
        congrArg (fun g ↦ g ≫
          (e.counitIso.hom.app (e.functor.obj M)).hom.app (op n)) hn
      _ = _ := by
        rw [Category.assoc, ht]
        exact Category.comp_id _

end AlgebraicGeometry.ProEtale
