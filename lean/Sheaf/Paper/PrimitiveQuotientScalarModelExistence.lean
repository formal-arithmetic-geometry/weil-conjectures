/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
import Sheaf.Paper.CoefficientExtensionReductionModel
import Sheaf.Paper.TransportedReductionScalarNormalized

/-! # Primitive quotient scalar model existence

This is the scalar conjunct split from
`primitiveQuotientRealizationComparisons`.
(blueprint: lem-trf-primitive-quotient-realization-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe t u c v r w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
open scoped ChangeOfRings

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The balanced finite-level association and the normalized Roos comparison
produce the required scalar realization. Source: Stacks 03EK, 06YY and 0941.
Proof: choose the flat-term K-flat representative supplied by the reduction
calculus. At each quotient level, use the balanced association
`(x tensor a) tensor b ↦ x tensor (a*b)` and its unit-inserting inverse. These
maps form a strict system map because the quotient transitions reduce the same
product. The system is K-flat by component evaluation, so ordinary scalar change
computes derived scalar change. Apply the fixed normalized Roos comparison and
descend the construction from K-flat representatives to the ambient derived
category. The generator and transition equations give the required normalization.
This theorem is the scalar conjunct split from
`primitiveQuotientRealizationComparisons`.
(blueprint: lem-trf-primitive-quotient-scalar-model-existence) -/
private theorem globalUnit_of_residueUnits (l : ℕ) {W : Scheme.{t}}
    (hl : ∀ x : W, IsUnit (l : W.residueField x)) : IsUnit (l : Γ(W, ⊤)) := by
  apply W.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have h : IsUnit (l : W.presheaf.stalk x) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).1
    simpa only [map_natCast] using (hl x).ne_zero
  simpa only [map_natCast] using h

private noncomputable def scalarModelIso'
    {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasSheafify J AddCommGrpCat.{r}]
    {R S : Sheaf J CommRingCat.{r}} {φ ψ : R ⟶ S}
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w₂}
      (SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (h : φ = ψ) (A : SheafOfModules.DerivedChangeOfRingsCochainModel φ)
    (B : SheafOfModules.DerivedChangeOfRingsCochainModel ψ) : A.T ≅ B.T := by
  subst ψ
  let a : A.E ≅ B.E := NatIso.ofComponents
    (fun M ↦ eqToIso ((A.obj_eq M).trans (B.obj_eq M).symm)) (by
      intro M N f
      simp only [eqToIso.hom, A.map_eq, B.map_eq, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans])
  letI := A.universal
  letI := B.universal
  exact Functor.leftDerivedNatIso A.T B.T A.ε B.ε
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex a (.up ℤ)) DerivedCategory.Q)

/-- The scalar realization iso exists before imposing the quotient-generator
normalization. Source: Stacks 06YY and 0941; this is the realization portion
of the primitive quotient construction.
(blueprint: lem-trf-primitive-quotient-scalar-model-existence) -/
theorem primitiveQuotientScalarModelRealization
    (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SW : CoefficientDerivedSystemCalculus l E W)
    (_ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (integralScalarExtensionOfUniverses l E L ι W ≅
      SW.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W ⋙
        coefficientSequenceLimit l L W) := by
  obtain ⟨SL, _⟩ := coefficientDerivedSystemEvaluationCalculus l L W
  obtain ⟨D⟩ := SemilinearSections.semilinearDerivedSections.{t + 1, t, u}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
  let A : CoefficientExtensionSystems l E L ι W :=
    D.coefficientExtension (integralCoefficientCommRingSheaf l L W)
      (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W)
  have hφ : SemilinearSections.systemMap.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W)
      (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W) =
        integralComparisonSequenceScalarMap l E L ι W := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    exact (SemilinearSections.systemMap_existsUnique.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W)
      (integralCoefficientCommRingSheaf l L W)
      (coefficientSequenceCommRingTransition l L W)
      (integralScalarQuotientSheafMap l E L ι W)
      (coefficientExtensionQuotient_naturality l E L ι W)).exists.choose_spec
        U.unop.1 (Opposite.op U.unop.2)
  let : HasSheafify (coefficientSequenceTopology (Scheme.ProEt.topology W))
      AddCommGrpCat.{max u (t + 1)} :=
    SemilinearSections.abelianSheafify.{t + 1, t, max u (t + 1)}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
  let : (coefficientSequenceTopology (Scheme.ProEt.topology W)).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
    SemilinearSections.locallyBijective.{t + 1, t, max u (t + 1)}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
  let a : A.scalar.T ≅ integralComparisonDerivedSequenceScalar l E L ι W :=
    scalarModelIso' hφ A.scalar.model
      (integralComparisonSequenceScalarModel l E L ι W)
  have hl : IsUnit (l : Γ(W, ⊤)) := globalUnit_of_residueUnits l _hlW
  obtain ⟨d⟩ := coefficientExtensionReductionModel l E L ι W SW SL A hl
  let e : integralScalarExtensionOfUniverses l E L ι W ≅
      SW.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W ⋙
        coefficientSequenceLimit l L W :=
    d.completion.symm ≪≫
      Functor.isoWhiskerLeft SW.reduction
        (Functor.isoWhiskerRight a (coefficientSequenceLimit l L W))
  exact ⟨e⟩

/-- The canonical realization satisfies the quotient-generator normalization.
Source: Stacks 06YY and 0941; the balanced quotient association and normalized
Roos comparison on simultaneous flat-term K-flat presentations.
(blueprint: lem-trf-primitive-quotient-scalar-model-normalization)
Proof: on each finite quotient, transpose the balanced map through the
scalar-extension adjunction. Its value on 1 tensor x is the prescribed tensor
section. The maps commute with quotient transitions and cochain differentials;
the strict Roos comparison then gives the displayed derived equation. Descent
from K-flat representatives and naturality extend the equation to every
coherent presentation. -/
theorem primitiveQuotientScalarModelNormalization
    (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρW : IntegralComparisonRoosModel l L W)
    (realization : integralScalarExtensionOfUniverses l E L ι W ≅
      SW.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι W ⋙
        coefficientSequenceLimit l L W) :
    IsIntegralComparisonScalarNormalized l E L ι W SW ρW realization := by
  sorry

theorem primitiveQuotientScalarModelExistence
    (W : Scheme.{t})
    (_hlW : ∀ x : W, IsUnit (l : W.residueField x))
    (SW : CoefficientDerivedSystemCalculus l E W)
    (ρW : IntegralComparisonRoosModel l L W) :
    Nonempty (IntegralComparisonScalarModel l E L ι W SW ρW) := by
  obtain ⟨realization⟩ := primitiveQuotientScalarModelRealization l E L ι W _hlW SW ρW
  exact ⟨⟨realization, primitiveQuotientScalarModelNormalization l E L ι W _hlW SW ρW
    realization⟩⟩

end WeilConjectures
