/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.RingStageAssembly.ExceptionalRingStageAssemblyData
import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ExceptionalCommonStageFromRational
import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Field stages extending a fixed ring-stage assembly

Localize the supplied integral adjunctions, then descend over common finite subfields.
The ring-stage operations, scalars and mates remain the supplied input.

## References

* [Zheng, Lemma 5.22, Proposition 5.24 and Constructions 6.2 and 6.6]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

attribute [local instance] constructionInclusionShift

section Linearity
variable (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (A : RingStageAssembly.{u, v} l Ω D hl (f := f))
private theorem integral_linear (c : Compactification f) (E : FieldStage.{max u v} l) :
    (A.operation c (.integral E)).F.Linear (Padic.coefficientExtensionIntegers l E.carrier) := by
  let O := Padic.coefficientExtensionIntegers l E.carrier
  let IX := PurCompactSupport.finiteTorIntegralInclusion l E.carrier X
  let IY := PurCompactSupport.finiteTorIntegralInclusion l E.carrier Y
  let P := sfCompactSupportFiniteIntegralFunctor l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier
  let : IX.Linear O := { map_smul := fun _ _ ↦ rfl }
  let : IY.Linear O := { map_smul := fun _ _ ↦ rfl }
  let : P.Linear O := (sfCompactSupportFiniteIntegralFunctor_linear l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) c E.carrier).2
  let : ((A.operation c (.integral E)).F ⋙ IY).Linear O :=
    Functor.linear_of_iso O (A.integralLeft c E).symm
  constructor
  intro K L h a
  have he := ((A.operation c (.integral E)).F ⋙ IY).map_smul a h
  exact ObjectProperty.hom_ext _ (congrArg (fun t ↦ t.hom) he)
end Linearity

private theorem representativeAction_of_transition
    {A B C D E H : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category H]
    (Fi : A ⥤ C) (Fj : B ⥤ D) (FΩ : E ⥤ H)
    (TX : A ⥤ B) (TY : C ⥤ D) (IXi : A ⥤ E) (IXj : B ⥤ E)
    (IYi : C ⥤ H) (IYj : D ⥤ H)
    (q : Fi ⋙ TY ≅ TX ⋙ Fj)
    (qi : Fi ⋙ IYi ≅ IXi ⋙ FΩ) (qj : Fj ⋙ IYj ≅ IXj ⋙ FΩ)
    (tauX : TX ⋙ IXj ≅ IXi) (tauY : TY ⋙ IYj ≅ IYi)
    (ht : ∀ K : A,
      qi.hom.app K ≫ FΩ.map (tauX.inv.app K) =
        tauY.inv.app (Fi.obj K) ≫ IYj.map (q.hom.app K) ≫ qj.hom.app (TX.obj K)) :
    representativeAction Fi Fj FΩ TX TY IXi IXj IYi IYj q qi qj tauX tauY := by
  intro K L a
  have hn := qj.hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [FΩ.map_comp]
  apply (cancel_epi (qi.hom.app K)).1
  simp only [← Category.assoc]
  rw [ht K]
  simp only [Category.assoc]
  rw [← hn]
  simp

/-- Extend fixed ring-stage operations by raw rational localization and common fields.
Only field operations and field comparisons are outputs; the supplied finite/integral
adjunctions and ring scalar maps are not reconstructed or replaced. -/
theorem exists_field_stage_completion (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
    {X Y : Scheme.{max u v}} (f : X ⟶ Y)
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (A : RingStageAssembly.{u, v} l Ω D hl (f := f)) :
    ∃ (rational : ∀ (_c : Compactification f) (E : FieldStage.{max u v} l),
        Operation.{u, v} l Ω X Y (.rational E))
      (closed : ∀ _c : Compactification f, Operation.{u, v} l Ω X Y .closed)
      (rationalLeft : ∀ (c : Compactification f) (E : FieldStage.{max u v} l),
        (rational c E).F ≅
          sfCompactSupportFiniteFunctor l D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
            c E.carrier),
      let R := A.complete l Ω D hl rational closed rationalLeft
      ∃ F : CoefficientConstructionFields.{u, v} l Ω D hl R,
        ∃ M : CoefficientConstructionCommon.{u, v} l Ω D hl R F,
          (∀ (c d : Compactification f) (E : FieldStage.{max u v} l),
            (F.rationalizationComparison c E).shiftX =
              (F.rationalizationComparison d E).shiftX) ∧
          (∀ (c d : Compactification f) (E : FieldStage.{max u v} l),
            (F.rationalizationComparison c E).shiftY =
              (F.rationalizationComparison d E).shiftY) ∧
          (∀ (c : Compactification f) (E : FieldStage.{max u v} l)
            (K : C.{u, v} l Ω X (.integral E)),
            HEq ((F.rationalizationComparison c E).q.hom.app K)
              (𝟙 ((rationalization.{u, v} l Ω E Y).obj
                ((A.operation c (.integral E)).F.obj K)))) ∧
          (∀ (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω),
            (M.commonComparison c i).shiftX = (M.commonComparison d i).shiftX) ∧
          (∀ (c d : Compactification f) (i : AlgebraicallyClosedCoefficients.Index l Ω),
            (M.commonComparison c i).shiftY = (M.commonComparison d i).shiftY) := by
  have hlin (c : Compactification f) (E : FieldStage.{max u v} l) :
      (A.operation c (.integral E)).F.Linear
        (Padic.coefficientExtensionIntegers l E.carrier) :=
    integral_linear l Ω D hl A c E
  have hright (c : Compactification f) (E : FieldStage.{max u v} l) :
      (A.operation c (.integral E)).G.Linear
        (Padic.coefficientExtensionIntegers l E.carrier) := by
    let := hlin c E
    exact (A.operation c (.integral E)).adjunction.right_adjoint_linear
  obtain ⟨P⟩ := exists_rational_stage_localization l Ω D hl A hlin hright
  obtain ⟨Q⟩ := exists_common_stage_descent l Ω D hl A P
  let R := A.complete l Ω D hl P.operation Q.operation P.left
  let F : CoefficientConstructionFields.{u, v} l Ω D hl R :=
    P.fields l Ω D hl Q.operation
  let M : CoefficientConstructionCommon.{u, v} l Ω D hl R F := {
    commonComparison := Q.comparison
    common_normalized := Q.normalized
    common_morphism_normalized := fun c i j h ↦
      representativeAction_of_transition _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (Q.transition c i j h) }
  exact ⟨P.operation, Q.operation, P.left, F, M,
    P.shiftX, P.shiftY, P.identity, Q.shiftX, Q.shiftY⟩

end WeilConjectures.ConstructibleExceptionalCoefficients
