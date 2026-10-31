/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorStageComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorCommonComponent
import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorIntegralNaturality
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import Mathlib.CategoryTheory.Localization.Prod

/-! # Naturality of the explicit completed tensor components

Source: BS Remark 6.8.15; HRS Lemma 7.9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.AdicQbarRealization.ordinary
  WeilConjectures.rationalDerivedTensor
  WeilConjectures.commonStageDerivedTensor

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
  (R : LocallyFiniteAdicRealization.Realization l X)
  [∀ x : X, Invertible (l : X.residueField x)]
  (closed : CoefficientClosedStructure (ambientHom l X R))
  (models : CoefficientTensorModels.{u + 1, u + 1, u}
    (ProEt.topology X) (ring l X R) closed)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.Stage
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5

private theorem descend_iso
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    {F G : B ⥤ D} (e : q ⋙ F ≅ q ⋙ G) :
    ∃ a : F ≅ G, ∀ P, a.hom.app (q.obj P) = e.hom.app P := by
  let ff := Localization.fullyFaithfulWhiskeringLeft q W D
  exact ⟨ff.preimageIso e, fun P ↦ congr_app (ff.map_preimage e.hom) P⟩

private theorem rational_component_iso
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E) :
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    let T := rationalDerivedTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
    ∃ a : (I.prod I) ⋙ ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor ≅
        T ⋙ I ⋙ ordinary l X R,
      ∀ P, a.hom.app P =
        (completedTensorIntegralComponent l X R closed models E N P.1.obj P.2.obj).hom := by
  let C := sfIntegralConstructibleCategory l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let q := sfRationalConstructibleLocalization l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let I := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let T := rationalDerivedTensor l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let F := (I.prod I) ⋙ ((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor
  let G := T ⋙ I ⋙ ordinary l X R
  let : ∀ n : ℤ, (shiftFunctor C n).Additive := fun n ↦ inferInstance
  let : ∀ n : ℤ, (shiftFunctor C n).Linear
      (Padic.coefficientExtensionIntegers l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)) :=
    (sfIntegralConstructible_linear l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X).2.2.2
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E))) C
  have : q.IsLocalization W := ScalarLocalization.semilinear_localization_isLocalization
    (Padic.coefficientExtensionIntegers l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)) C _
  obtain ⟨e, he⟩ := completedTensorIntegralComponent_natural_iso l X R closed models E N
  obtain ⟨a, ha₀⟩ := descend_iso (q.prod q) (W.prod W) (F := F) (G := G) e
  have ha (P) : a.hom.app P =
      (completedTensorIntegralComponent l X R closed models E N P.1.obj P.2.obj).hom := by
    exact (ha₀ (P.1.obj, P.2.obj)).trans (he _)
  exact ⟨a, ha⟩

private theorem pasted_component_naturality
    {C D : Type*} [Category* C] [Category* D] {F G H : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : ∀ P, F.obj P ≅ G.obj P)
    (hc : ∀ P, a.hom.app P = (c P).hom) {P Q : C} (f : P ⟶ Q) :
    F.map f ≫ (c Q ≪≫ b.app Q).hom = (c P ≪≫ b.app P).hom ≫ H.map f := by
  change F.map f ≫ ((c Q).hom ≫ b.hom.app Q) =
    ((c P).hom ≫ b.hom.app P) ≫ H.map f
  rw [← hc Q, ← hc P]
  exact (a ≪≫ b).hom.naturality f

attribute [local irreducible] ScalarLocalization.category sfIntegralConstructible

/-- At one fixed coefficient field the specified completed tensor components are natural.
Source: BS Definition 3.4.10 and Remark 6.8.15; HRS Proposition 5.2 and Lemma 7.9.
(blueprint: lem-sf-adic-completed-tensor-stage-naturality).

Proof: the integral component natural isomorphism is given by
completedTensorIntegralComponent_natural_iso. Each raw scalar localization is a
categorical localization at the rationalization morphism property. Their product
is therefore a localization, and full faithfulness of precomposition descends
the integral natural isomorphism. Every rational object is the localization of
its underlying integral object, so the descended components are exactly the
specified integral components. Whisker the existing natural inclusion tensor
comparison by ordinary, then paste it with this descended isomorphism. The generic
pasted_component_naturality lemma substitutes the component equations into this
natural square. This gives the displayed equation, including zero objects and
maps, coincident stages, and an empty scheme. -/
theorem completedTensorStageComponent_naturality
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (N : CompletedTensorFiniteModel l X R closed models E)
    {P Q : sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X ×
      sfRationalConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X}
    (f : P ⟶ Q) :
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := X) E
    (((ordinary l X R).prod (ordinary l X R)) ⋙ closed.tensor).map
        ((I.prod I).map f) ≫
        (completedTensorStageComponent l X R closed models E N Q.1 Q.2).hom =
      (completedTensorStageComponent l X R closed models E N P.1 P.2).hom ≫
        (commonStageDerivedTensor l (PadicAlgCl l) X ⋙ ordinary l X R).map
          ((I.prod I).map f) := by
  obtain ⟨a, ha⟩ := rational_component_iso l X R closed models E N
  unfold completedTensorStageComponent
  exact pasted_component_naturality a
    (Functor.isoWhiskerRight (commonInclusionTensorComparison l (PadicAlgCl l) X E)
      (ordinary l X R))
    (fun P ↦ completedTensorIntegralComponent l X R closed models E N P.1.obj P.2.obj) ha f

end WeilConjectures.AdicQbarRealization
