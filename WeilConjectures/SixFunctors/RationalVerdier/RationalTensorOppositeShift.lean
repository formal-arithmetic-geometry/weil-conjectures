/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
public import WeilConjectures.SmoothPurity.IntegralSystemRealization.IntegralOperationShiftData
public import Mathlib.CategoryTheory.Localization.Prod
import all WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Cancellation of opposite shifts in the recorded rational tensor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures.RationalVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] integralCompletedTensor rationalDerivedTensor
attribute [local implicit_reducible] constructibleIntegralTensor

/-- The completed integral tensor cancels a source shift against a target shift,
using the fixed right-slot map first and the fixed left-slot map second. -/
def integralOppositeShift (K P : sfIntegralConstructibleCategory l E X) (n : ℤ) :
    (integralTensor D l hl X E).obj (K⟦-n⟧, P⟦n⟧) ≅
      (integralTensor D l hl X E).obj (K, P) :=
  let I := (sfIntegralConstructible l E X).ι
  ObjectProperty.isoMk _
    ((integralCompletedTensor l E X).mapIso
        (Iso.prod ((I.commShiftIso (-n)).app K) ((I.commShiftIso n).app P)) ≪≫
      ((IntegralSystemRealization.tensorShifts l E).integralRight X n).app
        (K.obj⟦-n⟧, P.obj) ≪≫
      (shiftFunctor _ n).mapIso
        (((IntegralSystemRealization.tensorShifts l E).integralLeft X (-n)).app
          (K.obj, P.obj)) ≪≫
      (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).app
        ((integralCompletedTensor l E X).obj (K.obj, P.obj)))

/-- Integral tensor cancellation is natural in both variables. -/
theorem integralOppositeShift_naturality
    {K L P Q : sfIntegralConstructibleCategory l E X}
    (f : K ⟶ L) (g : P ⟶ Q) (n : ℤ) :
    (integralTensor D l hl X E).map (Prod.mkHom (f⟦-n⟧') (g⟦n⟧')) ≫
        (integralOppositeShift D l hl X E L Q n).hom =
      (integralOppositeShift D l hl X E K P n).hom ≫
        (integralTensor D l hl X E).map (Prod.mkHom f g) := by
  let I := (sfIntegralConstructible l E X).ι
  let T := integralCompletedTensor l E X
  let r := (IntegralSystemRealization.tensorShifts l E).integralRight X n
  let a := (IntegralSystemRealization.tensorShifts l E).integralLeft X (-n)
  apply I.map_injective
  dsimp only [integralOppositeShift]
  change T.map (Prod.mkHom (I.map (f⟦-n⟧')) (I.map (g⟦n⟧'))) ≫
    (T.map (Prod.mkHom ((I.commShiftIso (-n)).hom.app L)
      ((I.commShiftIso n).hom.app Q)) ≫ r.hom.app (L.obj⟦-n⟧, Q.obj) ≫
      (shiftFunctor _ n).map (a.hom.app (L.obj, Q.obj)) ≫
      (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).hom.app (T.obj (L.obj, Q.obj))) =
    (T.map (Prod.mkHom ((I.commShiftIso (-n)).hom.app K)
      ((I.commShiftIso n).hom.app P)) ≫ r.hom.app (K.obj⟦-n⟧, P.obj) ≫
      (shiftFunctor _ n).map (a.hom.app (K.obj, P.obj)) ≫
      (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).hom.app (T.obj (K.obj, P.obj))) ≫
        T.map (Prod.mkHom f.hom g.hom)
  have h₁ := (I.commShiftIso (-n)).hom.naturality f
  have h₂ := (I.commShiftIso n).hom.naturality g
  have hr := r.hom.naturality (Prod.mkHom (f.hom⟦-n⟧') g.hom)
  have ha := a.hom.naturality (Prod.mkHom f.hom g.hom)
  have hz := (shiftFunctorCompIsoId _ (-n) n (neg_add_cancel n)).hom.naturality
    (T.map (Prod.mkHom f.hom g.hom))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.id_map] at h₁ h₂ hr ha hz
  change T.map (Prod.mkHom (I.map (f⟦-n⟧')) (I.map (g⟦n⟧'))) ≫ _ = _
  rw [← T.map_comp_assoc]
  simp only [prod_comp]
  rw [h₁, h₂]
  have hp : Prod.mkHom
      (((I.commShiftIso (-n)).hom.app K) ≫ (f.hom⟦-n⟧'))
      (((I.commShiftIso n).hom.app P) ≫ (g.hom⟦n⟧')) =
      Prod.mkHom ((I.commShiftIso (-n)).hom.app K) ((I.commShiftIso n).hom.app P) ≫
        Prod.mkHom (f.hom⟦-n⟧') (g.hom⟦n⟧') := by rfl
  erw [hp, T.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hr]
  rw [← (shiftFunctor _ n).map_comp_assoc, ha, (shiftFunctor _ n).map_comp,
    Category.assoc, hz]

/-- The rational tensor has the recorded integral object formula. -/
theorem tensor_object (K P : sfRationalConstructibleCategory l E X) :
    (tensor D l hl X E).obj (K, P) =
      (sfRationalConstructibleLocalization l E X).obj
        ((integralTensor D l hl X E).obj (K.obj, P.obj)) := by
  letI := units D l hl X
  simpa only [tensor, rationalDerivedTensor, integralTensor,
    sfRationalConstructibleLocalization, ScalarLocalization.localization] using
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 (K, P)

/-- The binary localization comparison is fixed by the tensor's pure-map formula. -/
def tensorLocalizationComparison :
    (sfRationalConstructibleLocalization l E X).prod
        (sfRationalConstructibleLocalization l E X) ⋙ tensor D l hl X E ≅
      integralTensor D l hl X E ⋙ sfRationalConstructibleLocalization l E X := by
  let Q := sfRationalConstructibleLocalization l E X
  refine NatIso.ofComponents (fun K ↦ eqToIso
    (tensor_object D l hl X E (Q.obj K.1) (Q.obj K.2))) ?_
  intro K M f
  apply (by
    intro C hC A A' B B' hA hB f g h
    cases hA; cases hB; cases h
    simp : ∀ {C : Type _} [Category C] {A A' B B' : C}
      (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'},
      HEq f g → f ≫ eqToHom hB = eqToHom hA ≫ g)
    (tensor_object D l hl X E (Q.obj K.1) (Q.obj K.2))
    (tensor_object D l hl X E (Q.obj M.1) (Q.obj M.2))
  letI := units D l hl X
  obtain ⟨b, hb, hp⟩ := (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
    (Q.obj K.1) (Q.obj M.1) (Q.obj K.2) (Q.obj M.2)
  change HEq ((tensor D l hl X E).map (Prod.mkHom (Q.map f.1) (Q.map f.2))) _
  unfold tensor rationalDerivedTensor
  change HEq ((rationalDerivedTensor_existsUnique l E X).exists.choose.map
    (Prod.mkHom (Q.map f.1) (Q.map f.2))) _
  rw [hb]
  change HEq (b (Q.map f.1) (Q.map f.2))
    ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ[
      Padic.coefficientExtensionIntegers l E]
      (integralTensor D l hl X E).map (Prod.mkHom f.1 f.2))
  have hh := hp f.1 f.2 1 1
  simp only [one_mul] at hh
  convert hh using 1
  dsimp [Q, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    integralTensor]
  rfl

/-- Opposite integral tensor shifts form a natural isomorphism. -/
def integralOppositeShiftIso (n : ℤ) :
    (shiftFunctor (sfIntegralConstructibleCategory l E X) (-n)).prod
        (shiftFunctor (sfIntegralConstructibleCategory l E X) n) ⋙
        integralTensor D l hl X E ≅ integralTensor D l hl X E :=
  NatIso.ofComponents (fun K ↦ integralOppositeShift D l hl X E K.1 K.2 n)
    (fun f ↦ integralOppositeShift_naturality D l hl X E f.1 f.2 n)

/-- Localization identifies both integral tensor shifts with the given rational shifts. -/
def tensorShiftLocalization (n : ℤ) :
    (shiftFunctor (sfIntegralConstructibleCategory l E X) (-n)).prod
        (shiftFunctor (sfIntegralConstructibleCategory l E X) n) ⋙
        (sfRationalConstructibleLocalization l E X).prod
          (sfRationalConstructibleLocalization l E X) ≅
      (sfRationalConstructibleLocalization l E X).prod
          (sfRationalConstructibleLocalization l E X) ⋙
        (shiftFunctor (sfRationalConstructibleCategory l E X) (-n)).prod
          (shiftFunctor (sfRationalConstructibleCategory l E X) n) :=
  NatIso.ofComponents (fun K ↦ Iso.prod
    (((sfRationalConstructibleLocalization l E X).commShiftIso (-n)).app K.1)
    (((sfRationalConstructibleLocalization l E X).commShiftIso n).app K.2)) (by
      intro K M f
      apply Prod.hom_ext
      · exact ((sfRationalConstructibleLocalization l E X).commShiftIso (-n)).hom.naturality f.1
      · exact ((sfRationalConstructibleLocalization l E X).commShiftIso n).hom.naturality f.2)

/-- The raw coefficient localization has the universal property used by binary descent. -/
theorem rawLocalization_isLocalization :
    (sfRationalConstructibleLocalization l E X).IsLocalization
      (Rationalization.W (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
        (sfIntegralConstructibleCategory l E X)) :=
  ScalarLocalization.semilinear_localization_isLocalization
    (Padic.coefficientExtensionIntegers l E) (sfIntegralConstructibleCategory l E X)
    (Padic.coefficientExtensionUniformizer l E)

/-- Descend the specified integral cancellation through binary scalar localization. -/
def oppositeShiftIso (n : ℤ) :
    (shiftFunctor (sfRationalConstructibleCategory l E X) (-n)).prod
        (shiftFunctor (sfRationalConstructibleCategory l E X) n) ⋙
        tensor D l hl X E ≅ tensor D l hl X E := by
  let Q := sfRationalConstructibleLocalization l E X
  let W := Rationalization.W
    (Submonoid.powers (Padic.coefficientExtensionUniformizer l E))
    (sfIntegralConstructibleCategory l E X)
  letI : Q.IsLocalization W := rawLocalization_isLocalization l X E
  let A := (shiftFunctor (sfIntegralConstructibleCategory l E X) (-n)).prod
    (shiftFunctor (sfIntegralConstructibleCategory l E X) n)
  let B := (shiftFunctor (sfRationalConstructibleCategory l E X) (-n)).prod
    (shiftFunctor (sfRationalConstructibleCategory l E X) n)
  let e : Q.prod Q ⋙ (B ⋙ tensor D l hl X E) ≅ Q.prod Q ⋙ tensor D l hl X E :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (tensorShiftLocalization l X E n).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft A (tensorLocalizationComparison D l hl X E) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (integralOppositeShiftIso D l hl X E n) Q ≪≫
      (tensorLocalizationComparison D l hl X E).symm
  exact (Localization.fullyFaithfulWhiskeringLeft (Q.prod Q) (W.prod W)
    (sfRationalConstructibleCategory l E X)).preimageIso e

/-- The component of the descended opposite tensor-shift cancellation. -/
def oppositeShift (K P : sfRationalConstructibleCategory l E X) (n : ℤ) :
    (tensor D l hl X E).obj (K⟦-n⟧, P⟦n⟧) ≅
      (tensor D l hl X E).obj (K, P) :=
  (oppositeShiftIso D l hl X E n).app (K, P)

/-- Cancellation is natural in its second rational argument. -/
theorem oppositeShift_naturality (K : sfRationalConstructibleCategory l E X)
    {P Q : sfRationalConstructibleCategory l E X} (f : P ⟶ Q) (n : ℤ) :
    (tensor D l hl X E).map (Prod.mkHom (𝟙 (K⟦-n⟧)) (f⟦n⟧')) ≫
        (oppositeShift D l hl X E K Q n).hom =
      (oppositeShift D l hl X E K P n).hom ≫
        (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) := by
  simpa only [Functor.comp_map, Functor.prod_map, (shiftFunctor _ (-n)).map_id,
    oppositeShift, Iso.app_hom] using
    (oppositeShiftIso D l hl X E n).hom.naturality (Prod.mkHom (𝟙 K) f)

/-- The quadratic sign converting tensor cancellation into the coherent reversed
Hom shift; right-slot cancellation is performed before left-slot cancellation. -/
def signedOppositeShift (K P : sfRationalConstructibleCategory l E X) (n : ℤ) :
    (tensor D l hl X E).obj (K⟦-n⟧, P⟦n⟧) ⟶
      (tensor D l hl X E).obj (K, P) :=
  (n * (n - 1) / 2).negOnePow • (oppositeShift D l hl X E K P n).hom

/-- The sign in reversed Hom cancellation preserves naturality.
Source: blueprint thm-coef-qbar-verdier steps 3--4 and Stacks Tags 0A8X, 0941.
(blueprint: lem-coef-rational-tensor-opposite-shift-X3).
Proof: compose the recorded right-slot shift with the shifted left-slot shift
and the shift-cancellation isomorphism. Each is natural, so their composite is
natural in both integral arguments. The tensor's integral object and pure-map
formulas give its binary localization comparison. Full faithfulness of binary
localization descends the integral cancellation to a rational natural
isomorphism. Apply its naturality to (identity,f), and multiply by the common
integer unit (-1)^(n(n-1)/2). Bilinearity moves that unit through compositions. -/
theorem signedOppositeShift_naturality (K : sfRationalConstructibleCategory l E X)
    {P Q : sfRationalConstructibleCategory l E X} (f : P ⟶ Q) (n : ℤ) :
    (tensor D l hl X E).map (Prod.mkHom (𝟙 (K⟦-n⟧)) (f⟦n⟧')) ≫
        signedOppositeShift D l hl X E K Q n =
      signedOppositeShift D l hl X E K P n ≫
        (tensor D l hl X E).map (Prod.mkHom (𝟙 K) f) := by
  simpa only [signedOppositeShift, Linear.comp_units_smul, Linear.units_smul_comp] using
    congrArg ((n * (n - 1) / 2).negOnePow • ·)
      (oppositeShift_naturality D l hl X E K f n)

end WeilConjectures.RationalVerdier
