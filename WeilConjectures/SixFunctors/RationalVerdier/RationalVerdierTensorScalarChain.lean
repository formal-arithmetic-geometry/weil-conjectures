/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorCompletionCoordinates
import all Mathlib.CategoryTheory.Limits.HasLimits
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence

/-! # Representative calculations for tensor completion and scalar extension

Source: the normalized completion and tensor calculations in the blueprint proof of
lem-coef-integral-finite-extension, paragraphs 1 and 4.
(blueprint: lem-coef-rational-verdier-tensor-scalar-chain).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  integralOrdinaryScalar integralOrdinaryTensorSection scalarAdjunction
  integralCompletedTensor integralCompletedTensorComparison
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  scalarRoosMap integralOperationsRoosMap scalarTensorLevel scalarTensorTower
  towerTransitionEndomorphism CochainComplex.mappingCone CochainComplex.mappingCocone
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance 100000] integralOperationsCountableProducts
attribute [local implicit_reducible] integralOperationsTensorComplexFunctor
  Functor.mapHomologicalComplex
  completedOrdinaryScalarComplex coefficientTotalTensor

attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  integralOperationsTowerStep

attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
private theorem roos_scalar_coordinates
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ T) :
    (∀ n : ℕ, (scalarRoosMap F C ≫ integralOperationsRoosMap a) ≫
      CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫ Pi.π _ n =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫ Pi.π _ n) ≫
          a.app (op n)) ∧
    (∀ (n : ℕ) (i j : ℤ) (h : i + -1 = j),
      (scalarRoosMap F C ≫ integralOperationsRoosMap a).f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary T)).v i j h ≫
          (Pi.π (fun m ↦ T.obj (op m)) n).f j =
      F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j h ≫
        (Pi.π (fun m ↦ C.obj (op m)) n).f j) ≫ (a.app (op n)).f j) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hs := (scalarRoosMap_existsUnique F C).exists.choose_spec
  obtain ⟨hm₁, hm₂⟩ := IntegralAmbient.roosMap_coordinates a
  constructor
  · intro n
    rw [Category.assoc, reassoc_of% hm₁, Pi.map_π]
    simpa only [scalarRoosMap, scalarRoosBoundary, Functor.comp_obj, Category.assoc] using
      congrArg (fun f ↦ f ≫ a.app (op n)) (hs.1 n)
  · intro n i j hij
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [reassoc_of% (hm₂ i j hij)]
    have hp := congrArg (fun f ↦ f.f j)
      (Pi.map_π (fun m : ℕ ↦ a.app (op m)) n)
    simp only [HomologicalComplex.comp_f] at hp
    rw [hp]
    simpa only [scalarRoosMap, scalarRoosBoundary, Functor.comp_obj, Category.assoc] using
      congrArg (fun f ↦ f ≫ (a.app (op n)).f j) (hs.2 i j hij n)

private theorem chosen_spec {A : Sort*} {P : A → Prop}
    (h : ∃ a, P a) (a : A) (ha : a = h.choose) : P a :=
  ha.symm ▸ h.choose_spec

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (i : E →ₐ[Padic l] L) (X : Scheme.{u})

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

set_option maxHeartbeats 600000 in
-- The explicit total-tensor coordinate calculation elaborates several large model types.
omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))] in
attribute [-instance] IntegralAmbient.ambientCxCategory IntegralAmbient.ambientDCategory in
/-- The ordinary tensor augmentation commutes with the strict scalar tensor map.
Source: blueprint lem-coef-integral-finite-extension.proof.md, paragraph 1,
finite-free scalar extension and cofinal completion, with the tensor calculation
in paragraph 4.
(blueprint: lem-coef-rational-verdier-tensor-scalar-chain).

Proof: in every positive quotient coordinate, scalarRoosMap followed by the
strict tensor tower comparison sends 1 tensor (x tensor y) to the tensor of the
two scalar-extended quotient images. This is also the image under the ordinary
tensorator followed by the target tensor augmentation. The normalization of
completionChain supplies precisely these quotient maps. The shifted coordinate
of each augmentation is zero; scalarRoosMap and the Roos map of the strict tower
comparison are diagonal, so their composite still has zero shifted coordinate.
The scalar extension adjunction reduces equality to unit scalar generators.
Sheafification and the coproduct injections of signed total tensor reduce it to
homogeneous pure tensors. Product projections and the two mapping-fiber
coordinates then detect equality degree by degree. This calculation requires
no constructibility or invertibility of completion. -/
theorem tensor_completion_scalar_chain
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    ((integralOrdinaryScalar l E L i X).mapHomologicalComplex (.up ℤ)).map
        ((completionChain D l hl X E).app (P, Q)) ≫
      scalarTensorChain l E L i X P Q =
    (scalarOrdinaryTensorChain l E L i X).hom.app (P, Q) ≫
      (completionChain D l hl X L).app
        (((integralOrdinaryScalar l E L i X).mapHomologicalComplex (.up ℤ)).obj P,
          ((integralOrdinaryScalar l E L i X).mapHomologicalComplex (.up ℤ)).obj Q) := by
  let O := integralOrdinaryScalar l E L i X
  let S := O.mapHomologicalComplex (.up ℤ)
  let C := (integralOperationsTensorTowerFunctor l E X).obj (P, Q)
  let SP := S.obj P
  let SQ := S.obj Q
  let T := (integralOperationsTensorTowerFunctor l L X).obj (SP, SQ)
  let a := (scalarTensorTower l E L i X).app (P, Q)
  let χE : (constructibleTensorTotal l E X).obj (P, Q) ⟶
      integralOperationsRoos C :=
    (completionChain D l hl X E).app (P, Q)
  let χL : (constructibleTensorTotal l L X).obj (SP, SQ) ⟶
      integralOperationsRoos T :=
    (completionChain D l hl X L).app (SP, SQ)
  let α : S.obj ((constructibleTensorTotal l E X).obj (P, Q)) ⟶
      (constructibleTensorTotal l L X).obj (SP, SQ) :=
    (scalarOrdinaryTensorChain l E L i X).hom.app (P, Q)
  obtain ⟨hE, hEzero⟩ := tensor_completion_coordinates (l := l) (E := E) (X := X) (D := D)
    (hl := hl)
  obtain ⟨hL, hLzero⟩ := tensor_completion_coordinates (l := l) (E := L) (X := X) (D := D)
    (hl := hl)
  change S.map χE ≫ (scalarRoosMap O C ≫ integralOperationsRoosMap a) = α ≫ χL
  obtain ⟨hf, hz⟩ := roos_scalar_coordinates O C T a
  have first (n : ℕ) :
      S.map χE ≫ (scalarRoosMap O C ≫ integralOperationsRoosMap a) ≫
          CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫ Pi.π _ n =
        α ≫ χL ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫ Pi.π _ n := by
    rw [hf n, ← S.map_comp_assoc]
    apply HomologicalComplex.hom_ext
    intro k
    apply ((scalarAdjunction l E L i X).homEquiv _ _).injective
    erw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u} P Q k
    intro p q hpq U x y
    subst k
    change ((a.app (op n)).f (p + q)).val.app U
        ((O.map ((χE ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
          Pi.π _ n).f (p + q))).val.app U
          (((scalarAdjunction l E L i X).unit.app _).val.app U
            (constructibleTensorTotalSection l E X P Q p q U x y))) =
      ((χL ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary T) ≫
        Pi.π _ n).f (p + q)).val.app U
          ((α.f (p + q)).val.app U
            (((scalarAdjunction l E L i X).unit.app _).val.app U
              (constructibleTensorTotalSection l E X P Q p q U x y)))
    erw [scalarAdjunction_unit, scalar_map_tensor]
    have hE' := hE P Q p q n U x y
    change ((χE ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
      Pi.π _ n).f (p + q)).val.app U _ = _ at hE'
    rw [hE']
    have ha : a.app (op n) = (scalarTensorLevel l E L i X n).app (P, Q) :=
      by simpa only [a, scalarTensorTower] using
        (scalarTensorTower_existsUnique l E L i X).exists.choose_spec P Q n
    rw [ha]
    have hlevel := chosen_spec (scalarTensorLevel_existsUnique l E L i X n).exists
      (scalarTensorLevel l E L i X n) (by unfold scalarTensorLevel; rfl)
    erw [hlevel P Q p q U x y]
    erw [(scalarOrdinaryTensorChain_existsUnique l E L i X).exists.choose_spec]
    exact (hL SP SQ p q n U
      (integralOrdinaryTensorSection l E L i X (P.X p) U 1 x)
      (integralOrdinaryTensorSection l E L i X (Q.X q) U 1 y)).symm
  apply HomologicalComplex.hom_ext
  intro k
  apply cocone_degree_ext (scalarRoosBoundary T)
  · apply complexProduct_hom_ext
    intro n
    exact congrArg (fun z ↦ z.f k) (first n)
  · apply complexProduct_hom_ext
    intro n
    simp only [HomologicalComplex.comp_f, Category.assoc]
    change (S.map χE).f k ≫
      (scalarRoosMap O C ≫ integralOperationsRoosMap a).f k ≫ _ ≫ _ = _
    rw [hz n k (k - 1) (by omega)]
    change O.map (χE.f k) ≫ O.map
        ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v k (k - 1) (by omega) ≫
          (Pi.π (fun m ↦ C.obj (op m)) n).f (k - 1)) ≫ (a.app (op n)).f (k - 1) =
      α.f k ≫ χL.f k ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary T)).v k (k - 1) (by omega) ≫
          (Pi.π (fun m ↦ T.obj (op m)) n).f (k - 1)
    rw [← O.map_comp_assoc]
    have he := hEzero P Q k (k - 1) (by omega)
    have hl := hLzero SP SQ k (k - 1) (by omega)
    change χE.f k ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v k (k - 1) (by omega) =
        0 at he
    change χL.f k ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary T)).v k (k - 1) (by omega) =
        0 at hl
    rw [← Category.assoc (χE.f k), he, zero_comp, O.map_zero, zero_comp,
      ← Category.assoc (χL.f k), hl, zero_comp, comp_zero]

end WeilConjectures.RationalVerdier
