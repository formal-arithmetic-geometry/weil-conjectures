/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.FiniteCoordinates.SystemFiniteEvaluationCoordinates
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Adjunction coordinates for finite system evaluation

Source: Stacks 03DI and 07A7; finite evaluation in prop-sf-pf-coherence.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
universe u
open scoped CategoryTheory.TwoSquare
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.IntegralSystemRealization.FiniteCoordinates

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  scalarReductionTargetDerived
attribute [local irreducible] HasDerivedCategory.standard Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

/-- Finite evaluation in the fixed coefficient presentation.
Source: Stacks 03DI and 07A7
(blueprint: lem-sf-system-finite-adjunction-coordinates). -/
def fixedEvaluation (m : ℕ) (X : Scheme.{u}) : System l E X ⥤
    ProperOpenDerived (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) X :=
  coefficientSequenceDerivedEvaluation l E X m ⋙
    (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E (m + 1))).inverse

/-- The object coordinate of fixed finite evaluation.
Source: Stacks 03DI (blueprint: lem-sf-system-finite-adjunction-coordinates). -/
theorem fixedEvaluation_obj (m : ℕ) (X : Scheme.{u}) (M : System l E X) :
    (fixedEvaluation l E m X).obj M = input l E m X M := rfl

/-- The morphism coordinate of fixed finite evaluation.
Source: Stacks 03DI (blueprint: lem-sf-system-finite-adjunction-coordinates). -/
theorem fixedEvaluation_map (m : ℕ) (X : Scheme.{u})
    {M N : System l E X} (f : M ⟶ N) :
    (fixedEvaluation l E m X).map f =
      (sfIntrinsicDerivedEquivalence X
        (Padic.coefficientExtensionRing l E (m + 1))).inverse.map
          ((coefficientSequenceDerivedEvaluation l E X m).map f) := rfl

/-- The natural direct-image coordinate, with the coefficient unit cancelled.
Source: Stacks 03DI and 07A7
(blueprint: lem-sf-system-finite-adjunction-coordinates). -/
def pushCoordinates (o : Operations l E) (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Operations.push l E o f ⋙ fixedEvaluation l E m Y ≅
      fixedEvaluation l E m X ⋙
        ProperOpenPush (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f :=
  NatIso.ofComponents (fixedPush l E o m f) (by
    intro M N a
    exact fixedPush_naturality l E o m f a)

/-- Naturality of open evaluation before cancelling the coefficient presentation.
Source: Stacks 03DI (blueprint: lem-sf-system-finite-adjunction-coordinates).
Proof: paste open-evaluation naturality, counit naturality of the coefficient
presentation, and naturality of the derived open comparison. -/
theorem shriek_naturality (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : System l E X} (a : M ⟶ N) :
    (coefficientSequenceDerivedEvaluation l E Y m).map
        ((Operations.shriek l E o j).map a) ≫ (shriek l E o m j N).hom =
      (shriek l E o m j M).hom ≫
        (sfIntrinsicDerivedEquivalence Y
          (Padic.coefficientExtensionRing l E (m + 1))).functor.map
            ((ProperOpenShriek
              (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) j).map
                ((sfIntrinsicDerivedEquivalence X
                  (Padic.coefficientExtensionRing l E (m + 1))).inverse.map
                    ((coefficientSequenceDerivedEvaluation l E X m).map a))) := by
  let B := Padic.coefficientExtensionRing l E (m + 1)
  let J := (sfIntrinsicExtensionByZero j B).mapDerivedCategory
  let R := sfIntrinsicDerivedEquivalence X B
  let v := (coefficientSequenceDerivedEvaluation l E X m).map a
  let ν := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison B j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  simp only [shriek, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  have hn := ((o.openEvaluation j).evaluation m).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  have hu := R.counitIso.inv.naturality v
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← J.map_comp_assoc, hu, J.map_comp]
  simp only [Category.assoc]
  have hv := ν.hom.naturality (R.inverse.map v)
  dsimp only [Functor.comp_map] at hv
  erw [hv]
  rfl

/-- The natural open coordinate, with the coefficient unit cancelled.
Source: Stacks 03DI and 07A7
(blueprint: lem-sf-system-finite-adjunction-coordinates). -/
def shriekCoordinates (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    Operations.shriek l E o j ⋙ fixedEvaluation l E m Y ≅
      fixedEvaluation l E m X ⋙
        ProperOpenShriek (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) j :=
  NatIso.ofComponents (fixedShriek l E o m j) (by
    intro M N a
    exact fixed_square _ (shriek l E o m j M) (shriek l E o m j N) _ _
      (shriek_naturality l E o m j a))

private def inverse_coordinates
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (R : A ≌ B) (S : C ≌ D) (F : A ⥤ C) (G : B ⥤ D)
    (q : R.functor ⋙ G ≅ F ⋙ S.functor) : G ⋙ S.inverse ≅ R.inverse ⋙ F :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight R.counitIso.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerRight q S.inverse) ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.isoWhiskerLeft F S.unitIso.symm) ≪≫
    Functor.isoWhiskerLeft R.inverse (Functor.rightUnitor F)

private theorem evaluation_is_mate (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (o.direct f).adj (finiteAdj l E f m)
      (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f m).inv)).natTrans =
        ((o.evaluation f).evaluation m).hom := by
  ext M
  apply ((finiteAdj l E f m).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((pullbackTensorDerivedEvaluation l E f m).hom.app
    ((Operations.push l E o f).obj M))).mp
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
    ((o.evaluation f).counit m M).symm

/-- The prescribed direct coordinate is the mate of a unique pull coordinate.

Source: Stacks 03DI and 07A7; finite evaluation in
prop-sf-pf-coherence.proof.md.
Proof: evaluate the system pullback using pullbackTensorDerivedEvaluation.
Transport the finite intrinsic adjunction through sfIntrinsicDerivedEquivalence.
The section-normalized direct-image comparison identifies its right adjoint with
ProperOpenPush; adjoint uniqueness gives the corresponding left comparison with
ProperOpenPull. Compose this comparison with the evaluated pullback comparison.
The unit and counit evaluation equations in DirectEvaluation identify its mate
with pushCoordinates, after cancelling the coefficient-equivalence unit/counit.
Finally mateEquiv is injective, and an isomorphism is determined by its inverse,
so this pull coordinate is unique. The construction works for every scheme map,
including identities, empty schemes, and zero complexes.
(blueprint: lem-sf-system-finite-adjunction-coordinates).
-/
theorem pullCoordinates_existsUnique (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : pull l E f ⋙ fixedEvaluation l E m X ≅
        fixedEvaluation l E m Y ⋙
          ProperOpenPull (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f,
      (mateEquiv (o.direct f).adj
        (derivedUpperStarLowerStarAdjunction
          (ModuleCat.{u + 1}
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) f)
        (TwoSquare.mk _ _ _ _ e.inv)).natTrans = (pushCoordinates l E o m f).hom := by
  let B := Padic.coefficientExtensionRing l E (m + 1)
  let RX := sfIntrinsicDerivedEquivalence X B
  let RY := sfIntrinsicDerivedEquivalence Y B
  let F := ProperOpenPush (ULift.{u + 1} B) f
  let G := proEtaleConstantDerivedDirectImage f B
  let a := (o.direct f).adj
  let b := finiteAdj l E f m
  let c := derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) f
  let δ := inverse_coordinates RX RY F G (sfIntrinsicDerivedDirectImageComparison f B)
  let α := (mateEquiv b c).symm (TwoSquare.mk _ _ _ _ δ.hom)
  let _ : IsIso α.natTrans := isIso_inverseMate_of_equivalences b c δ
  let σ := TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E f m).inv
  let t := σ ≫ₕ α
  let _ : IsIso t.natTrans := by
    dsimp only [t, TwoSquare.hComp]
    infer_instance
  let e := (asIso t.natTrans).symm
  have he : (mateEquiv a c (TwoSquare.mk _ _ _ _ e.inv)).natTrans =
      (pushCoordinates l E o m f).hom := by
    have h := mateEquiv_vcomp a b c σ α
    rw [show mateEquiv a b σ = TwoSquare.mk _ _ _ _
      ((o.evaluation f).evaluation m).hom from
        evaluation_is_mate l E o m f] at h
    rw [(mateEquiv b c).apply_symm_apply] at h
    ext M
    have hm := congrArg (fun s ↦ s.natTrans.app M) h
    simpa only [e, t, α, δ, inverse_coordinates, pushCoordinates, fixedPush, push,
      TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans, NatIso.ofComponents_hom_app,
      Iso.symm_inv, asIso_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      NatTrans.comp_app, Category.id_comp, Category.comp_id, Functor.map_comp,
      Functor.map_id, Functor.comp_map, Functor.comp_obj, Functor.id_obj,
      Category.assoc, input, RX, RY, F, G, B] using hm
  refine ⟨e, he, ?_⟩
  intro e' he'
  have h : e'.inv = e.inv := (mateEquiv a c).injective (he'.trans he.symm)
  exact congrArg Iso.symm (show e'.symm = e.symm from Iso.ext h)

/-- The pull comparison uniquely determined by the two prescribed adjunctions.
Source: Stacks 03DI and 07A7
(blueprint: lem-sf-system-finite-adjunction-coordinates). -/
def pullCoordinates (o : Operations l E) (m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pull l E f ⋙ fixedEvaluation l E m X ≅
      fixedEvaluation l E m Y ⋙
        ProperOpenPull (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1))) f :=
  (pullCoordinates_existsUnique l E o m f).exists.choose

/-- The defining mate equation for the chosen pull comparison.
Source: Stacks 03DI and 07A7
(blueprint: lem-sf-system-finite-adjunction-coordinates). -/
theorem pullCoordinates_mate (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (o.direct f).adj
      (derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1}
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (m + 1)))) f)
      (TwoSquare.mk _ _ _ _ (pullCoordinates l E o m f).inv)).natTrans =
        (pushCoordinates l E o m f).hom :=
  (pullCoordinates_existsUnique l E o m f).exists.choose_spec

/-- The direct-coordinate component is the prescribed fixed push isomorphism.
Source: Stacks 07A7 (blueprint: lem-sf-system-finite-adjunction-coordinates). -/
theorem pushCoordinates_hom_app (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) :
    (pushCoordinates l E o m f).hom.app M = (fixedPush l E o m f M).hom := rfl

/-- The open-coordinate component is the prescribed fixed shriek isomorphism.
Source: Stacks 03DI (blueprint: lem-sf-system-finite-adjunction-coordinates). -/
theorem shriekCoordinates_hom_app (o : Operations l E) (m : ℕ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : System l E X) :
    (shriekCoordinates l E o m f).hom.app M = (fixedShriek l E o m f M).hom := rfl

attribute [implicit_reducible] fixedEvaluation

end WeilConjectures.IntegralSystemRealization.FiniteCoordinates
