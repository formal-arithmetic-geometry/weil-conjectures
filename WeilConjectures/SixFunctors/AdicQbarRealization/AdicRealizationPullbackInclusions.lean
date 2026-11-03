/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.PoincareDuality.Derived.DerivedAutomorphismHomEvaluationContinuationB
public import Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.SixFunctors.Common.CommonStagePullbackNormalizedDescent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull

/-! # Pullback on finite-stage inclusions

Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-realization-pullback-inclusions)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients (inclusion stageSystem)

attribute [local irreducible] HasDerivedCategory.standard integralDerivedPullback

private theorem morphism_inclusion_eq
    {I : Type*} [Preorder I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)]
    {D : I → Type*} [∀ i, Category (D i)]
    {S : StageSystem C} {T : StageSystem D} (F : S.Morphism T) (i : I) :
    S.ι i ⋙ F.functor = F.Φ i ⋙ T.ι i := by
  refine CategoryTheory.Functor.hext (F := S.ι i ⋙ F.functor)
    (G := F.Φ i ⋙ T.ι i) (fun _ ↦ rfl) ?_
  intro K L f
  exact heq_of_eq (F.functor_map_ι f)

/-- The chosen pullback restricts to its prescribed rational stage functor.
Source: normalized descent (blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationPullback_inclusion_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l)) :
    inclusion (l := l) (Ω := PadicAlgCl l) (Y := Y) E ⋙
        commonStageDerivedPullback l (PadicAlgCl l) g =
      rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        inclusion (l := l) (Ω := PadicAlgCl l) (Y := X) E := by
  obtain ⟨hc, he⟩ := commonStagePullbackNormalizedDescent l (PadicAlgCl l) g
  rw [he]
  exact morphism_inclusion_eq _ E

/-- Integral localization intertwines the prescribed integral and rational pullbacks.
Source: rational pullback normalization
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationPullback_localization_eq (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : Index l (PadicAlgCl l)) :
    sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) Y ⋙
        rationalDerivedPullback l (Coefficient.{u} l (PadicAlgCl l) E) g =
      constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        sfRationalConstructibleLocalization l (Coefficient.{u} l (PadicAlgCl l) E) X := by
  let h := (rationalDerivedPullback_existsUnique l
    (Coefficient.{u} l (PadicAlgCl l) E) g).exists.choose_spec
  refine CategoryTheory.Functor.hext (fun K ↦ h.2.1 _) ?_
  intro K L f
  exact h.2.2 K L f 1

/-- Complete-input inverse image agrees with the tower-defined integral pullback.
Source: the specified completion-unit comparison and its naturality laws
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
@[irreducible] def realizationCompletionPullbackIso (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l)) :
    (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) Y).ι ⋙
        podCompletedDerivedInverseImage l (Coefficient.{u} l (PadicAlgCl l) E) g ≅
      constructibleIntegralPullback l (Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        (sfIntegralConstructible l (Coefficient.{u} l (PadicAlgCl l) E) X).ι :=
  NatIso.ofComponents
    (fun K ↦ podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K)
    (fun {K L} f ↦ (podCompletedToTower_laws l
      (Coefficient.{u} l (PadicAlgCl l) E) g).1 K.obj L.obj f.hom)

/-- The inverse component is the prescribed complete-input comparison.
Source: construction of the preceding isomorphism
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationCompletionPullbackIso_inv_app (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (E : Index l (PadicAlgCl l))
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l (PadicAlgCl l) E) Y) :
    (realizationCompletionPullbackIso l g E).inv.app K =
      (podCompletedToTowerIso l (Coefficient.{u} l (PadicAlgCl l) E) g K).inv := by
  delta realizationCompletionPullbackIso
  rfl

end WeilConjectures.AdicQbarRealization

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The ambient comparison is the canonical exact-pullback comparison itself.
Source: `def-weil-derived-pullback-tensor-hom`, the termwise formula for total pullback.
Proof: exactness identifies the total left derived functor with termwise inverse image.
(blueprint: lem-sfb-condensed-pullback-inclusions). -/
def realizationPullback_termwiseIso :
    moduleObjectDerivedPullback Λ g ≅ (upperStar Λ g).mapDerivedCategory :=
  leftDerivedUpperStarIsoMapDerivedCategory Λ g

/-- On any full subcategory, derived inverse image is the exact termwise inverse image.
Source: `def-weil-derived-pullback-tensor-hom`, its exactness comparison.
Proof: restrict the components of the canonical total-derived/termwise comparison.
Its naturality on the underlying morphisms proves naturality after inclusion.
(blueprint: lem-sfb-condensed-pullback-inclusions). -/
def realizationPullback_inclusionIso :
    P.ι ⋙ moduleObjectDerivedPullback Λ g ≅ P.ι ⋙ (upperStar Λ g).mapDerivedCategory :=
  NatIso.ofComponents
    (fun K ↦ (realizationPullback_termwiseIso Λ g).app K.obj)
    (fun {_K _L} f ↦ (realizationPullback_termwiseIso Λ g).hom.naturality f.hom)

/-- Restriction retains the specified inverse component, with no choice of comparisons.
Source: the component construction above.
Proof: unfold the natural isomorphism built from components.
(blueprint: lem-sfb-condensed-pullback-inclusions). -/
theorem realizationPullback_inclusionIso_inv_app (K : P.FullSubcategory) :
    (realizationPullback_inclusionIso Λ g P).inv.app K =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K.obj := by
  rfl

/-- Inverse image commutes with derived coefficient change, including localization
and non-flat reduction. No completion or finite-stage realization is involved.
Source: `det-prop-scalar-six-pullback`, proof (1).
Proof: use the canonical derived tensor/pullback comparison, computed on K-flat
resolutions; the coefficient square identifies the two tensor products.
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
def realizationPullback_scalarIso :
    moduleObjectDerivedPullback Λ g ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ moduleObjectDerivedPullback Λ' g :=
  derivedUpperStarExtendScalarsIso a g

/-- Transport the same scalar square through the exact-pullback identifications.
Source: `det-prop-scalar-six-pullback`, proof (1), where inverse image is exact.
Proof: compose inverse exactness at Λ, the specified total-derived scalar square,
and exactness at Λ′. These are the prescribed maps, not independently chosen witnesses.
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
def realizationPullback_scalarTermwiseIso :
    (upperStar Λ g).mapDerivedCategory ⋙ L(Mod.extendScalars (coefficientMap a X)) ≅
      L(Mod.extendScalars (coefficientMap a Y)) ⋙ (upperStar Λ' g).mapDerivedCategory :=
  Functor.isoWhiskerRight (realizationPullback_termwiseIso Λ g).symm _ ≪≫
    realizationPullback_scalarIso g a ≪≫
    Functor.isoWhiskerLeft _ (realizationPullback_termwiseIso Λ' g)

/-- The scalar comparison on a full subcategory is the restriction of the ambient
comparison, with the functor associators recorded explicitly.
Source: `det-prop-scalar-six-pullback`, proof (1), naturality in the input.
Proof: associate to the ambient square, restrict it by the inclusion, and reassociate.
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
def realizationPullback_scalarInclusionIso :
    (P.ι ⋙ (upperStar Λ g).mapDerivedCategory) ⋙
        L(Mod.extendScalars (coefficientMap a X)) ≅
      (P.ι ⋙ L(Mod.extendScalars (coefficientMap a Y))) ⋙
        (upperStar Λ' g).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft P.ι (realizationPullback_scalarTermwiseIso g a) ≪≫
    (Functor.associator _ _ _).symm

/-- The restricted comparison retains the specified ambient arrow and exactness transports.
Source: the preceding restricted comparison.
Proof: the associator components are identities; whiskering evaluates at the
underlying object. Thus no equality merely after reduction is used.
(blueprint: lem-sf-adic-realization-pullback-inclusions). -/
theorem realizationPullback_scalarInclusionIso_hom_app (K : P.FullSubcategory) :
    (realizationPullback_scalarInclusionIso g P a).hom.app K =
      L(Mod.extendScalars (coefficientMap a X)).map
          ((leftDerivedUpperStarIsoMapDerivedCategory Λ g).inv.app K.obj) ≫
        (derivedUpperStarExtendScalarsIso a g).hom.app K.obj ≫
        (leftDerivedUpperStarIsoMapDerivedCategory Λ' g).hom.app
          (L(Mod.extendScalars (coefficientMap a Y)).obj K.obj) := by
  simp only [realizationPullback_scalarInclusionIso, realizationPullback_scalarTermwiseIso,
    realizationPullback_scalarIso, realizationPullback_termwiseIso,
    Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Category.id_comp, Category.comp_id]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
