/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
public import WeilConjectures.CategoryTheory.StageSystem.Preadditive
public import Mathlib.CategoryTheory.Functor.Currying
public import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization
import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Bilinear comparisons under coefficient descent

Source: main-20261015, `def-weil-rationalization-karoubi` (raw Hom tensor formula)
and `def-weil-algebraically-closed-coefficients` (common-stage Hom formula).
(blueprint: lem-pur-bilinear-comparison-coefficient-descent).

The algebraic and common-stage assertions are parametrized separately: the latter applies
both before and after the former, and does not assume additive objects or triangulations.
Scalar-first tensors use the recorded ScalarLocalization convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local implicit_reducible] CategoryTheory.Prod.sectL CategoryTheory.Prod.sectR
  CategoryTheory.ScalarLocalization.extension
attribute [local instance 2000] DivisionSemiring.to_moduleIsTorsionFree

set_option linter.unusedSectionVars false

universe r u v u' v' u₂ v₂ u₃ v₃ w

open CategoryTheory TensorProduct

namespace CategoryTheory.BilinearCoefficientDescent

variable {R : Type r} [CommRing R]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear R D]

@[no_expose] private def tensorComp (R : Type r) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] (p : R) (K L M : C)
    (g : Localization.Away p ⊗[R] (L ⟶ M)) (f : Localization.Away p ⊗[R] (K ⟶ L)) :
    Localization.Away p ⊗[R] (K ⟶ M) :=
  ((ScalarLocalization.composition R C p K L M).toFun g).toFun f

attribute [local implicit_reducible] tensorComp

attribute [local simp] tensorComp_zero_left tensorComp_zero_right
  tensorComp_add_left tensorComp_add_right

@[no_expose] private def integralHom (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U)
    (X X' Y Y' : C) : (X ⟶ X') →ₗ[R] (Y ⟶ Y') →ₗ[R]
      (U.obj (X, Y) ⟶ U.obj (X', Y')) := by
  letI := (hU.1 X').1
  letI := (hU.1 X').2
  letI := (hU.2 Y).1
  letI := (hU.2 Y).2
  exact LinearMap.mk₂ R
    (fun f g ↦ ((Prod.sectL C Y ⋙ U).map f) ≫ ((Prod.sectR X' C ⋙ U).map g))
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_add, Preadditive.add_comp])
    (by intros; rw [(Prod.sectL C Y ⋙ U).map_smul, Linear.smul_comp])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_add, Preadditive.comp_add])
    (by intros; rw [(Prod.sectR X' C ⋙ U).map_smul, Linear.comp_smul])

attribute [local irreducible] integralHom

@[no_expose] private noncomputable def rawHomLinear (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C) :
    (Localization.Away p ⊗[R] (X ⟶ X')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (Y ⟶ Y')) →ₗ[Localization.Away p]
      (Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y'))) :=
  TensorProduct.curry
    (((TensorProduct.lift (integralHom U hU X X' Y Y')).baseChange
      (Localization.Away p)).comp
        (AlgebraTensorModule.distribBaseChange R (Localization.Away p)
          (X ⟶ X') (Y ⟶ Y')).symm.toLinearMap)

@[no_expose] private def rawHom (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) (X X' Y Y' : C)
    (f : Localization.Away p ⊗[R] (X ⟶ X'))
    (g : Localization.Away p ⊗[R] (Y ⟶ Y')) :
    Localization.Away p ⊗[R] (U.obj (X, Y) ⟶ U.obj (X', Y')) :=
  ((rawHomLinear p U hU X X' Y Y').toFun f).toFun g

attribute [local simp] rawHom_zero_left rawHom_zero_right rawHom_add_left rawHom_add_right

attribute [local irreducible] rawHom rawHomLinear ScalarLocalization.composition
  ScalarLocalization.extensionHom ScalarLocalization.coefficientMap

@[no_expose] private noncomputable def rawFunctor (p : R) (U : C × C ⥤ D)
    (hU : IsSeparatelyLinear R U) :
    ScalarLocalization R C p × ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨U.obj (X.1.obj, X.2.obj)⟩
  map {X Y} f := rawHom p U hU _ _ _ _ f.1 f.2
  map_id X := by
    change rawHom p U hU _ _ _ _ (1 ⊗ₜ[R] 𝟙 _) (1 ⊗ₜ[R] 𝟙 _) = _
    rw [rawHom_tmul, one_mul]
    exact congrArg (fun f ↦ (1 : Localization.Away p) ⊗ₜ[R] f) (U.map_id _)
  map_comp {X Y Z} f g := rawHom_comp p U hU _ _ _ _ _ _ f.1 g.1 f.2 g.2

attribute [local implicit_reducible] rawFunctor

/-- Give a functor its prescribed object function, transporting its morphisms.
Source: transport along object equalities
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def withObjects
    {C₀ : Type u₃} [Category.{v₃} C₀] {D₀ : Type u₂} [Category.{v₂} D₀]
    (F : C₀ ⥤ D₀) (obj : C₀ → D₀) (h : ∀ X, F.obj X = obj X) : C₀ ⥤ D₀ where
  obj := obj
  map {X Y} f := eqToHom (h X).symm ≫ F.map f ≫ eqToHom (h Y)
  map_id X := by
    simp only [F.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
  map_comp f g := by
    simp only [F.map_comp, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]

/-- The unique raw extension; all its data are determined by the preceding prescription.
Source: raw Hom tensor formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def raw (p : R) (U : C × C ⥤ D) (hU : IsSeparatelyLinear R U) :=
  withObjects (raw_extension_existsUnique p U hU).exists.choose
    (fun X ↦ ⟨U.obj (X.1.obj, X.2.obj)⟩)
    (raw_extension_existsUnique p U hU).exists.choose_spec.2.1

attribute [local irreducible] raw

section RawWhiskering

variable {E : Type u₂} [Category.{v₂} E] [Preadditive E] [Linear R E]

end RawWhiskering

attribute [local implicit_reducible] StageSystem.Morphism.functor StageSystem.ι

section CommonStage

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  {A₂ : I → Type u₂} [∀ i, Category.{v₂} (A₂ i)]
  {B : I → Type u'} [∀ i, Category.{v'} (B i)]
  (S : StageSystem A) (S₂ : StageSystem A₂) (T : StageSystem B)

/-- The family of identity comparisons, with its unchanged component type.
Source: supplied common-stage units
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitComparisons (S : StageSystem A) := ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)

/-- The two cocycles stored with specified identity comparisons.
Source: common-stage unit equations
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def UnitLaws (S : StageSystem A) (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i)) :
    Prop :=
  (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X)) ∧
    (∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X))

/-- Specified identity comparisons and their two unit cocycles.
Source: common-stage formula, supplied identity and tower isomorphisms
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Units (S : StageSystem A) :=
  {unit : UnitComparisons S // UnitLaws S unit}

namespace Units

@[no_expose, implicit_reducible] def unit {S : StageSystem A} (uS : Units S) :
    ∀ i, S.T (le_refl i) ≅ 𝟭 (A i) := uS.val

@[no_expose] def mk {S : StageSystem A} (unit : ∀ i, S.T (le_refl i) ≅ 𝟭 (A i))
    (left : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc (le_refl i) h).hom.app X = (S.T h).map ((unit i).hom.app X))
    (right : ∀ {i j : I} (h : i ≤ j) (X : A i),
      (S.assoc h (le_refl j)).hom.app X = (unit j).hom.app ((S.T h).obj X)) :
    Units S := ⟨unit, left, right⟩

end Units

/-- The tower law stored in a bilinear family.
Source: common-stage comparison cocycle
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def FamilyTower (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j) : Prop :=
  ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)

namespace Family

variable {S S₂ T}

@[no_expose, implicit_reducible] def U (F : Family S S₂ T) : ∀ i, A i × A₂ i ⥤ B i := F.functors

@[no_expose, implicit_reducible] def comparison (F : Family S S₂ T) {i j : I} (h : i ≤ j) :
    F.U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ F.U j := F.comparisons h

@[no_expose] def mk (U : ∀ i, A i × A₂ i ⥤ B i)
    (comparison : ∀ {i j : I} (h : i ≤ j),
      U i ⋙ T.T h ≅ (S.T h).prod (S₂.T h) ⋙ U j)
    (tower : ∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k) (X : A i) (Y : A₂ i),
    (T.T h').map ((comparison h).hom.app (X, Y)) ≫
      (comparison h').hom.app ((S.T h).obj X, (S₂.T h).obj Y) ≫
      (U k).map (X := ((S.T h').obj ((S.T h).obj X),
        (S₂.T h').obj ((S₂.T h).obj Y)))
        (Y := ((S.T (h.trans h')).obj X, (S₂.T (h.trans h')).obj Y))
        ((S.assoc h h').hom.app X, (S₂.assoc h h').hom.app Y) =
    (T.assoc h h').hom.app ((U i).obj (X, Y)) ≫
      (comparison (h.trans h')).hom.app (X, Y)) : Family S S₂ T := Family.mkData U comparison tower

end Family

variable {S S₂ T}

/-- The scalar square stored in a compatible transformation.
Source: common-stage transformation formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def TransformationSquare (U V : Family S S₂ T)
    (app : ∀ i, U.U i ⟶ V.U i) : Prop :=
  ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
    (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
      (U.comparison h).hom.app (X, Y) ≫
        (app j).app ((S.T h).obj X, (S₂.T h).obj Y)

namespace Transformation

variable {U V : Family S S₂ T}

@[no_expose, implicit_reducible] def app (η : Transformation U V) (i : I) :
    U.U i ⟶ V.U i := η.components i

@[no_expose] def mk (app : ∀ i, U.U i ⟶ V.U i)
    (square : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₂ i),
      (T.T h).map ((app i).app (X, Y)) ≫ (V.comparison h).hom.app (X, Y) =
        (U.comparison h).hom.app (X, Y) ≫
          (app j).app ((S.T h).obj X, (S₂.T h).obj Y)) : Transformation U V :=
  Transformation.mkData app square

end Transformation

@[no_expose] private def productSystem (S : StageSystem A) (S₂ : StageSystem A₂) :
    StageSystem (fun i ↦ A i × A₂ i) where
  T h := (S.T h).prod (S₂.T h)
  assoc h h' := NatIso.ofComponents
    (fun X ↦ Iso.prod ((S.assoc h h').app X.1) ((S₂.assoc h h').app X.2))
    (by
      intro X Y f
      exact Prod.ext ((S.assoc h h').hom.naturality f.1)
        ((S₂.assoc h h').hom.naturality f.2))
  cocycle h h' h'' X := Prod.ext (S.cocycle h h' h'' X.1) (S₂.cocycle h h' h'' X.2)

@[no_expose] private def familyMorphism (U : Family S S₂ T) : (productSystem S S₂).Morphism T where
  Φ := U.U
  β := U.comparison
  coh h h' X := U.tower h h' X.1 X.2

@[no_expose] private def projectionLeft (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S where
  Φ i := Prod.fst (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S.assoc h h').hom.app X.1 =
      (S.assoc h h').hom.app X.1 ≫ 𝟙 _
    simp

@[no_expose] private def projectionRight (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).Morphism S₂ where
  Φ i := Prod.snd (A i) (A₂ i)
  β _ := Iso.refl _
  coh h h' X := by
    change (S₂.T h').map (𝟙 _) ≫ 𝟙 _ ≫ (S₂.assoc h h').hom.app X.2 =
      (S₂.assoc h h').hom.app X.2 ≫ 𝟙 _
    simp

@[no_expose] private def diagonal (S : StageSystem A) (S₂ : StageSystem A₂) :
    (productSystem S S₂).PairCategory ⥤ S.PairCategory × S₂.PairCategory where
  obj X := (⟨X.stage, X.obj.1⟩, ⟨X.stage, X.obj.2⟩)
  map f := ((projectionLeft S S₂).functor.prod' (projectionRight S S₂).functor).map f
  map_id X := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_id X
  map_comp f g := ((projectionLeft S S₂).functor.prod'
    (projectionRight S S₂).functor).map_comp f g

attribute [local implicit_reducible] productSystem familyMorphism projectionLeft
  projectionRight diagonal

@[no_expose] private def diagonalFF (S : StageSystem A) (S₂ : StageSystem A₂) :
    (diagonal S S₂).FullyFaithful :=
  ((Functor.FullyFaithful.nonempty_iff_map_bijective _).2 (diagonal_bijective S S₂)).some

@[no_expose] private def pairedObject (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) : (productSystem S S₂).PairCategory :=
  ⟨join X.1.stage X.2.stage,
    (X.1.toStage (left _ _), X.2.toStage (right _ _))⟩

@[no_expose] private def pairedIso (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
    (X : S.PairCategory × S₂.PairCategory) :
    (diagonal S S₂).obj (pairedObject S S₂ join left right X) ≅ X :=
  Iso.prod (S.isoToStage X.1 (left _ _)).symm
    (S₂.isoToStage X.2 (right _ _)).symm

@[no_expose] private def pairing (S : StageSystem A) (S₂ : StageSystem A₂) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ (productSystem S S₂).PairCategory where
  obj := pairedObject S S₂ join left right
  map {X Y} f := (diagonalFF S S₂).preimage
    ((pairedIso S S₂ join left right X).hom ≫ f ≫
      (pairedIso S S₂ join left right Y).inv)
  map_id X := by
    apply (diagonalFF S S₂).map_injective
    rw [(diagonalFF S S₂).map_preimage]
    simp
  map_comp {X Y Z} f g := by
    apply (diagonalFF S S₂).map_injective
    rw [Functor.map_comp]
    simp only [(diagonalFF S S₂).map_preimage, Category.assoc, Iso.inv_hom_id_assoc]

attribute [local implicit_reducible] pairedObject pairedIso pairing output endpoint

@[no_expose] private def explicitDescent (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :
    S.PairCategory × S₂.PairCategory ⥤ T.PairCategory where
  obj X := output U join left right X
  map f := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map f
  map_id X := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_id X
  map_comp f g := (pairing S S₂ join left right ⋙ (familyMorphism U).functor).map_comp f g

/-- The unique representative-normalized descended bifunctor.
Source: common-stage Hom formula
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def descend (U : Family S S₂ T) (join : I → I → I)
    (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j) :=
  withObjects (descent_existsUnique U join left right).exists.choose
    (output U join left right)
    (descent_existsUnique U join left right).exists.choose_spec.1

attribute [local implicit_reducible] explicitDescent

attribute [local irreducible] descend

@[no_expose] private def pairingComparison (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    pairing S S₂ j jl jr ≅ pairing S S₂ k kl kr :=
  NatIso.ofComponents
    (fun X ↦ (diagonalFF S S₂).preimageIso
      (pairedIso S S₂ j jl jr X ≪≫ (pairedIso S S₂ k kl kr X).symm)) (by
        intro X Y f
        apply (diagonalFF S S₂).map_injective
        simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
          (diagonalFF S S₂).map_preimage]
        change (diagonal S S₂).map ((diagonalFF S S₂).preimage _) ≫ _ =
          _ ≫ (diagonal S S₂).map ((diagonalFF S S₂).preimage _)
        simp only [(diagonalFF S S₂).map_preimage]
        simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
          Iso.inv_hom_id_assoc])

@[no_expose] private def descentComparison (U : Family S S₂ T) (j k : I → I → I)
    (jl : ∀ a b, a ≤ j a b) (jr : ∀ a b, b ≤ j a b)
    (kl : ∀ a b, a ≤ k a b) (kr : ∀ a b, b ≤ k a b) :
    descend U j jl jr ≅ descend U k kl kr :=
  eqToIso (descend_eq U j jl jr) ≪≫
    Functor.isoWhiskerRight (pairingComparison j k jl jr kl kr) (familyMorphism U).functor ≪≫
      (eqToIso (descend_eq U k kl kr)).symm

attribute [local irreducible] productSystem projectionLeft projectionRight diagonal diagonalFF
  pairedObject pairedIso pairing

section InputLeft

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S) (U : Family S S₂ T) (UF : Family S₀ S₂ T)
    (hU : ∀ i, UF.U i = ((F.Φ i).prod (𝟭 (A₂ i))) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A₀ i) (Y : A₂ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app ((F.Φ i).obj X, Y) ≫
          (U.U j).map (X := ((S.T h).obj ((F.Φ i).obj X), (S₂.T h).obj Y))
            (Y := ((F.Φ j).obj ((S₀.T h).obj X), (S₂.T h).obj Y))
            ((F.β h).hom.app X, 𝟙 _)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

end InputLeft

section InputRight

variable
    {A₀ : I → Type u₃} [∀ i, Category.{v₃} (A₀ i)] {S₀ : StageSystem A₀}
    (F : S₀.Morphism S₂) (U : Family S S₂ T) (UF : Family S S₀ T)
    (hU : ∀ i, UF.U i = ((𝟭 (A i)).prod (F.Φ i)) ⋙ U.U i)
    (cU : ∀ {i j : I} (h : i ≤ j) (X : A i) (Y : A₀ i),
      HEq ((UF.comparison h).hom.app (X, Y))
        ((U.comparison h).hom.app (X, (F.Φ i).obj Y) ≫
          (U.U j).map (X := ((S.T h).obj X, (S₂.T h).obj ((F.Φ i).obj Y)))
            (Y := ((S.T h).obj X, (F.Φ j).obj ((S₀.T h).obj Y)))
            (𝟙 _, (F.β h).hom.app Y)))
    (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

end InputRight

end CommonStage

section RationalSystems

variable {I : Type w} [Preorder I]
  {O : I → Type r} [∀ i, CommRing (O i)] (π : ∀ i, O i)
  (φ : ∀ {i j : I}, i ≤ j → O i →+* O j)
  (unitImage : ∀ {i j : I} (h : i ≤ j),
    IsUnit (algebraMap (O j) (Localization.Away (π j)) (φ h (π i))))
  {A : I → Type u} [∀ i, Category.{v} (A i)]
  [∀ i, Preadditive (A i)] [∀ i, Linear (O i) (A i)]
  (S : StageSystem A) [∀ (i j : I) (h : i ≤ j), (S.T h).Additive]
  (semi : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (S.T h))

variable {π φ unitImage S semi}

@[no_expose] private def rationalComparisonIso
    {B : I → Type u'} [∀ i, Category.{v'} (B i)]
    [∀ i, Preadditive (B i)] [∀ i, Linear (O i) (B i)]
    (T : StageSystem B) [∀ (i j : I) (h : i ≤ j), (T.T h).Additive]
    (semiT : ∀ {i j : I} (h : i ≤ j), ScalarLocalization.IsSemilinear (φ h) (T.T h))
    (U : Family S S T) (hU : ∀ i, IsSeparatelyLinear (O i) (U.U i))
    {i j : I} (h : i ≤ j) :
    rawFunctor (π i) (U.U i) (hU i) ⋙
        ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (T.T h) (semiT h) ≅
      (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)).prod
        (ScalarLocalization.extension (π i) (π j) (φ h) (unitImage h) (S.T h) (semi h)) ⋙
        rawFunctor (π j) (U.U j) (hU j) :=
  NatIso.ofComponents
    (fun X ↦ (ScalarLocalization.localization (O j) (B j) (π j)).mapIso
      ((U.comparison h).app (X.1.obj, X.2.obj))) (by
        intro X Y f
        exact rationalComparison_naturality T semiT U hU h
          X.1.obj Y.1.obj X.2.obj Y.2.obj f.1 f.2)

attribute [local irreducible] Units HasUnitComparison

end RationalSystems

attribute [local irreducible] Padic.coefficientExtensionIntegers
  Padic.coefficientExtensionUniformizer

section PadicCoefficients

variable (l : ℕ) [Fact l.Prime] (Ω : Type w) [Field Ω]
  [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The recorded valuation rings, indexed by the genuine finite intermediate extensions.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def Integers (E : Padic.FiniteCoefficientFields l Ω) : Subring E.val :=
  Padic.coefficientExtensionIntegers l E.val

/-- The recorded uniformizer; no extra torsion-free or characteristic hypotheses.
Source: blueprint coefficient definitions
(blueprint: lem-pur-bilinear-comparison-coefficient-descent). -/
@[no_expose] def uniformizer (E : Padic.FiniteCoefficientFields l Ω) : Integers l Ω E :=
  ⟨(Padic.coefficientExtensionUniformizer l E.val : E.val), uniformizer_mem l Ω E⟩

set_option linter.unusedSectionVars false in
attribute [local irreducible] Padic.finiteCoefficientCompositum uniformizer

end PadicCoefficients
end CategoryTheory.BilinearCoefficientDescent
