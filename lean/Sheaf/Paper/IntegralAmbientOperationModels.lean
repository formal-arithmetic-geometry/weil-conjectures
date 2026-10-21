/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.RingedTopoiDerivedPullback
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses
import all Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.KFlatTotalTensorModel

/-! # Ambient completion presentations of integral operations

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 0G7E, 07A4 and 0941;
sites-modules.tex, Tags 03D7 and 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

All towers and finite operations below are the recorded constructions. The completed
coefficient map is specified by its projections, not by an identification of rings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralAmbient
open AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem sequenceConstantUnit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (A : CommRingCat.{max u (t + 1)}) (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).obj A)).app U ≫
      (coefficientProEtaleDirectRingMap.{t, u} f A).hom.app U =
    (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)).app
      ((proEtaleBaseChange f).op.obj U) := by
  have h := (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj A))
      |>.apply_symm_apply (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj A)))
  exact congrArg (fun α ↦ α.app U) h

private theorem sequenceConstantMap_naturality {X Y : Scheme.{t}} (f : X ⟶ Y)
    {A B : CommRingCat.{max u (t + 1)}} (a : A ⟶ B) :
    (constantSheaf (ProEt.topology Y) CommRingCat.{max u (t + 1)}).map a ≫
      coefficientProEtaleDirectRingMap.{t, u} f B =
    coefficientProEtaleDirectRingMap.{t, u} f A ≫
      ((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
        (ProEt.topology Y) (ProEt.topology X)).map
          ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).map a) := by
  apply (sheafificationAdjunction (ProEt.topology Y)
      CommRingCat.{max u (t + 1)}).homEquiv ((Functor.const Y.ProEtᵒᵖ).obj A)
        (((proEtaleBaseChange f).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
          (ProEt.topology Y) (ProEt.topology X)).obj
            ((constantSheaf (ProEt.topology X) CommRingCat.{max u (t + 1)}).obj B)) |>.injective
  apply NatTrans.ext
  funext U
  change _ ≫ (_ ≫ _) = _ ≫ (_ ≫ _)
  have hY := congrArg (fun α ↦ α.app U)
    (toSheafify_naturality (ProEt.topology Y) ((Functor.const Y.ProEtᵒᵖ).map a))
  change a ≫ _ = _ ≫ _ at hY
  erw [← Category.assoc, ← hY, Category.assoc, sequenceConstantUnit,
    ← Category.assoc, sequenceConstantUnit]
  exact congrArg (fun α ↦ α.app ((proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map a))

/-- The completed-ring structure map is determined by all finite projections.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the constant-section maps commute with every quotient reduction. Compose them
with the completed-ring projections to obtain a cone after direct image. Direct image
preserves limits, so its universal property gives the map, and the projections give
uniqueness. Taking the adjoint gives the map f⁻¹R_Y → R_X without interchanging f⁻¹
and inverse limit. -/
theorem coefficientMap_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! c : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).obj (completedIntegralCommRingSheafUnrestricted l E X),
      ∀ n : ℕ, c ≫ ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
            (Scheme.ProEt.topology X)).map
              (completedIntegralCommRingProjectionUnrestricted l E X n) =
        completedIntegralCommRingProjectionUnrestricted l E Y n ≫
          Scheme.coefficientProEtaleDirectRingMap.{t, u} f
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let G := (Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
    RingCat.{max u (t + 1)} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let d (n : ℕ) : integralCoefficientSheaf l E Y n ⟶
      G.obj (integralCoefficientSheaf l E X n) :=
    ⟨Functor.whiskerRight (Scheme.coefficientProEtaleDirectRingMap.{t, u} f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
  have hd (n : ℕ) : (integralCoefficientSheafSystem l E Y).map
      (homOfLE (Nat.le_succ n)).op ≫ d n =
        d (n + 1) ≫ (integralCoefficientSheafSystem l E X ⋙ G).map
          (homOfLE (Nat.le_succ n)).op := by
    let a : CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 2))) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))) :=
      CommRingCat.ofHom ((ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          (ULift.ringEquiv : ULift.{t + 1} _ ≃+* _).toRingHom))
    have h := sequenceConstantMap_naturality.{t, u} f a
    simp only [Functor.comp_map, integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    exact congrArg (fun a ↦ (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map a) h
  let τ : integralCoefficientSheafSystem l E Y ⟶ integralCoefficientSheafSystem l E X ⋙ G :=
    NatTrans.ofOpSequence d hd
  have : PreservesLimitsOfShape ℕᵒᵖ G := by
    let H := sheafToPresheaf (Scheme.ProEt.topology Y) RingCat.{max u (t + 1)}
    have : PreservesLimitsOfShape ℕᵒᵖ (G ⋙ H) :=
      inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
        (sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)} ⋙
          (Functor.whiskeringLeft _ _ _).obj (Scheme.proEtaleBaseChange f).op))
    exact preservesLimitsOfShape_of_reflects_of_preserves G H
  let c : Cone (integralCoefficientSheafSystem l E X ⋙ G) :=
    ⟨completedIntegralCoefficientSheafUnrestricted l E Y,
      (limit.cone (integralCoefficientSheafSystem l E Y)).π ≫ τ⟩
  let h := isLimitOfPreserves G (limit.isLimit (integralCoefficientSheafSystem l E X))
  let ρ := h.lift c
  have hρ (n : ℕ) : ρ ≫ G.map
      (limit.π (integralCoefficientSheafSystem l E X) (op n)) =
        limit.π (integralCoefficientSheafSystem l E Y) (op n) ≫ d n := h.fac c (op n)
  let b : completedIntegralCommRingSheafUnrestricted l E Y ⟶
      ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        CommRingCat.{max u (t + 1)} (Scheme.ProEt.topology Y)
          (Scheme.ProEt.topology X)).obj (completedIntegralCommRingSheafUnrestricted l E X) :=
    ⟨{ app := fun U ↦
         letI := completedIntegralCoefficientCommRingUnrestricted l E Y U
         letI := completedIntegralCoefficientCommRingUnrestricted l E X
           ((Scheme.proEtaleBaseChange f).op.obj U)
         CommRingCat.ofHom (ρ.hom.app U).hom
       naturality := fun U V a ↦ (forget₂ CommRingCat RingCat).map_injective
         (ρ.hom.naturality a) }⟩
  refine ⟨b, ?_, ?_⟩
  · intro n
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat RingCat).map_injective
    exact congrArg (fun a ↦ a.hom.app U) (hρ n)
  · intro b' hb'
    let ρ' : completedIntegralCoefficientSheafUnrestricted l E Y ⟶
        G.obj (completedIntegralCoefficientSheafUnrestricted l E X) :=
      ⟨Functor.whiskerRight b'.hom (forget₂ CommRingCat RingCat)⟩
    have he : ρ' = ρ := by
      apply h.hom_ext
      intro n
      change ρ' ≫ G.map (limit.π (integralCoefficientSheafSystem l E X) n) =
        ρ ≫ G.map (limit.π (integralCoefficientSheafSystem l E X) n)
      rw [hρ n.unop]
      exact congrArg (fun a ↦ (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).map a)
          (hb' n.unop)
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply (forget₂ CommRingCat RingCat).map_injective
    exact congrArg (fun a ↦ a.hom.app U) he

/-- The unique projection-induced ring map, in its adjoint presentation.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def coefficientMap {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (coefficientMap_existsUnique l E f).exists.choose

/-- Ordinary module direct image with the projection-induced scalar action.
Source: Stacks 03D2 (blueprint: lem-pur-integral-ambient-operation-models). -/
def push {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := completedIntegralCoefficientSheafUnrestricted l E Y)
    (R := completedIntegralCoefficientSheafUnrestricted l E X)
    ⟨Functor.whiskerRight (coefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩

/-- The ordinary module pullback exists in the independent coefficient universe.
Source: Stacks 03D2, 03D7 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: transport to the coefficient-sized small site model. Presheaf module Kan
extension followed by module sheafification is left adjoint to this pushforward.
Transport back. Its tensor presentation is R_X ⊗_(f⁻¹R_Y) f⁻¹(-). -/
@[instance]
theorem push_isRightAdjoint {X Y : Scheme.{t}} (f : X ⟶ Y) :
    (push l E f).IsRightAdjoint := by
  exact SheafOfModules.module_pushforward_isRightAdjoint_of_universes
    ⟨Functor.whiskerRight (coefficientMap l E f).hom (forget₂ CommRingCat RingCat)⟩

/-- Ordinary ambient module pullback along the specified coefficient map.
Source: Stacks 03D2 (blueprint: lem-pur-integral-ambient-operation-models). -/
def pull {X Y : Scheme.{t}} (f : X ⟶ Y) := (push l E f).leftAdjoint

/-- The canonical module adjunction, fixing scalar insertion on generators.
Source: Stacks 03D7 (blueprint: lem-pur-integral-ambient-operation-models). -/
def adjunction {X Y : Scheme.{t}} (f : X ⟶ Y) : pull l E f ⊣ push l E f :=
  Adjunction.ofIsRightAdjoint _

/-- Direct image is additive since it precomposes the sectionwise linear maps.
Source: Stacks 03D2 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: addition of maps is sectionwise; coefficient restriction changes only the action. -/
@[instance]
theorem push_additive {X Y : Scheme.{t}} (f : X ⟶ Y) : (push l E f).Additive := by
  exact Functor.additive_of_preserves_binary_products (push l E f)

/-- The module pullback is additive.
Source: Stacks 03D2 (blueprint: lem-pur-integral-ambient-operation-models). -/
instance pull_additive {X Y : Scheme.{t}} (f : X ⟶ Y) : (pull l E f).Additive :=
  (adjunction l E f).left_adjoint_additive

/-- Termwise ordinary pullback, with no boundedness restriction.
Source: Stacks 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
abbrev pullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (pull l E f).mapHomologicalComplex (.up ℤ)

/-- The generalized inverse-image generator, normalized by the adjunction unit.
Source: Stacks 03D7 (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullSection {X Y : Scheme.{t}} (f : X ⟶ Y) (M : integralTowerModules l E Y)
    (V : Y.ProEt) (x : M.val.obj (op V)) :=
  ((adjunction l E f).unit.app M).val.app (op V) x

/-- Scalar insertion into the finite-operation pullback, in the existing presentation.
Source: Stacks 03EL (blueprint: lem-pur-integral-ambient-operation-models). -/
def finitePullSection {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) (i : ℤ) (V : Y.ProEt)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)) :
    ((integralOperationsLevelPullback l E f n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange f).obj V)) :=
  @SMul.smul
    ((integralCoefficientCommRingSheaf l E X n).obj.obj
      (op ((Scheme.proEtaleBaseChange f).obj V)))
    (((integralOperationsLevelPullback l E f n).obj
      (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
        (op ((Scheme.proEtaleBaseChange f).obj V))) inferInstance a
    (integralOperationsPullbackGenerator l E f n _ V
    (unrestrictedIntegralTensorSection l E Y n (P.X i) (op V) 1 x) :
      ((integralOperationsLevelPullback l E f n).obj
        (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i)).val.obj
          (op ((Scheme.proEtaleBaseChange f).obj V)))

/-- The source strict tower is completion of ordinary pullback.
Source: Stacks 06YY, 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  pullComplex l E f ⋙ IntegralOnSlice.tower l E X none

/-- The source tensor tower uses the direct-sum total tensor complex.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTower (W : Scheme.{t}) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) ⋙ IntegralOnSlice.tower l E W none

/-- The normalized scalar-association isomorphism of whole strict pullback towers.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the coefficient square commutes by coefficientMap's projections. In degree i
send (r tensor x) tensor a to pi_n(r)a tensor (x tensor 1); the inverse sends
 a tensor (x tensor b) to (1 tensor x) tensor a c_n(b). Balancing proves both
composites are identities. The maps commute with differentials and chain maps.
Reduction of a gives the same formula on both paths of every quotient transition.
This determines the unique natural strict tower isomorphism. -/
theorem pullTowerModel {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! b : pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f,
      ∀ (P : CochainComplex (integralTowerModules l E Y) ℤ) (n : ℕ) (i : ℤ)
        (V : Y.ProEt) (a : (integralCoefficientCommRingSheaf l E X n).obj.obj
          (op ((Scheme.proEtaleBaseChange f).obj V))) (x : (P.X i).val.obj (op V)),
        (((b.hom.app P).app (op n)).f i).val.app
            (op ((Scheme.proEtaleBaseChange f).obj V))
          (IntegralOnSlice.generator l E X none n ((pull l E f).obj (P.X i))
            (op ((Scheme.proEtaleBaseChange f).obj V)) a (pullSection l E f (P.X i) V x)) =
          finitePullSection l E f n P i V a x := by
  sorry

/-- The normalized balanced-tensor isomorphism of whole strict tensor towers.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: in bidegree (p,q) send (x tensor y) tensor a to
(x tensor a) tensor (y tensor 1); the inverse multiplies the two coefficients.
The tensor universal property and direct sums extend these inverse maps. Both
sides have differential dx tensor y + (-1)^p x tensor dy, with unchanged a.
The formulas commute with all quotient transitions and with both input chain maps. -/
theorem tensorTowerModel (W : Scheme.{t}) :
    ∃! d : tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W,
      ∀ (P Q : CochainComplex (integralTowerModules l E W) ℤ) (n : ℕ) (p q : ℤ)
        (V : W.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E W n).obj.obj V)
        (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
        (((d.hom.app (P, Q)).app (op n)).f (p + q)).val.app V
          (IntegralOnSlice.generator l E W none n _ V a
            (coefficientTensorGenerator.{u, t + 1, t} (Scheme.ProEt.topology W)
              (completedIntegralCommRingSheafUnrestricted l E W) P Q p q (p + q) rfl V x y)) =
          integralOperationsTotalTensorSection l E W n P Q p q V
            (unrestrictedIntegralTensorSection l E W n (P.X p) V a x)
            (unrestrictedIntegralTensorSection l E W n (Q.X q) V 1 y) := by
  sorry


/-- The uniquely normalized strict pullback comparison.
Source: Stacks 03EL, 06YY (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullTowerIso {X Y : Scheme.{t}} (f : X ⟶ Y) :
    pullTower l E f ≅ integralOperationsPullbackTowerFunctor l E f :=
  (pullTowerModel l E f).exists.choose

/-- The uniquely normalized strict tensor comparison.
Source: Stacks 03EL, 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorTowerIso (W : Scheme.{t}) :
    tensorTower l E W ≅ integralOperationsTensorTowerFunctor l E W :=
  (tensorTowerModel l E W).exists.choose

/-- The operation augmentation, with finite components given by scalar insertion.
The preceding normalization gives (r tensor x) ↦ pi_n(r) tensor (x tensor 1).
Source: Stacks 03EL, 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def pullOperationUnit {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    (pullComplex l E f).obj P ⟶
      integralOperationsRoos ((integralOperationsPullbackTowerFunctor l E f).obj P) :=
  IntegralOnSlice.roosUnit l E X none ((pullComplex l E f).obj P) ≫
    integralOperationsRoosFunctor.map ((pullTowerIso l E f).hom.app P)

/-- The tensor operation augmentation, with finite components
x tensor y ↦ (x tensor 1) tensor (y tensor 1).
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorOperationUnit (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    (coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q) ⟶
        integralOperationsRoos ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)) :=
  IntegralOnSlice.roosUnit l E W none _ ≫
    integralOperationsRoosFunctor.map ((tensorTowerIso l E W).hom.app (P, Q))

attribute [local irreducible] coefficientTotalTensor
  coefficientMap push pull pullTowerIso tensorTowerIso
  IntegralOnSlice.duality IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit IntegralOnSlice.roosUnit HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted unrestrictedIntegralReductionExistence

open CochainComplex CochainComplex.HomComplex in
private theorem roosMap_coordinates
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    integralOperationsRoosMap a ≫ mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')) =
      mappingCocone.fst (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)) ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (integralOperationsRoosMap a).f p ≫
          (mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h =
        (mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h ≫
            (Limits.Pi.map (fun n : ℕ ↦ a.app (op n))).f q := by
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square a)]
  let φ := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)
  let ψ := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')
  let b := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  let c := mappingCone.map φ ψ b b (integralOperationsRoos_square a)
  have hc₁ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.fst ψ).1.v (p + -1) p (by omega) =
      (mappingCone.fst φ).1.v (p + -1) p (by omega) ≫ b.f p := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  have hc₂ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.snd ψ).v (p + -1) (p + -1) (add_zero _) =
      (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) ≫ b.f (p + -1) := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  constructor
  · apply HomologicalComplex.hom_ext
    intro p
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫ (mappingCocone.fst ψ).f p =
      (mappingCocone.fst φ).f p ≫ b.f p
    simp [mappingCocone.fst,
      Cochain.leftShift_v (mappingCone.fst ψ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega),
      Cochain.leftShift_v (mappingCone.fst φ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega)]
    erw [Category.id_comp, Category.id_comp]
    exact hc₁ p
  · intro p q h
    obtain rfl : q = p + -1 := h.symm
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫
      (mappingCocone.snd ψ).v p (p + -1) h =
        (mappingCocone.snd φ).v p (p + -1) h ≫ b.f (p + -1)
    simp [mappingCocone.snd,
      Cochain.leftShift_v (mappingCone.snd ψ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      Int.negOnePow_even 2 ⟨1, rfl⟩]
    erw [Category.id_comp, Category.id_comp]
    exact hc₂ p

private theorem roosUnit_fst (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none) :
    IntegralOnSlice.roosUnit l E W none P ≫ CochainComplex.mappingCocone.fst
      (towerTransitionEndomorphism
        (K := fun n ↦ ((IntegralOnSlice.tower l E W none).obj P).obj (op n))
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E W none).obj P))) =
      IntegralOnSlice.productAugmentation l E W none P := by
  unfold IntegralOnSlice.roosUnit integralOperationsRoos
  exact CochainComplex.mappingCocone.lift_fst _ _ _ _

private theorem roosUnit_snd (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none)
    (p q : ℤ) (h : p + -1 = q) :
    (IntegralOnSlice.roosUnit l E W none P).f p ≫
      (CochainComplex.mappingCocone.snd (towerTransitionEndomorphism
        (K := fun n ↦ ((IntegralOnSlice.tower l E W none).obj P).obj (op n))
        (integralOperationsTowerStep ((IntegralOnSlice.tower l E W none).obj P)))).v p q h =
      0 := by
  unfold IntegralOnSlice.roosUnit integralOperationsRoos
  exact CochainComplex.mappingCocone.lift_f_snd_v _ _ _ _ p q h

private theorem roosMap_zero_snd
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C')
    {P : CochainComplex A ℤ} (c : P ⟶ integralOperationsRoos C)
    (p q : ℤ) (h : p + -1 = q)
    (hc : c.f p ≫ (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h = 0) :
    (c ≫ integralOperationsRoosMap a).f p ≫ (CochainComplex.mappingCocone.snd
      (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h = 0 := by
  rw [HomologicalComplex.comp_f, Category.assoc, (roosMap_coordinates a).2 p q h,
    ← Category.assoc, hc, zero_comp]

private theorem roosUnit_map_snd (W : Scheme.{t})
    (P : IntegralOnSlice.Cx l E W none)
    {C : ℕᵒᵖ ⥤ IntegralOnSlice.Cx l E W none}
    (a : (IntegralOnSlice.tower l E W none).obj P ⟶ C)
    (p q : ℤ) (h : p + -1 = q) :
    (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a).f p ≫
      (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C))).v p q h = 0 := by
  exact roosMap_zero_snd a (IntegralOnSlice.roosUnit l E W none P) p q h
    (roosUnit_snd l E W P p q h)

private theorem ambientRoosUnit_coordinates (W : Scheme.{t})
    (P : CochainComplex (integralTowerModules l E W) ℤ)
    {C : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ}
    (a : (IntegralOnSlice.tower l E W none).obj P ⟶ C) :
    (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a) ≫
      CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
          (integralOperationsTowerStep C)) =
      IntegralOnSlice.productAugmentation l E W none P ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (IntegralOnSlice.roosUnit l E W none P ≫ integralOperationsRoosMap a).f p ≫
        (CochainComplex.mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
            (integralOperationsTowerStep C))).v p q h = 0 := by
  constructor
  · rw [Category.assoc, (roosMap_coordinates a).1, ← Category.assoc, roosUnit_fst]
  · exact roosUnit_map_snd l E W P a

/-- The pullback tower comparison carries the quotient augmentation to the operation
augmentation, including its zero shifted-product coordinate.
Source: Stacks 03EL, 0941 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the nth quotient unit sends z to z tensor 1. The normalized scalar association
sends this to the defining finite pullback insertion. Strict tower maps induce the
same product map on both cone coordinates. They therefore preserve the zero second
cochain, while the unshifted coordinate is the product of the finite insertions. -/
theorem pullOperationUnit_coordinates {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ) :
    pullOperationUnit l E f P ≫ CochainComplex.mappingCocone.fst
      (C := integralTowerModules l E X)
      (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
        (integralOperationsTowerStep ((integralOperationsPullbackTowerFunctor l E f).obj P))) =
      IntegralOnSlice.productAugmentation l E X none ((pullComplex l E f).obj P) ≫
        Limits.Pi.map (fun n : ℕ ↦ ((pullTowerIso l E f).hom.app P).app (op n)) ∧
    ∀ (p q : ℤ) (h : p + (-1) = q),
      (pullOperationUnit l E f P).f p ≫
        (CochainComplex.mappingCocone.snd
          (C := integralTowerModules l E X) (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ ((integralOperationsPullbackTowerFunctor l E f).obj P).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsPullbackTowerFunctor l E f).obj P)))).v p q h = 0 := by
  have hc := roosMap_coordinates ((pullTowerIso l E f).hom.app P)
  dsimp only [pullTower, Functor.comp_obj] at hc
  constructor
  · dsimp only [pullOperationUnit, integralOperationsRoosFunctor]
    rw [Category.assoc, hc.1, ← Category.assoc]
    rw [roosUnit_fst]
  · intro p q h
    dsimp only [pullOperationUnit, integralOperationsRoosFunctor]
    exact roosMap_zero_snd ((pullTowerIso l E f).hom.app P)
      (IntegralOnSlice.roosUnit l E X none ((pullComplex l E f).obj P)) p q h
      (roosUnit_snd l E X ((pullComplex l E f).obj P) p q h)

/-- The analogous tensor augmentation equation retains the zero shifted-product part.
Source: Stacks 03EL, 07A4, 0941 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: x tensor y maps to (x tensor y) tensor 1, hence under the normalized comparison
to (x tensor 1) tensor (y tensor 1). The strict Roos map is diagonal on product
coordinates, so its shifted-product component remains zero in every degree. -/
theorem tensorOperationUnit_coordinates (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ) :
    tensorOperationUnit l E W P Q ≫ CochainComplex.mappingCocone.fst
      (C := integralTowerModules l E W)
      (towerTransitionEndomorphism
        (K := fun n : ℕ ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n))
        (integralOperationsTowerStep ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)))) =
      IntegralOnSlice.productAugmentation l E W none
        ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) ≫
        Limits.Pi.map (fun n : ℕ ↦ ((tensorTowerIso l E W).hom.app (P, Q)).app (op n)) ∧
    ∀ (p q : ℤ) (h : p + (-1) = q),
      (tensorOperationUnit l E W P Q).f p ≫
        (CochainComplex.mappingCocone.snd
          (C := integralTowerModules l E W) (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ ((integralOperationsTensorTowerFunctor l E W).obj (P, Q)).obj (op n))
          (integralOperationsTowerStep
            ((integralOperationsTensorTowerFunctor l E W).obj (P, Q))))).v p q h = 0 := by
  simpa only [tensorOperationUnit, integralOperationsRoosFunctor] using
    ambientRoosUnit_coordinates l E W
      ((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q))
      ((tensorTowerIso l E W).hom.app (P, Q))

/-- Ordinary pullback carries flat-term K-flat representatives to such representatives.
Source: Stacks 0G7E (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the module inverse image is the geometric inverse image followed by scalar
extension along coefficientMap. Apply ringed-topos K-flat pullback to this presentation;
flatness of its terms follows from the same ringed pullback theorem. -/
theorem pull_good {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P : CochainComplex (integralTowerModules l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) :
    IntegralOnSlice.Good l E X none ((pullComplex l E f).obj P) := by
  sorry

attribute [local semireducible] coefficientTotalTensor

/-- The direct-sum total tensor of two good representatives is good.
Source: Stacks 07A2, 07A4 (blueprint: lem-pur-integral-ambient-operation-models).
Proof: the total tensor of K-flat complexes is K-flat. Its terms are direct sums
of tensor products of flat module sheaves and are therefore flat. No boundedness
or product totalization is involved. -/
theorem tensor_good (W : Scheme.{t})
    (P Q : CochainComplex (integralTowerModules l E W) ℤ)
    (hP : integralOperationsGoodComplex l E W P)
    (hQ : integralOperationsGoodComplex l E W Q) :
    IntegralOnSlice.Good l E W none
      ((coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P, Q)) := by
  let : EssentiallySmall.{max u (t + 1)} W.ProEt := essentiallySmallSelf _
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P Q hP.1 hQ.1 hP.2 hQ.2
  exact ⟨h.1, h.2.1⟩

/-- The recorded ordinary derived tensor comparison on good representatives.
Source: Stacks 07A4 (blueprint: lem-pur-integral-ambient-operation-models). -/
def tensorRepresentative (W : Scheme.{t})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (IntegralOnSlice.duality l E W none).closed
    (IntegralOnSlice.duality l E W none).models P.obj Q.obj P.property.1 Q.property.1

attribute [local irreducible] integralDerivedPullback integralCompletedTensor
  integralDerivedPullbackComparison integralCompletedTensorComparison
  integralOperationsPullbackTowerFunctor integralOperationsTensorTowerFunctor
  integralOperationsGoodComplex tensorRepresentative

/-- Completion of ordinary ambient pullback and tensor is precisely the recorded
finite-quotient integral pullback and completed tensor, naturally on all derived objects.
The equalities specify that these are the derived limits of pullTowerIso and
 tensorTowerIso, and identify both operation augmentations, including their zero
shifted-product coordinates recorded above.
Source: Stacks 06YY, 0G7E, 07A4, 0941; sites-modules.tex, 03EL
(blueprint: lem-pur-integral-ambient-operation-models).

Proof: (1) construct the completed coefficient map from its finite projections;
coefficientMap_existsUnique does not commute inverse image with a limit.
(2) Choose flat-term K-flat resolutions (lem-pc-kflat-resolution). Ordinary pullback
and total tensor preserve these representatives (0G7E, 07A2).
(3) The normalized balanced scalar-association maps give pullTowerIso, with inverse
multiplying the finite scalar factors (def-pur-cochain-coefficient-arrows).
(4) The tensor-reduction comparison gives tensorTowerIso on direct-sum total complexes.
(5) Reduction of each scalar verifies the equations for all strict quotient transitions.
(6) K-flat change of rings computes every finite pullback and tensor simultaneously;
exact restriction of scalars retains these computations.
(7) Apply strict-tower derived inverse limit to the whole tower isomorphisms.
(8) The quotient units become the operation units; the diagonal Roos map preserves
the zero shifted coordinate, as in the two coordinate theorems above.
(9) Exact countable products on the pro-etale site and strict Roos derivation identify
these cone maps with total derived inverse limit, with the same augmentations.
(10) Naturality in chain maps and inverse quasi-isomorphisms descends through the
resolving representative localization (lem-weil-pbc-resolving-representative-whiskering
and the quasi-isomorphism calculus of fractions). The counit normalization computes
arbitrary resolutions by inverting their quasi-isomorphisms. Both tensor variables
vary, and neither completeness nor constructibility nor boundedness is assumed. -/
theorem integralAmbientOperationModels {X Y : Scheme.{t}} (f : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ (F : DerivedCategory (integralTowerModules l E Y) ⥤
        DerivedCategory (integralTowerModules l E X))
      (ε : DerivedCategory.Q ⋙ F ⟶ pullComplex l E f ⋙ DerivedCategory.Q)
      (α : F ⋙ IntegralOnSlice.completion l E X none ≅ integralDerivedPullback l E f),
      F.IsLeftDerivedFunctor ε
        (HomologicalComplex.quasiIso (integralTowerModules l E Y) (.up ℤ)) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        IsIso (ε.app P.obj)) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        α.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          (IntegralOnSlice.completion l E X none).map (ε.app P.obj) ≫
            (IntegralOnSlice.completionComparison l E X none).hom.app
              ⟨(pullComplex l E f).obj P.obj, pull_good l E f P.obj P.property⟩ ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map ((pullTowerIso l E f).hom.app P.obj))) ∧
      (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (IntegralOnSlice.completionUnit l E X none).app (F.obj (DerivedCategory.Q.obj P.obj)) ≫
            α.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (integralDerivedPullbackComparison l E f).hom.app P =
          ε.app P.obj ≫ DerivedCategory.Q.map (pullOperationUnit l E f P.obj)) ∧
      ∀ W : Scheme.{t}, W = X ∨ W = Y →
        ∃ β : (IntegralOnSlice.duality l E W none).closed.tensor ⋙
            IntegralOnSlice.completion l E W none ≅ integralCompletedTensor l E W,
          (∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
            β.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
                (integralCompletedTensorComparison l E W).hom.app (P, Q) =
              (IntegralOnSlice.completion l E W none).map
                (tensorRepresentative l E W P Q).inv ≫
              (IntegralOnSlice.completionComparison l E W none).hom.app
                ⟨_, tensor_good l E W P.obj Q.obj P.property Q.property⟩ ≫
              DerivedCategory.Q.map (integralOperationsRoosFunctor.map
                ((tensorTowerIso l E W).hom.app (P.obj, Q.obj)))) ∧
          (∀ P Q : (integralOperationsGoodComplex l E W).FullSubcategory,
            (IntegralOnSlice.completionUnit l E W none).app
                ((IntegralOnSlice.duality l E W none).closed.tensor.obj
                  (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj)) ≫
                β.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
                (integralCompletedTensorComparison l E W).hom.app (P, Q) =
              (tensorRepresentative l E W P Q).inv ≫
                DerivedCategory.Q.map (tensorOperationUnit l E W P.obj Q.obj)) := by
  sorry

end WeilConjectures.IntegralAmbient
