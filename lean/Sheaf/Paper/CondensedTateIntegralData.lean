/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import Sheaf.Paper.CondensedERealizationDefinitions
public import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Paper.CompletedRlimFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.PurTwistSheafLocallyFree
import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
import Sheaf.Paper.CompletedCondensedCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

/-!
# Integral coefficients and the strict positive Tate tower

Source: main-20261015, smooth purity, rational-and-qbar-purity proof, Step 2;
Bhatt--Scholze, Sections 3.1 and 6.8; Stacks 03EK, 06YU and 0941
(blueprint: lem-pur-condensed-tate-realization).

## Main statements

* `integralComparison_existsUnique`: the coefficient-ring comparison fixed by inclusion.

## Main constructions

* `finiteTower`, `integralPower`: the strict finite tower and the integral tensor powers.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option linter.mathlibStandardSet false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures WeilConjectures.CondensedERealization
open scoped CategoryTheory.Obj

set_option allowUnsafeReducibility true in
attribute [local reducible] reductionModulesHasDerivedCategory
  reductionRingModulesHasDerivedCategory proEtaleRingModules_hasDerivedCategory
  reductionTowerHasDerivedCategory

attribute [local instance 40000] reductionRingModulesHasDerivedCategory
  proEtaleRingModules_hasDerivedCategory reductionTowerHasDerivedCategory

attribute [local instance 41000] reductionModulesHasDerivedCategory

attribute [local irreducible] _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard Functor.leftAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Mod.monoidalClosed DerivedCategory.monoidalClosed
  Mod.extendScalars Mod.derivedExtendMapDerivedCategoryAdjunction
  AlgebraicGeometry.ProEtale.upperStarFromPoint

attribute [local irreducible] moduleEncoding

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Q_l in the coefficient universe, with its canonical down equivalence.
Source: blueprint realization, coefficient-size convention
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev LiftedQ := ULift.{u} ℚ_[l]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The lifted field carries the original norm and metric.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
instance liftedQNormedField : NormedField (LiftedQ.{u} l) :=
  fast_instance% NormedField.induced (ULift.{u} ℚ_[l]) ℚ_[l]
    (ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).toRingHom ULift.down_injective

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The lift is the same normed Q_l-algebra.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
instance liftedQNormedAlgebra : NormedAlgebra ℚ_[l] (LiftedQ.{u} l) := inferInstance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Universe lifting preserves the one-dimensional coefficient field.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization).
Proof: ULift.moduleEquiv is a Q_l-linear equivalence with Q_l, whose dimension is one. -/
@[instance] theorem liftedQ_finite : FiniteDimensional ℚ_[l] (LiftedQ.{u} l) := by
  exact inferInstanceAs (Module.Finite ℚ_[l] (ULift.{u} ℚ_[l]))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The completed integral coefficient ring of the recorded realization.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def CompletedRing : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l (LiftedQ.{u} l))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Lift rational-valued continuous functions coefficientwise.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
def rationalLiftRingMap : Profinite.continuousMapRingSheaf ℚ_[l] ⟶
    Profinite.continuousCoefficientRingSheaf (LiftedQ.{u} l) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).symm.toRingHom.compLeftContinuous
            S.unop
            continuous_uliftUp).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Forget the coefficient lift, by the inverse continuous field map.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
def rationalDownRingMap :
    Profinite.continuousCoefficientRingSheaf (LiftedQ.{u} l) ⟶
      Profinite.continuousMapRingSheaf ℚ_[l] :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).toRingHom.compLeftContinuous
            S.unop
            continuous_uliftDown).comp ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The integral coefficient ring in the actual Tate construction.
Source: archived TateTwist/ProEtale, integral coefficient
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev R : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Internal modules over the pulled-back integral ring.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-pur-condensed-tate-realization). -/
abbrev IntegralModules : Type (u + 2) := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (R X l)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Inclusion of the integral condensed coefficient into its rationalization.
Source: blueprint coefficient comparison, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def integralToRational :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicIntCondensedRingToPadicCondensedRing l ≫
          rationalLiftRingMap l)) X

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: Both factors are morphisms of sheaves of rings. Forgetting to abelian sheaves
retains their unit and multiplication equations, and coefficientMap is the strong
monoidal point inverse image. It therefore retains these equations. -/
@[instance] theorem integralToRational_isMonHom : IsMonHom (integralToRational X l) := by
  unfold integralToRational
  infer_instance

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The rational bottom-field inclusion into the finite-extension-valued closure.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def rationalToQbar : Coefficient (LiftedQ.{u} l) X ⟶
    condensedRingObj (Profinite.padicAlgClRingObj l) X :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l
          (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≫
            Profinite.padicSubfieldCondensedRingToPadicAlgCl l ⟨⊥, inferInstance⟩)) X

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: The lift-down map, bottom-field inclusion and finite-extension-colimit inclusion
are ring morphisms. Their composite preserves unit and multiplication. Strong
monoidal inverse image preserves both equations. -/
@[instance] theorem rationalToQbar_isMonHom : IsMonHom (rationalToQbar X l) := by
  unfold rationalToQbar
  infer_instance

private theorem rationalDown_isIso : IsIso (rationalDownRingMap.{u} l) := by
  refine ⟨⟨rationalLiftRingMap l, ?_, ?_⟩⟩
  all_goals
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro f
    rfl

private theorem rationalBottom_isIso :
    IsIso (Profinite.padicCondensedRingToPadicSubfieldCondensedRing.{u} l
      (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))) := by
  let E := (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))
  let := PadicAlgCl.normedFieldOfAlgebra l E
  let e := IntermediateField.botEquiv ℚ_[l] (PadicAlgCl l)
  let g := Profinite.continuousMapRingSheafMap.{u} e.toRingHom
    e.toLinearMap.continuous_of_finiteDimensional
  refine ⟨⟨g, ?_, ?_⟩⟩
  all_goals
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
  · change e (algebraMap ℚ_[l] E (f.down x)) = f.down x
    exact e.commutes (f.down x)
  · change algebraMap ℚ_[l] E (e (f.down x)) = f.down x
    exact e.symm_apply_apply (f.down x)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Scalar extension along the coefficient-field inclusion is exact.
Source: Stacks 06YU and the finite-extension-valued coefficient comparison in
`prop-weil-pbc-qbar-condensed-two-colimit` (blueprint: lem-pur-condensed-tate-realization).
The map is a field extension on every pro-etale section, hence tensoring with it
preserves finite limits in the module categories. -/
theorem rationalToQbar_preservesFiniteLimits :
    PreservesFiniteLimits (Mod.extendScalars (rationalToQbar X l)) := by
  let E : PadicAlgCl.FiniteIntermediateField l := ⟨⊥, inferInstance⟩
  let F := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  let a : Coefficient (LiftedQ.{u} l) X ⟶ padicSubfieldRingObj X l E := coefficientMap
    (F.map (rationalDownRingMap l ≫
      Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E)) X
  let b : padicSubfieldRingObj X l E ⟶
      condensedRingObj (Profinite.padicAlgClRingObj l) X :=
    padicSubfieldRingObjToPadicAlgCl X l E
  have downIso := rationalDown_isIso.{u} l
  have bottomIso := rationalBottom_isIso.{u} l
  have aMon : IsMonHom a := by
    change IsMonHom ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E)))
    infer_instance
  have bMon : IsMonHom b := by dsimp only [b]; infer_instance
  have aIso : IsIso a := by
    have sourceIso : IsIso (rationalDownRingMap l ≫
        Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E) := by
      dsimp only [E]
      infer_instance
    change IsIso ((upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E)))
    infer_instance
  have aExact : PreservesFiniteLimits
      (Mod.extendScalars (C := Sheaf (ProEt.topology X) Ab.{u + 1}) a) :=
    preservesFiniteLimits_of_natIso
      (Mod.extendScalarsIsoComapInv (C := Sheaf (ProEt.topology X) Ab.{u + 1}) a).symm
  have bExact : PreservesFiniteLimits
      (Mod.extendScalars (C := Sheaf (ProEt.topology X) Ab.{u + 1}) b) :=
    preservesFiniteLimits_extendScalars_padicSubfieldRingObjToPadicAlgCl
      (X := X) (ℓ := l) E
  have h : rationalToQbar X l = a ≫ b := by
    let G := F ⋙ upperStarFromPoint X
    change G.map (rationalDownRingMap l ≫
        Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E ≫
        Profinite.padicSubfieldCondensedRingToPadicAlgCl l E) =
      G.map (rationalDownRingMap l ≫
        Profinite.padicCondensedRingToPadicSubfieldCondensedRing l E) ≫
      G.map (Profinite.padicSubfieldCondensedRingToPadicAlgCl l E)
    erw [← Category.assoc]
    exact G.map_comp _ _
  have compExact := comp_preservesFiniteLimits
    (Mod.extendScalars (C := Sheaf (ProEt.topology X) Ab.{u + 1}) a)
    (Mod.extendScalars (C := Sheaf (ProEt.topology X) Ab.{u + 1}) b)
  exact preservesFiniteLimits_of_natIso
    (Mod.extendScalarsIsoOfEq (C := Sheaf (ProEt.topology X) Ab.{u + 1}) h ≪≫
      Mod.extendScalarsComp (C := Sheaf (ProEt.topology X) Ab.{u + 1}) a b).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The section-ring comparison is pinned by its map into rational coefficients.
Source: blueprint realization, Step 1 and its coefficient-limit comparisons
(blueprint: lem-pur-condensed-tate-integral-comparison).
Proof: identify both integral coefficient sheaves with the limit of their finite
constant quotients, using completedCondensedIntegral and the completed-constant
comparison. On every quotient the identification sends a constant residue to itself.
Its composite into rational coefficients is the prescribed inclusion. That inclusion
is monic, so this equality determines the ring isomorphism uniquely. -/
theorem integralComparison_existsUnique (r : At l (LiftedQ.{u} l) X) :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology X) (R X l) ≅ CompletedRing X l,
      e.hom ≫ r.integralIso.hom ≫ r.inclusion =
        sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom := by
  sorry

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The unique integral-ring identification fixed by rational inclusion.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def integralComparison (r : At l (LiftedQ.{u} l) X) :=
  (integralComparison_existsUnique X l r).exists.choose

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The existing sectionwise module equivalence, with the normalized coefficient change.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization). -/
def integralEncoding (r : At l (LiftedQ.{u} l) X) :
    IntegralModules X l ≌ pbcModules X (CompletedRing X l) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (R X l)).trans
    (ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (integralComparison X l r)).symm)

attribute [local irreducible] integralEncoding

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The finite constant coefficient as an integral module: R/ell^(n+1).
Source: blueprint realization, Steps 1 and 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteUnit (n : ℕ) : IntegralModules X l :=
  cokernel ((l ^ (n + 1)) • 𝟙 (𝟙_ (IntegralModules X l)))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The quotient transition square for consecutive positive exponents commutes.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization).
Proof: composing multiplication by ell with multiplication by ell^(n+1)
is multiplication by ell^(n+2). Composition with the identity changes nothing. -/
theorem finiteUnit_square (n : ℕ) :
    ((l ^ (n + 2)) • 𝟙 (𝟙_ (IntegralModules X l))) ≫ 𝟙 _ =
      (l • 𝟙 (𝟙_ (IntegralModules X l))) ≫
        ((l ^ (n + 1)) • 𝟙 (𝟙_ (IntegralModules X l))) := by
  simp only [Category.comp_id, Preadditive.nsmul_comp, Category.id_comp, smul_smul]
  rw [show n + 2 = (n + 1) + 1 by omega, pow_succ', Nat.mul_comm]

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Quotient reduction, not a freely chosen transition.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteUnitTransition (n : ℕ) : finiteUnit X l (n + 1) ⟶ finiteUnit X l n :=
  cokernel.map _ _ (l • 𝟙 _) (𝟙 _) (finiteUnit_square X l n)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Positive finite twists, tensoring over R; the zero power is the finite quotient.
Since the root module is killed by ell^(n+1), these tensors equal the tensors over
(Z/ell^(n+1))_X. Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteLevel (n : ℕ) : ℕ → IntegralModules X l
  | 0 => finiteUnit X l n
  | d + 1 => finiteLevel n d ⊗ tateModuleLevel X l (n + 1)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Quotient and root-power transitions in every tensor factor.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteTransition (n : ℕ) : ∀ d : ℕ, finiteLevel X l (n + 1) d ⟶ finiteLevel X l n d
  | 0 => finiteUnitTransition X l n
  | d + 1 => finiteTransition n d ⊗ₘ tateModuleTransition X l (n + 1)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The precise positive-index strict Tate tower; n means exponent n+1.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteTower (d : ℕ) : ℕᵒᵖ ⥤ IntegralModules X l :=
  Functor.ofOpSequence (X := fun n ↦ finiteLevel X l n d)
    (fun n ↦ finiteTransition X l n d)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Tensor powers of the integral limit line, including its tensor unit.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def integralPower : ℕ → IntegralModules X l
  | 0 => 𝟙_ _
  | d + 1 => integralPower d ⊗ tateModule X l

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The tensor of the specified positive limit projections.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def powerProjection (n : ℕ) : ∀ d : ℕ, integralPower X l d ⟶ finiteLevel X l n d
  | 0 => cokernel.π _
  | d + 1 => powerProjection n d ⊗ₘ limit.π (tateModuleSystem X l) (op (n + 1))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The tensor projections commute with the quotient and root-power transitions.
Source: blueprint realization, Steps 3 and 4
(blueprint: lem-pur-condensed-tate-realization).
Proof: at d=0 this is the cokernel-map equation. At a successor, tensor the
induction equation with the cone equation for the actual Tate module system. -/
theorem powerProjection_compatible (n d : ℕ) :
    powerProjection X l (n + 1) d ≫ finiteTransition X l n d =
      powerProjection X l n d := by
  induction d with
  | zero =>
      dsimp only [powerProjection, finiteTransition, finiteUnitTransition, cokernel.map]
      erw [cokernel.π_desc, Category.id_comp]
      rfl
  | succ d ih =>
      change (powerProjection X l (n + 1) d ⊗ₘ
          limit.π (tateModuleSystem X l) (op (n + 2))) ≫
          (finiteTransition X l n d ⊗ₘ tateModuleTransition X l (n + 1)) =
        powerProjection X l n d ⊗ₘ limit.π (tateModuleSystem X l) (op (n + 1))
      have h := limit.w (tateModuleSystem X l) (homOfLE (Nat.le_succ (n + 1))).op
      simp only [tateModuleSystem, Functor.ofOpSequence_map_homOfLE_succ] at h
      exact (tensorHom_comp_tensorHom _ _ _ _).trans
        (congrArg₂ (fun f g ↦ f ⊗ₘ g) ih h)

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The coefficient encoding is additive, since it is an equivalence of abelian categories.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization).
Proof: the section-module equivalence preserves addition on underlying maps; restriction
along the inverse ring isomorphism does also. Their composite is therefore additive. -/
@[instance] theorem integralEncoding_additive (r : At l (LiftedQ.{u} l) X) :
    (integralEncoding X l r).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Additivity of the reverse encoding.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization).
Proof: the inverse section-module equivalence and inverse ring transport preserve
addition of maps. Their composite is the inverse encoding. -/
@[instance] theorem integralEncoding_inverseAdditive (r : At l (LiftedQ.{u} l) X) :
    (integralEncoding X l r).inverse.Additive := by
  exact (integralEncoding X l r).inverse_additive


attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Apply the existing coefficient equivalence to the entire strict tower.
Source: blueprint realization, Steps 1, 3 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def encodedTower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    ℕᵒᵖ ⥤ pbcModules X (CompletedRing X l) :=
  finiteTower X l d ⋙ (integralEncoding X l r).functor

end AlgebraicGeometry.ProEtale.CondensedTateRealization
