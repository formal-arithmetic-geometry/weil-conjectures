/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import Sheaf.Paper.CondensedERealization
public import WeilConjectures.TateTwist.ProEtale
public import Sheaf.Paper.PurTwistSheafLocallyFree
public import Sheaf.Paper.CompletedRlimFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf
public import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.CondensedZlReduction
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProEtaleReplete
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
public import Sheaf.Paper.CompletedCondensedCoefficients
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.Paper.AdicCoefficientDatum

/-!
# Realization of the reconstructed positive Tate tower

Source: main-20261015, smooth purity, rational-and-qbar-purity proof, Step 2;
Bhatt--Scholze, Sections 3.1 and 6.8; Stacks 03EK, 06YU and 0941
(blueprint: lem-pur-condensed-tate-realization).

## Main statements

* `condensed_tate_realization`: the projection-normalized ambient realization isomorphism.
* `integralComparison_existsUnique`: the coefficient-ring comparison fixed by inclusion.
* `balancedPower_existsUnique`: the balanced tensor maps fixed on all generators and the unit.

## Main constructions

* `finiteTower`, `reconstructed`, `shiftedReconstructed`: the specified positive strict tower.
* `realized`, `shiftedComparison`: the recorded J-realization and its canonical comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open WeilConjectures WeilConjectures.CondensedERealization
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedTateRealization

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- Q_l in the coefficient universe, with its canonical down equivalence.
Source: blueprint realization, coefficient-size convention
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev LiftedQ := ULift.{u} ℚ_[l]

/-- The lifted field carries the original norm and metric.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
instance liftedQNormedField : NormedField (LiftedQ.{u} l) :=
  NormedField.induced (ULift.{u} ℚ_[l]) ℚ_[l]
    (ULift.ringEquiv : ULift.{u} ℚ_[l] ≃+* ℚ_[l]).toRingHom ULift.down_injective

/-- The lift is the same normed Q_l-algebra.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization). -/
instance liftedQNormedAlgebra : NormedAlgebra ℚ_[l] (LiftedQ.{u} l) where
  toAlgebra := inferInstanceAs (Algebra ℚ_[l] (ULift.{u} ℚ_[l]))
  norm_smul_le a x := norm_smul_le a x.down

/-- Universe lifting preserves the one-dimensional coefficient field.
Source: blueprint realization, coefficient transport
(blueprint: lem-pur-condensed-tate-realization).
Proof: ULift.moduleEquiv is a Q_l-linear equivalence with Q_l, whose dimension is one. -/
@[instance] theorem liftedQ_finite : FiniteDimensional ℚ_[l] (LiftedQ.{u} l) := by
  sorry

/-- The completed integral coefficient ring of the recorded realization.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev CompletedRing : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  pbcAdicCompletion X (pbcIntegralDatum l (LiftedQ.{u} l))

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

/-- The integral coefficient ring in the actual Tate construction.
Source: archived TateTwist/ProEtale, integral coefficient
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev R : Sheaf (ProEt.topology X) Ab.{u + 1} :=
  condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X

/-- Internal modules over the pulled-back integral ring.
Source: Bhatt--Scholze 6.8.1 (blueprint: lem-pur-condensed-tate-realization). -/
abbrev IntegralModules : Type (u + 2) := Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (R X l)

/-- Inclusion of the integral condensed coefficient into its rationalization.
Source: blueprint coefficient comparison, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def integralToRational :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.padicIntCondensedRingToPadicCondensedRing l ≫
          rationalLiftRingMap l)) X

/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: Both factors are morphisms of sheaves of rings. Forgetting to abelian sheaves
retains their unit and multiplication equations, and coefficientMap is the strong
monoidal point inverse image. It therefore retains these equations. -/
@[instance] theorem integralToRational_isMonHom : IsMonHom (integralToRational X l) := by
  sorry

/-- The rational bottom-field inclusion into the finite-extension-valued closure.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def rationalToQbar :=
  coefficientMap
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (rationalDownRingMap l ≫
          Profinite.padicCondensedRingToPadicSubfieldCondensedRing l
          (⊥ : IntermediateField ℚ_[l] (PadicAlgCl l)) ≫
            Profinite.padicSubfieldCondensedRingToPadicAlgCl l ⟨⊥, inferInstance⟩)) X

/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: The lift-down map, bottom-field inclusion and finite-extension-colimit inclusion
are ring morphisms. Their composite preserves unit and multiplication. Strong
monoidal inverse image preserves both equations. -/
@[instance] theorem rationalToQbar_isMonHom : IsMonHom (rationalToQbar X l) := by
  sorry

/-- Scalar extension along the coefficient-field inclusion is exact.
Source: Stacks 06YU and the finite-extension-valued coefficient comparison in
`prop-weil-pbc-qbar-condensed-two-colimit` (blueprint: lem-pur-condensed-tate-realization).
The map is a field extension on every pro-etale section, hence tensoring with it
preserves finite limits in the module categories. -/
theorem rationalToQbar_preservesFiniteLimits :
    PreservesFiniteLimits (Mod.extendScalars (rationalToQbar X l)) := by
  sorry

/-- The section-ring comparison is pinned by its map into rational coefficients.
Source: blueprint realization, Step 1 and its coefficient-limit comparisons
(blueprint: lem-pur-condensed-tate-realization).
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

/-- The unique integral-ring identification fixed by rational inclusion.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def integralComparison (r : At l (LiftedQ.{u} l) X) :=
  (integralComparison_existsUnique X l r).exists.choose

/-- The existing sectionwise module equivalence, with the normalized coefficient change.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization). -/
def integralEncoding (r : At l (LiftedQ.{u} l) X) :=
  (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (ProEt.topology X) (R X l)).trans
    (ringModuleEquivalenceOfIso X
      ((adicLisseForget X).mapIso (integralComparison X l r)).symm)

/-- The finite constant coefficient as an integral module: R/ell^(n+1).
Source: blueprint realization, Steps 1 and 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteUnit (n : ℕ) : IntegralModules X l :=
  cokernel ((l ^ (n + 1)) • 𝟙 (𝟙_ (IntegralModules X l)))

/-- The quotient transition square for consecutive positive exponents commutes.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization).
Proof: composing multiplication by ell with multiplication by ell^(n+1)
is multiplication by ell^(n+2). Composition with the identity changes nothing. -/
theorem finiteUnit_square (n : ℕ) :
    ((l ^ (n + 2)) • 𝟙 (𝟙_ (IntegralModules X l))) ≫ 𝟙 _ =
      (l • 𝟙 (𝟙_ (IntegralModules X l))) ≫
        ((l ^ (n + 1)) • 𝟙 (𝟙_ (IntegralModules X l))) := by
  sorry

/-- Quotient reduction, not a freely chosen transition.
Source: blueprint realization, Step 1
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteUnitTransition (n : ℕ) : finiteUnit X l (n + 1) ⟶ finiteUnit X l n :=
  cokernel.map _ _ (l • 𝟙 _) (𝟙 _) (finiteUnit_square X l n)

/-- Positive finite twists, tensoring over R; the zero power is the finite quotient.
Since the root module is killed by ell^(n+1), these tensors equal the tensors over
(Z/ell^(n+1))_X. Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteLevel (n : ℕ) : ℕ → IntegralModules X l
  | 0 => finiteUnit X l n
  | d + 1 => finiteLevel n d ⊗ tateModuleLevel X l (n + 1)

/-- Quotient and root-power transitions in every tensor factor.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteTransition (n : ℕ) : ∀ d : ℕ, finiteLevel X l (n + 1) d ⟶ finiteLevel X l n d
  | 0 => finiteUnitTransition X l n
  | d + 1 => finiteTransition n d ⊗ₘ tateModuleTransition X l (n + 1)

/-- The precise positive-index strict Tate tower; n means exponent n+1.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def finiteTower (d : ℕ) : ℕᵒᵖ ⥤ IntegralModules X l :=
  Functor.ofOpSequence (X := fun n ↦ finiteLevel X l n d)
    (fun n ↦ finiteTransition X l n d)

/-- Tensor powers of the integral limit line, including its tensor unit.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def integralPower : ℕ → IntegralModules X l
  | 0 => 𝟙_ _
  | d + 1 => integralPower d ⊗ tateModule X l

/-- The tensor of the specified positive limit projections.
Source: blueprint realization, Step 4
(blueprint: lem-pur-condensed-tate-realization). -/
def powerProjection (n : ℕ) : ∀ d : ℕ, integralPower X l d ⟶ finiteLevel X l n d
  | 0 => cokernel.π _
  | d + 1 => powerProjection n d ⊗ₘ limit.π (tateModuleSystem X l) (op (n + 1))

/-- The tensor projections commute with the quotient and root-power transitions.
Source: blueprint realization, Steps 3 and 4
(blueprint: lem-pur-condensed-tate-realization).
Proof: at d=0 this is the cokernel-map equation. At a successor, tensor the
induction equation with the cone equation for the actual Tate module system. -/
theorem powerProjection_compatible (n d : ℕ) :
    powerProjection X l (n + 1) d ≫ finiteTransition X l n d =
      powerProjection X l n d := by
  sorry

/-- The coefficient encoding is additive, since it is an equivalence of abelian categories.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization).
Proof: the section-module equivalence preserves addition on underlying maps; restriction
along the inverse ring isomorphism does also. Their composite is therefore additive. -/
@[instance] theorem integralEncoding_additive (r : At l (LiftedQ.{u} l) X) :
    (integralEncoding X l r).functor.Additive := by
  sorry

/-- Additivity of the reverse encoding.
Source: blueprint realization, Steps 1 and 3
(blueprint: lem-pur-condensed-tate-realization).
Proof: the inverse section-module equivalence and inverse ring transport preserve
addition of maps. Their composite is the inverse encoding. -/
@[instance] theorem integralEncoding_inverseAdditive (r : At l (LiftedQ.{u} l) X) :
    (integralEncoding X l r).inverse.Additive := by
  sorry

attribute [instance] At.encodingAdditive At.encodingInverseAdditive

/-- Apply the existing coefficient equivalence to the entire strict tower.
Source: blueprint realization, Steps 1, 3 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def encodedTower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  finiteTower X l d ⋙ (integralEncoding X l r).functor

/-- The unshifted reconstructed object is the actual functorial derived limit.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def reconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (completedRlim X (CompletedRing X l)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d))

/-- The specified reconstructed object M_d, with cohomological shift 2d.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def shiftedReconstructed (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (shiftFunctor _ (2 * d : ℤ)).obj (reconstructed X l r d)

/-- The encoded projections satisfy naturality for the actual strict-tower steps.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization).
Proof: Functor.ofOpSequence_map_homOfLE_succ identifies the step of finiteTower
with finiteTransition. The step of encodedTower is its image under integralEncoding.
The constant tower has identity steps. Apply integralEncoding.functor.map to
powerProjection_compatible, use map_comp, and remove the identity composition. -/
theorem augmentation_compatible (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    𝟙 ((integralEncoding X l r).functor.obj (integralPower X l d)) ≫
        (integralEncoding X l r).functor.map (powerProjection X l n d) =
      (integralEncoding X l r).functor.map (powerProjection X l (n + 1) d) ≫
        (encodedTower X l r d).map (homOfLE (n.le_add_right 1)).op := by
  sorry

/-- The cone of the original tensor projections, transported without changing maps.
Source: blueprint realization, Steps 4 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def augmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (Functor.const ℕᵒᵖ).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        encodedTower X l r d :=
  NatTrans.ofOpSequence
    (fun n ↦ (integralEncoding X l r).functor.map (powerProjection X l n d))
    (fun n ↦ augmentation_compatible X l r d n)

/-- The canonical constant-tower/derived-limit adjunction.
Source: Stacks 079P, blueprint realization Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def limitAdjunction :
    (Functor.const ℕᵒᵖ :
      pbcModules X (CompletedRing X l) ⥤ _).mapDerivedCategory ⊣
      completedRlim X (CompletedRing X l) :=
  (constLimAdj : (Functor.const ℕᵒᵖ :
    pbcModules X (CompletedRing X l) ⥤ _) ⊣
      completedTowerLimit X (CompletedRing X l)).mapDerivedCategoryRightDerivedAdjunction

/-- The derived augmentation, obtained by transposing the actual cone.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def derivedAugmentation (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
        reconstructed X l r d :=
  (limitAdjunction X l).homEquiv _ _
    (((Functor.const ℕᵒᵖ).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
      (DerivedCategory.singleFunctor _ 0).map (augmentation X l r d))

/-- The coefficient map used by the recorded scalar-extension realization.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def scalarMap (r : At l (LiftedQ.{u} l) X) := r.integralIso.hom ≫ r.inclusion

/-- Scalar extension through Q_l to the specified finite-extension-valued closure.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ambientRealization (r : At l (LiftedQ.{u} l) X) :=
  pbcDerivedExtend (scalarMap X l r) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse ⋙
      (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor

/-- Restriction in the reverse order is the right adjoint of scalar extension.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ambientRestriction (r : At l (LiftedQ.{u} l) X) :=
  (Mod.comap (rationalToQbar X l)).mapDerivedCategory ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor ⋙
      pbcDerivedRestrict (scalarMap X l r)

/-- The composite derived scalar adjunction, with its original units and counits.
Source: Stacks 06YU and blueprint realization Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def scalarAdjunction (r : At l (LiftedQ.{u} l) X) :
    ambientRealization X l r ⊣ ambientRestriction X l r :=
  ((pbcDerivedScalarAdjunction (scalarMap X l r)).comp
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.symm.toAdjunction).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (rationalToQbar X l))

/-- The literal iota U(M) in the node: realize M[1/l], then extend to Qbar.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def realized (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :=
  (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.obj
    (r.realization.functor.obj (ScalarLocalization.mk M)).obj

/-- The recorded J scalar-extension comparison, followed by the actual Qbar extension.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def realizationComparison (r : At l (LiftedQ.{u} l) X) (M : Integral l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).obj M.obj ≅ realized X l r M :=
  (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.mapIso
    (((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse.mapIso
        (r.scalarExtension.app M).symm) ≪≫
      (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.unitIso.symm.app _)


/-- The actual integral-to-closure map of the archived Tate module.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def integralToQbar := coefficientMap (Profinite.padicIntRingObjToPadicAlgCl l) X

/-- The specified coefficient map preserves the ring-object operations.
Source: blueprint realization, coefficient maps
(blueprint: lem-pur-condensed-tate-realization).
Proof: The archived padicIntRingObjToPadicAlgCl is a morphism of condensed ring objects.
The strong monoidal point inverse image retains its unit and multiplication equations. -/
@[instance] theorem integralToQbar_isMonHom : IsMonHom (integralToQbar X l) := by
  sorry

/-- Balanced tensor-power maps, fixed at the unit and on every tensor generator.
Source: blueprint realization, Steps 8 and 9
(blueprint: lem-pur-condensed-tate-realization). -/
def IsBalancedPowerFamily
    (c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d)) : Prop :=
  (c 0).hom = integralToQbar X l ∧ ∀ d : ℕ,
    Mod.tensorObjπ (integralPower X l d) (tateModule X l) ≫ (c (d + 1)).hom =
      ((c d).hom ⊗ₘ
        ((Mod.extendRestrictAdjunction (integralToQbar X l)).unit.app
          (tateModule X l)).hom) ≫
        Mod.tensorObjπ (tateTwistNat X l d) (tateTwistOne X l)

/-- The balanced comparison is unique, including its zeroth tensor power.
Source: blueprint realization, Steps 8 and 9
(blueprint: lem-pur-condensed-tate-realization).
Proof: in degree zero use the prescribed ring inclusion. At a successor the displayed
map on the two underlying sheaves is R-balanced, so descends through the tensor
coequalizer. The coequalizer projection is epic, proving uniqueness by induction.
This is the ordinary scalar-extension tensor comparison, sending
b tensor (z_1 tensor ... tensor z_d) to (b tensor z_1) tensor ... tensor (1 tensor z_d). -/
theorem balancedPower_existsUnique :
    ∃! c : ∀ d : ℕ, integralPower X l d ⟶
      (Mod.comap (integralToQbar X l)).obj (tateTwistNat X l d),
      IsBalancedPowerFamily X l c := by
  sorry

/-- The uniquely specified balanced tensor map into the actual Tate twist.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def balancedPower (d : ℕ) := (balancedPower_existsUnique X l).exists.choose d

/-- Ordinary restriction through the same coefficient maps as the derived realization.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
abbrev ordinaryRestriction (r : At l (LiftedQ.{u} l) X) :=
  Mod.comap (rationalToQbar X l) ⋙
    (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor ⋙
      pbcRestrict (scalarMap X l r)

/-- The coefficient-square-normalized ordinary map is unchanged on sections.
Source: blueprint realization, Steps 1, 3, 7 and 8
(blueprint: lem-pur-condensed-tate-realization).
Proof: the defining square for integralComparison identifies the composite scalar
restriction with restriction along integralToQbar. The section-module equivalence and
ring-isomorphism transport retain the underlying sections and restrictions. Thus the
balancedPower map is linear for precisely the completed-ring actions displayed here.
Its underlying section maps determine it uniquely. -/
theorem encodedBalancedPower_existsUnique (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    ∃! c : (integralEncoding X l r).functor.obj (integralPower X l d) ⟶
        (ordinaryRestriction X l r).obj (tateTwistNat X l d),
      ∀ (V : X.ProEtᵒᵖ) (x : (integralPower X l d).X.obj.obj V),
        c.val.app V x = (balancedPower X l d).hom.hom.app V x := by
  sorry

/-- The unique completed-coefficient form of the balanced map.
Source: blueprint realization, Step 8
(blueprint: lem-pur-condensed-tate-realization). -/
def encodedBalancedPower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :=
  (encodedBalancedPower_existsUnique X l r d).exists.choose

/-- The standard exact-functor composition comparisons for restriction.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
def restrictionComparison (r : At l (LiftedQ.{u} l) X) :
    (ordinaryRestriction X l r).mapDerivedCategory ≅ ambientRestriction X l r :=
  Functor.mapDerivedCategoryCompIso
      (Mod.comap (rationalToQbar X l) ⋙
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcRestrict (scalarMap X l r)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryCompIso (Mod.comap (rationalToQbar X l))
        (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor)
      (pbcDerivedRestrict (scalarMap X l r))

/-- Derive the specified ordinary balanced map and use the standard single comparison.
Source: blueprint realization, Steps 7 and 8
(blueprint: lem-pur-condensed-tate-realization). -/
def derivedBalancedPower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    (DerivedCategory.singleFunctor _ 0).obj
        ((integralEncoding X l r).functor.obj (integralPower X l d)) ⟶
      (ambientRestriction X l r).obj (tateTwistDerived X l (d : ℤ)) :=
  (DerivedCategory.singleFunctor _ 0).map (encodedBalancedPower X l r d) ≫
    ((ordinaryRestriction X l r).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (restrictionComparison X l r).hom.app _

/-- The actual positive-index derived-limit projection.
Source: blueprint realization, Step 6
(blueprint: lem-pur-condensed-tate-realization). -/
def reconstructedProjection (r : At l (LiftedQ.{u} l) X) (d n : ℕ) :
    reconstructed X l r d ⟶
      (DerivedCategory.singleFunctor _ 0).obj
        ((encodedTower X l r d).obj (op n)) :=
  (completedRlimProjection X (CompletedRing X l) n).app
      ((DerivedCategory.singleFunctor _ 0).obj (encodedTower X l r d)) ≫
    ((reductionTowerEvaluation X
      (reductionModuleRing X (CompletedRing X l)) n).mapDerivedCategorySingleFunctor 0).hom.app _

/-- Canonical reductions mean the given derived-limit projections factor through the
scalar-extension unit by isomorphisms, retaining the completed-ring action.
Source: blueprint realization, hypothesis on M_d
(blueprint: lem-pur-condensed-tate-realization). -/
def HasCanonicalReductions (r : At l (LiftedQ.{u} l) X) (d : ℕ) : Prop :=
  ∀ n : ℕ, ∃ e :
      (pbcDerivedRestrict (pbcAdicProjection X (pbcIntegralDatum l (LiftedQ.{u} l)) n)).obj
        ((pbcCompletedReduction X (pbcIntegralDatum l (LiftedQ.{u} l)) n).obj
          (shiftedReconstructed X l r d)) ≅
      (shiftFunctor _ (2 * d : ℤ)).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((encodedTower X l r d).obj (op n))),
    (pbcDerivedScalarAdjunction
        (pbcAdicProjection X (pbcIntegralDatum l (LiftedQ.{u} l)) n)).unit.app
          (shiftedReconstructed X l r d) ≫ e.hom =
      (shiftFunctor _ (2 * d : ℤ)).map (reconstructedProjection X l r d n)

/-- The exact sectionwise module equivalence carries the standard derived shift comparison.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance encodingMapCommShift (r : At l (LiftedQ.{u} l) X) :
    ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.functor).CommShift ℤ := by
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.Additive := by
    infer_instance
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.Additive := by
    infer_instance
  change ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.mapDerivedCategory).CommShift ℤ
  infer_instance

/-- The inverse exact module equivalence carries the standard derived shift comparison.
Source: blueprint realization, Step 7
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance encodingInverseCommShift (r : At l (LiftedQ.{u} l) X) :
    ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).mapDerivedCategory.inverse).CommShift ℤ := by
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).functor.Additive := by
    infer_instance
  letI : (moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.Additive := by
    infer_instance
  change ((moduleEncoding l (LiftedQ.{u} l) X r.sectionIso).inverse.mapDerivedCategory).CommShift ℤ
  infer_instance

/-- The scalar-extension realization carries the canonical derived shift comparison.
Source: blueprint realization, Steps 7--9
(blueprint: lem-pur-condensed-tate-realization). -/
noncomputable instance ambientRealizationCommShift (r : At l (LiftedQ.{u} l) X) :
    (ambientRealization X l r).CommShift ℤ := by
  letI : (pbcDerivedRestrict (scalarMap X l r)).CommShift ℤ :=
    inferInstanceAs ((pbcRestrict (scalarMap X l r)).mapDerivedCategory.CommShift ℤ)
  letI : (pbcDerivedExtend (scalarMap X l r)).CommShift ℤ :=
    (pbcDerivedScalarAdjunction (scalarMap X l r)).leftAdjointCommShift ℤ
  letI : PreservesFiniteLimits (Mod.extendScalars (rationalToQbar X l)) :=
    rationalToQbar_preservesFiniteLimits X l
  letI : (Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctor.CommShift ℤ := by
    exact Functor.CommShift.ofIso
      ((Mod.extendScalars (rationalToQbar X l)).leftDerivedFunctorIsoMapDerivedCategory.symm) ℤ
  unfold ambientRealization
  infer_instance

/-- The shifted scalar comparison, formed from the recorded J comparison and the
canonical shift comparison of actual derived scalar extension.
Source: blueprint realization, Steps 7--9
(blueprint: lem-pur-condensed-tate-realization). -/
def shiftedComparison (r : At l (LiftedQ.{u} l) X) (d : ℕ)
    (hM : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l (LiftedQ.{u} l))
      (shiftedReconstructed X l r d))
    (e : (ambientRealization X l r).obj (reconstructed X l r d) ≅
      tateTwistDerived X l (d : ℤ)) :
    realized X l r ⟨shiftedReconstructed X l r d, hM⟩ ≅
      (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived X l (d : ℤ)) :=
  (realizationComparison X l r ⟨shiftedReconstructed X l r d, hM⟩).symm ≪≫
    ((ambientRealization X l r).commShiftIso (2 * d : ℤ)).app
      (reconstructed X l r d) ≪≫ (shiftFunctor _ (2 * d : ℤ)).mapIso e

/-- The reconstructed positive Tate tower realizes canonically as the actual condensed
derived Tate twist, including the unit in tensor degree zero.
Source: main-20261015, smooth purity, rational-and-qbar-purity proof Step 2;
Bhatt--Scholze 3.1.10, 6.8.2 and 6.8.4; Stacks 03EK, 06YU, 0941
(blueprint: lem-pur-condensed-tate-realization).

Proof:
1. completedCondensedIntegral and the finite-quotient and completed-constant comparisons
identify R with the completed coefficient ring, with every finite projection unchanged
[sk-prop-sfb-qlbar-colimit-x, lem-pur-condensed-zl-reduction-mod-ell-power,
lem-weil-pbc-completed-constant-sheaf-reduction].
The finite root sheaf is killed by ell^n, so r tensor z maps to rho_n(r) z, with inverse
z maps to 1 tensor z. The two composites are identities by locally lifting rho_n(r)
to an integer. These maps commute with root-power transitions. The n=0 root sheaf
mu_1 is zero; removing it preserves the limit and every positive projection.
2. The internal/sectionwise equivalence retains underlying sheaves. The locally-free
Tate-line theorem identifies the limit with a rank-one R-module. Repleteness makes
each limit projection epic. Its induced finite quotient map is an epimorphism between
locally rank-one free modules, hence invertible. Tensoring gives exactly powerProjection
and the strict finite tower, including quotient coefficients at d=0
[lem-pur-twist-sheaf-locally-free, det-pe-replete-epimorphism,
def-weil-pbc-internal-abelian-sheaf-module-equivalence].
3. Trivializing the line identifies its tensor powers with R. They are flat and their
single complexes K-flat. The tower is epimorphic. Its degree-zero limit is integralPower.
Compare its Roos triangle with the K-injective Rlim triangle using the same projections.
The levelwise-isomorphism theorem gives invertibility of derivedAugmentation;
negative Ext vanishing gives uniqueness of this projection-normalized map
[lem-pc-kflat-closure, lem-weil-proetale-surjective-tower-derived-limit,
lemma-weil-pbc-r-lim-levelwise-isomorphism,
lem-weil-pbc-ringed-strict-tower-homotopy-limit].
4. J's recorded scalarExtension computes realization on the integral object. The
canonical lift/down coefficient transport identifies the rational field with Q_l.
The K-flat line computes both scalar extensions. The actual derived adjunction unit
identifies the adjoint of the ordinary balancedPower map with its scalar-extension map.
Monoidality of ringed derived tensor pullback makes this an isomorphism to tateTwistNat
[lem-weil-pbc-condensed-e-realization, lem-pur-derived-change-of-rings,
lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-topoi-derived-tensor-pullback].
5. Invert derivedAugmentation to obtain the unique e0 satisfying the displayed equation.
The recorded realization and canonical shift comparisons give shiftedComparison, hence
the requested ambient isomorphism. At d=0 the balanced map is precisely integralToQbar,
so this is the canonical identification of the realized unit with B. The same construction
works on the empty scheme and at ell=2; no primitive root or global trivialization is chosen. -/
theorem condensed_tate_realization (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)] (T : Base k)
    (r : At l (LiftedQ.{u} l) T.scheme) (d : ℕ)
    (hM : PbcIsBoundedConstructibleComplete T.scheme
      (pbcIntegralDatum l (LiftedQ.{u} l)) (shiftedReconstructed T.scheme l r d))
    (_hred : HasCanonicalReductions T.scheme l r d) :
    ∃! e : realized T.scheme l r ⟨shiftedReconstructed T.scheme l r d, hM⟩ ≅
        (shiftFunctor _ (2 * d : ℤ)).obj (tateTwistDerived T.scheme l (d : ℤ)),
      ∃ e0 : (ambientRealization T.scheme l r).obj (reconstructed T.scheme l r d) ≅
          tateTwistDerived T.scheme l (d : ℤ),
        derivedAugmentation T.scheme l r d ≫
            (scalarAdjunction T.scheme l r).unit.app (reconstructed T.scheme l r d) ≫
            (ambientRestriction T.scheme l r).map e0.hom =
              derivedBalancedPower T.scheme l r d ∧
          e = shiftedComparison T.scheme l r d hM e0 := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedTateRealization
