/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Analysis.Normed.Field.Basic
public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions
public import WeilConjectures.TateTwist.ProEtale
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive

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

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
private def baseIntegersEquiv : ℤ_[l] ≃+*
    Padic.coefficientExtensionIntegers l (LiftedQ.{u} l) := by
  let E := LiftedQ.{u} l
  let e : ℚ_[l] ≃+* E := ULift.ringEquiv.symm
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x.down‖ ≤ 1 := by
    have h := (Padic.extension_integers_dvr l E
      (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1 x
    change x ∈ Padic.coefficientExtensionIntegers l E ↔ spectralNorm ℚ_[l] E x ≤ 1 at h
    rw [← NormedAlgebra.norm_eq_spectralNorm ℚ_[l]] at h
    exact h
  let f : ℤ_[l] →+* Padic.coefficientExtensionIntegers l E :=
    { toFun := fun z ↦ ⟨e z, (hm _).mpr z.property⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun a b ↦ Subtype.ext (map_mul e _ _)
      map_zero' := Subtype.ext (map_zero e)
      map_add' := fun a b ↦ Subtype.ext (map_add e _ _) }
  exact RingEquiv.ofBijective f ⟨fun _ _ h ↦ Subtype.ext
    (e.injective (congrArg Subtype.val h)), fun y ↦
      ⟨⟨e.symm y, (hm _).mp y.property⟩, Subtype.ext (e.apply_symm_apply _)⟩⟩

-- Abstracting the field fixes the spectral topology before specializing to LiftedQ.
private def integralFunctionIso (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (e : ℤ_[l] ≃+* Padic.coefficientExtensionIntegers l E)
    (hn : ∀ z, Padic.coefficientExtensionAbsoluteValue l E (e z) = ‖z‖) :
    continuousMapRingSheaf X ℤ_[l] ≅
      (adicLisseForget X).obj (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E) := by
  letI nf := coefficientExtensionNormedField l E
  letI : TopologicalSpace E :=
    nf.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hi : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    exact hn
  have his : Isometry e.symm := by
    intro a b
    simpa only [e.apply_symm_apply] using (hi (e.symm a) (e.symm b)).symm
  let f (U : X.ProEtᵒᵖ) : ULift.{u + 1} C(U.unop.left, ℤ_[l]) →+*
      C(U.unop.left, ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
    ((ULift.ringEquiv.symm.toRingHom.comp e.toRingHom).compLeftContinuous U.unop.left
      (continuous_uliftUp.comp hi.continuous)).comp ULift.ringEquiv.toRingHom
  let g (U : X.ProEtᵒᵖ) :
      C(U.unop.left, ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) →+*
        ULift.{u + 1} C(U.unop.left, ℤ_[l]) :=
    ULift.ringEquiv.symm.toRingHom.comp
      ((e.symm.toRingHom.comp ULift.ringEquiv.toRingHom).compLeftContinuous U.unop.left
        (his.continuous.comp continuous_uliftDown))
  refine
    { hom := ⟨{ app := fun U ↦ RingCat.ofHom (f U)
                naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{ app := fun U ↦ RingCat.ofHom (g U)
                naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · ext U : 3
    apply ConcreteCategory.hom_ext
    intro z
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply (z.down x)
  · ext U : 3
    apply ConcreteCategory.hom_ext
    intro z
    apply ContinuousMap.ext
    intro x
    change C(U.unop.left, ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) at z
    exact congrArg ULift.up (e.apply_symm_apply (z x).down)

private def baseContinuousIso : continuousMapRingSheaf X ℤ_[l] ≅
    (adicLisseForget X).obj (AlgebraicGeometry.Scheme.integralCoefficientSheaf
      l X (LiftedQ.{u} l)) :=
  integralFunctionIso X l (LiftedQ l) (baseIntegersEquiv l) (fun z ↦ by
    change spectralNorm ℚ_[l] (LiftedQ.{u} l) (ULift.up (z : ℚ_[l])) = ‖z‖
    exact spectralNorm_extends (K := ℚ_[l]) (L := LiftedQ.{u} l) _)

private def integralSectionIso :
    InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (ProEt.topology X) (R X l) ≅
        AlgebraicGeometry.Scheme.integralCoefficientSheaf l X (LiftedQ.{u} l) := by
  let J := ProEt.topology X
  let B := continuousMapRingSheaf X ℤ_[l]
  let A := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj B
  letI : IsCommMonObj A := Sheaf.isCommMonObj_sheafCompose_obj J B
    (fun U a b ↦ @mul_comm (ULift.{u + 1} C(U.unop.left, ℤ_[l])) _ a b)
  let c : R X l ⟶ A := chartComparison X ℤ_[l]
  haveI : IsIso c := chartComparison_isIso X ℤ_[l]
  let e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J (R X l) ≅
      InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A :=
    { hom := sectionRingMap X c
      inv := sectionRingMap X (inv c)
      hom_inv_id := by
        ext U x
        change (inv c).hom.app U (c.hom.app U x) = x
        exact ConcreteCategory.congr_hom
          (congr_app (congrArg (fun f : R X l ⟶ R X l ↦ f.hom) (IsIso.hom_inv_id c)) U) x
      inv_hom_id := by
        ext U x
        change c.hom.app U ((inv c).hom.app U x) = x
        exact ConcreteCategory.congr_hom
          (congr_app (congrArg (fun f : A ⟶ A ↦ f.hom) (IsIso.inv_hom_id c)) U) x }
  let f : (adicLisseForget X).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} J A) ≅
        (adicLisseForget X).obj
          (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X (LiftedQ.{u} l)) :=
    reconstructedRingIso X B ≪≫ baseContinuousIso X l
  exact e ≪≫ (fullyFaithfulSheafCompose J
    CommRingCat.fullyFaithfulForget₂ToRingCat.{u + 1}).preimageIso f

private theorem integralSectionIso_value (U : X.ProEtᵒᵖ)
    (s : (R X l).obj.obj U) (x : U.unop.left) :
    (integralCoefficientValue l (LiftedQ.{u} l) X U
      ((integralSectionIso X l).hom.hom.app U s) x : LiftedQ l) =
        ULift.up (((chartComparison X ℤ_[l]).hom.app U s).down x : ℚ_[l]) := by
  rfl

private def integralRationalFunctionMap :
    (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X ℤ_[l]) ⟶
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf X (LiftedQ.{u} l)) :=
  ⟨{ app := fun _U ↦ AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up ⟨fun x ↦ ULift.up (f.down x : ℚ_[l]),
          continuous_uliftUp.comp (continuous_subtype_val.comp f.down.continuous)⟩
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
     naturality := fun _ _ _ ↦ rfl }⟩

set_option maxHeartbeats 2000000 in
set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.ProEtale.upperStarFromPoint in
private theorem integralRational_square (r : At l (LiftedQ.{u} l) X) :
    integralToRational X l ≫ r.coefficientIso.hom.hom =
      chartComparison X ℤ_[l] ≫ integralRationalFunctionMap X l := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  dsimp only [integralToRational, coefficientMap, upperStarFromPoint]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left _ r.coefficientIso.hom.hom]
  rw [adj.homEquiv_naturality_right (chartComparison X ℤ_[l])
    (integralRationalFunctionMap X l)]
  simp only [chartComparison, adj, Equiv.apply_symm_apply]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  exact r.coefficient_normalization S.unop
    ⟨fun x ↦ ULift.up (f.down x : ℚ_[l]),
      continuous_uliftUp.comp (continuous_subtype_val.comp f.down.continuous)⟩

private theorem integralValue_ext (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : X.ProEtᵒᵖ)
    (a b : (AlgebraicGeometry.Scheme.integralCoefficientSheaf l X E).obj.obj U)
    (h : ∀ x, integralCoefficientValue l E X U a x = integralCoefficientValue l E X U b x) :
    a = b := by
  let := coefficientExtensionNormedField l E
  apply ContinuousMap.ext
  intro x
  exact ULift.down_injective (h x)

private theorem rationalValue_ext (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : X.ProEtᵒᵖ)
    (a b : (rationalCoefficientSheaf l X E).obj.obj U)
    (h : ∀ x, rationalCoefficientValue l E X U a x = rationalCoefficientValue l E X U b x) :
    a = b := by
  let := coefficientExtensionNormedField l E
  apply ContinuousMap.ext
  intro x
  exact ULift.down_injective (h x)

private theorem integralInclusion_injective (r : At l (LiftedQ.{u} l) X)
    (U : X.ProEtᵒᵖ) : Function.Injective (r.inclusion.hom.app U) := by
  intro a b h
  apply integralValue_ext X l (LiftedQ l) U a b
  intro x
  apply Subtype.ext
  exact (r.inclusion_normalization U.unop a x).symm.trans
    ((congrArg (fun s ↦ rationalCoefficientValue l (LiftedQ.{u} l) X U s x) h).trans
      (r.inclusion_normalization U.unop b x))

private theorem integralSectionIso_square (r : At l (LiftedQ.{u} l) X) :
    (integralSectionIso X l).hom ≫ r.inclusion =
      sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply rationalValue_ext X l (LiftedQ l) U
  intro x
  change rationalCoefficientValue l (LiftedQ.{u} l) X U
      (r.inclusion.hom.app U ((integralSectionIso X l).hom.hom.app U s)) x = _
  rw [r.inclusion_normalization U.unop]
  change (integralCoefficientValue l (LiftedQ.{u} l) X U
      ((integralSectionIso X l).hom.hom.app U s) x : LiftedQ l) =
    rationalCoefficientValue l (LiftedQ.{u} l) X U
      (r.sectionIso.hom.hom.app U ((integralToRational X l).hom.app U s)) x
  rw [integralSectionIso_value X l U s x]
  have h := congrArg (fun f : R X l ⟶
      (sheafCompose (ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (AlgebraicGeometry.ProEtale.continuousCoefficientRingSheaf X (LiftedQ.{u} l)) ↦
          ((f.hom.app U) s).down x) (integralRational_square X l r)
  exact h.symm.trans
    (r.section_normalization U ((integralToRational X l).hom.app U s) x).symm

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The section-ring comparison is pinned by its map into rational coefficients.
Source: Hemo--Richarz--Scholbach, Example 3.1; blueprint normalized integral chart
(blueprint: lem-route-integral-comparison-exists-unique).
Proof: the lifted field's integral subring is isometrically the usual p-adic integers,
by the spectral-norm membership characterization. Transport the canonical continuous
p-adic integer chart to that subring and reconstruct its section ring. The point
adjunction and the supplied normalization of the rational chart show that this
isomorphism commutes with integral inclusion. Compose it with the inverse supplied
completion chart. Pointwise injectivity of inclusion proves uniqueness. -/
theorem integralComparison_existsUnique (r : At l (LiftedQ.{u} l) X) :
    ∃! e : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (ProEt.topology X) (R X l) ≅ CompletedRing X l,
      e.hom ≫ r.integralIso.hom ≫ r.inclusion =
        sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom := by
  let e := integralSectionIso X l ≪≫ r.integralIso.symm
  have he : e.hom ≫ r.integralIso.hom ≫ r.inclusion =
      sectionRingMap X (integralToRational X l) ≫ r.sectionIso.hom := by
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_assoc] using integralSectionIso_square X l r
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_mono r.integralIso.hom).1
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply integralInclusion_injective X l r U
  exact ConcreteCategory.congr_hom
    (congr_app (congrArg (fun f : _ ⟶ rationalCoefficientSheaf l X (LiftedQ l) ↦ f.hom)
      (he'.trans he.symm)) U) s

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
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- Apply the existing coefficient equivalence to the entire strict tower.
Source: blueprint realization, Steps 1, 3 and 6
(blueprint: lem-pur-condensed-tate-realization). -/
def encodedTower (r : At l (LiftedQ.{u} l) X) (d : ℕ) :
    ℕᵒᵖ ⥤ pbcModules X (CompletedRing X l) :=
  finiteTower X l d ⋙ (integralEncoding X l r).functor

end AlgebraicGeometry.ProEtale.CondensedTateRealization
