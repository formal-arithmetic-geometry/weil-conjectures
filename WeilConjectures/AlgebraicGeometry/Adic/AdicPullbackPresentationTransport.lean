/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction
public import WeilConjectures.Algebra.Homology.SixFunctors.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedRlimFunctor
public import WeilConjectures.ProperBaseChange.ConstantCompletionEquivalence
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.CategoryTheory.Adjunction.Mates

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientTransitionCompatibility
import all WeilConjectures.Algebra.Homology.ProperBaseChange.DiagramKFlatReplacements
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.CategoryTheory.StrictReduction.ReductionPullbackDerivedTower
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import WeilConjectures.CategoryTheory.ModuleInverseImageAction
import WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageScalarGraph
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
public import WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels
import all WeilConjectures.AlgebraicGeometry.Adic.AdicPullbackPresentationModels
/-!
# Counit-normalized transport of adic pullback presentations

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md; Stacks Tags 05S7 and 03DI.
(blueprint: lem-cbc-adic-pullback-presentation-transport).

The coefficient uniqueness statement first identifies both presentations with the published
coefficient map. The subsequent statements use these identifications to write both universal
pairs over the same ordinary functor. No invertibility of the completed coefficient map is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {A : Type (u + 1)} [CommRing A]
  (d : AdicCoefficientDatum A)

section Pairs
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]

/-- Both derived comparisons are uniquely determined by their displayed counit equations.
The coefficients have first been identified by adic_pullback_coefficient_presentations,
so the balanced-tensor comparison is the identity in these common coordinates.
Source: blueprint CBC argument, Step 3; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: use the universal left-derived lift with the first counit and the second
universal pair, and repeat in reverse. Uniqueness makes the two composites identities.
The same proof in the abelian strict-tower category gives the second assertion. -/
theorem adic_pullback_presentation_transport :
    (∃! e : L₁ ≅ L₂, Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε₂ = ε₁) ∧
    (∃! e : T₁ ≅ T₂, Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ τ₂ = τ₁) := by
  constructor
  · refine ⟨Functor.leftDerivedUnique L₂ L₁ ε₁ ε₂
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ)), ?_, ?_⟩
    · simp
    · intro e he
      apply Iso.ext
      apply Functor.leftDerived_ext L₂ ε₂
        (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
      simpa using he
  · refine ⟨Functor.leftDerivedUnique T₂ T₁ τ₁ τ₂
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ)), ?_, ?_⟩
    · simp
    · intro e he
      apply Iso.ext
      apply Functor.leftDerived_ext T₂ τ₂
        (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
      simpa using he

end Pairs

section CompletionTransport
/-- The strict reduction completion computed from a chosen tower presentation.
Source: blueprint CBC argument, Steps 6--8; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationCompletion
    (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)) :=
  (completedTowerRlim d X).obj
    (T.obj ((completedReductionTower Y d).obj K))

/-- The quotient augmentation unit for a chosen presentation and its constant-tower
comparison. The augmentation is the canonical strict reduction unit, so every quotient
transition is retained. Source: blueprint CBC argument, Steps 6 and 8; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationUnit
    (L : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
    (T : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (b : L ⋙ completedDerivedConstant d X ≅
      completedDerivedConstant d Y ⋙ T)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    L.obj K ⟶ adicPresentationCompletion d T K :=
  (completedConstantRlimUnit d X).app (L.obj K) ≫
    (completedTowerRlim d X).map
      (b.hom.app K ≫ T.map ((completedReductionTowerUnit d Y).app K))

/-- The natural comparison of the two completed strict presentations. It is obtained by
applying the functorial derived inverse limit to the strict-tower comparison. Source:
blueprint CBC argument, Steps 3 and 7; Stacks 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLimitComparison
    (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
      DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
    (e : T₁ ≅ T₂) (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d))) :
    adicPresentationCompletion d T₁ K ≅ adicPresentationCompletion d T₂ K :=
  (completedTowerRlim d X).mapIso
    ((Functor.isoWhiskerLeft (completedReductionTower Y d) e).app K)

end CompletionTransport

section TransportSquares
variable
  (L₁ L₂ : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcModules X (pbcAdicCompletion X d)))
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶
    (completedModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [L₁.IsLeftDerivedFunctor ε₁
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [L₂.IsLeftDerivedFunctor ε₂
    (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (T₁ T₂ : DerivedCategory (pbcTowers Y (pbcAdicCompletion Y d)) ⥤
    DerivedCategory (pbcTowers X (pbcAdicCompletion X d)))
  (τ₁ : DerivedCategory.Qh ⋙ T₁ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (τ₂ : DerivedCategory.Qh ⋙ T₂ ⟶
    (completedTowerModulePullback g d).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  [T₁.IsLeftDerivedFunctor τ₁
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  [T₂.IsLeftDerivedFunctor τ₂
    (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))]
  (e : L₁ ≅ L₂) (et : T₁ ≅ T₂)
  (hε : Functor.whiskerLeft DerivedCategory.Qh e.hom ≫ ε₂ = ε₁)
  (hτ : Functor.whiskerLeft DerivedCategory.Qh et.hom ≫ τ₂ = τ₁)

include hε hτ in
/-- The unique presentation comparisons respect both constant towers and evaluation.
These squares are conclusions of counit normalization. Source: CBC Step 4; Stacks 05S7
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: on objectwise K-flat resolutions insert the two displayed counit equations.
Both paths become the identical constant or evaluated tensor map. The normalization
of each comparison and uniqueness after localization give the two squares. -/
theorem adicPresentationComparison_squares :
    Functor.whiskerRight e.hom (completedDerivedConstant d X) ≫
        (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂).hom =
      (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁).hom ≫
        Functor.whiskerLeft (completedDerivedConstant d Y) et.hom ∧
    ∀ n : ℕ,
      Functor.whiskerRight et.hom (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≫
          (adicPresentationEvaluationIso g d L₂ ε₂ T₂ τ₂ n).hom =
        (adicPresentationEvaluationIso g d L₁ ε₁ T₁ τ₁ n).hom ≫
          Functor.whiskerLeft (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n) e.hom := by
  have hl : e.hom ≫ (adicPresentationOrdinaryIso g d L₂ ε₂).hom =
      (adicPresentationOrdinaryIso g d L₁ ε₁).hom := by
    apply Functor.leftDerived_ext (completedOrdinaryPullback g d)
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
    simpa [adicPresentationOrdinaryIso, Functor.whiskerLeft_comp,
      Category.assoc] using hε
  have ht : et.hom ≫ (adicPresentationTowerIso g d T₂ τ₂).hom =
      (adicPresentationTowerIso g d T₁ τ₁).hom := by
    apply Functor.leftDerived_ext (completedTowerPullback g d)
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
    simpa [adicPresentationTowerIso, Functor.whiskerLeft_comp,
      Category.assoc] using hτ
  have hi : (adicPresentationTowerIso g d T₁ τ₁).inv ≫ et.hom =
      (adicPresentationTowerIso g d T₂ τ₂).inv := by
    apply (cancel_mono (adicPresentationTowerIso g d T₂ τ₂).hom).1
    simp only [Category.assoc, ht, Iso.inv_hom_id]
  constructor
  · apply NatTrans.ext
    funext K
    simp only [adicPresentationConstantIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, hl]
    simpa only [Category.assoc, NatTrans.comp_app] using
      congrArg (fun f ↦
        (completedDerivedConstant d X).map
          (((adicPresentationOrdinaryIso g d L₁ ε₁).hom).app K) ≫
        (completedPullbackConstantIso g d).hom.app K ≫
        f.app ((completedDerivedConstant d Y).obj K)) hi.symm
  · intro n
    let v₁ := adicPresentationEvaluationIso g d L₁ ε₁ T₁ τ₁ n
    let v := Functor.isoWhiskerRight et.symm
        (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≪≫
      v₁ ≪≫ Functor.isoWhiskerLeft (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n) e
    have hv₁ : HasAdicPresentationEvaluationNormalization g d L₁ ε₁ T₁ τ₁ n v₁ :=
      (adicPresentationEvaluationIso_exists g d L₁ ε₁ T₁ τ₁ n).exists.choose_spec
    have hv : HasAdicPresentationEvaluationNormalization g d L₂ ε₂ T₂ τ₂ n v := by
      exact (normalizationTransportCounits (completedTowerModulePullback g d)
        (completedModulePullback g d)
        (pbcTowerEvaluation X (pbcAdicCompletion X d) n)
        (pbcTowerEvaluation Y (pbcAdicCompletion Y d) n)
        (((CategoryTheory.evaluation ℕᵒᵖ (pbcModules Y (pbcAdicCompletion Y d))).obj
          (op n)).mapHomologicalComplex (.up ℤ))
        T₁ T₂ L₁ L₂ τ₁ τ₂ ε₁ ε₂ et e hτ hε
        (fun P ↦ ∀ k : ℕ, CochainComplex.IsKFlatIndependentCoefficients
          (R := pbcAdicCompletion Y d) (P.asFunctor.obj (op k)))
        (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
          (pbcModules Y (pbcAdicCompletion Y d))).obj (op n)).mapDerivedCategoryFactors.hom.app P)
        (fun P ↦ ((CategoryTheory.evaluation ℕᵒᵖ
          (pbcModules X (pbcAdicCompletion X d))).obj (op n)).mapDerivedCategoryFactors.hom.app
            (((completedTowerModulePullback g d).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (eqToHom (adicPresentationEvaluationComplex_eq g d n P)))
        v₁).1 hv₁
    have heq : v = adicPresentationEvaluationIso g d L₂ ε₂ T₂ τ₂ n :=
      (adicPresentationEvaluationIso_exists g d L₂ ε₂ T₂ τ₂ n).unique hv
        (adicPresentationEvaluationIso_exists g d L₂ ε₂ T₂ τ₂ n).exists.choose_spec
    rw [← heq]
    ext K
    simp [v, v₁]

include hτ in
/-- Every finite reduction comparison is unchanged by the unique presentation transport.
Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: uniqueness of the universal tower comparison makes its composites to the
published pair equal. Whisker by strict reduction and exact evaluation, and compose
with the published generator-normalized finite comparison. -/
theorem adicPresentationFiniteIso_transport (n : ℕ) :
    Functor.whiskerRight
        (Functor.whiskerLeft (completedReductionTower Y d) et.hom)
        (pbcTowerEvaluation X (pbcAdicCompletion X d) n) ≫
      (adicPresentationFiniteIso g d T₂ τ₂ n).hom =
        (adicPresentationFiniteIso g d T₁ τ₁ n).hom := by
  have ht : et.hom ≫ (adicPresentationTowerIso g d T₂ τ₂).hom =
      (adicPresentationTowerIso g d T₁ τ₁).hom := by
    apply Functor.leftDerived_ext (completedTowerPullback g d)
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
    simpa [adicPresentationTowerIso, Functor.whiskerLeft_comp,
      Category.assoc] using hτ
  apply NatTrans.ext
  funext K
  simpa [adicPresentationFiniteIso, ← Category.assoc] using
    congrArg (fun f ↦ (pbcTowerEvaluation X (pbcAdicCompletion X d) n).map
      (f.app ((completedReductionTower Y d).obj K)) ≫
        (completedReductionFiniteEvaluation g d n).hom.app K) ht

/-- Finite comparisons retain every quotient arrow, including equal indices.
Source: CBC Step 5; Stacks 099L
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: on strict resolutions the ordinary finite comparison sends each pure tensor
to its quotient class. Quotienting either before or after the comparison gives the
same tensor. The normalized target transition is the descent of that very quotient
map. Naturality of the universal tower comparison transports this square to T₁.
The restriction-composition comparison is identity on underlying sections. -/
theorem adicPresentationFiniteIso_transition
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (a b : ℕ) (h : a ≤ b) :
    (adicPresentationFiniteIso g d T₁ τ₁ b).hom.app K ≫
        (pbcDerivedRestrict (completedReductionProjection X d b)).map
          ((completedReductionTargetTransition g d a b h).app K) ≫
        (pbcDerivedRestrictComp (completedReductionProjection X d b)
          (reductionCoefficientMap X d b a h) (completedReductionProjection X d a)
          (completedReductionProjection_comp X d b a h)).hom.app
            ((completedReductionFiniteTarget g d a).obj K) =
      (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app
          (T₁.obj ((completedReductionTower Y d).obj K)) ≫
        (adicPresentationFiniteIso g d T₁ τ₁ a).hom.app K := by
  let t := adicPresentationTowerIso g d T₁ τ₁
  let R := (completedReductionTower Y d).obj K
  have hn := (pbcTowerTransition X (pbcAdicCompletion X d) b a h).naturality
    (t.hom.app R)
  have hc := finite_quotient_transition_compatibility g d K a b h
  dsimp only [adicPresentationFiniteIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc] at hc ⊢
  rw [hc, ← Category.assoc, hn, Category.assoc]


include hε hτ in
/-- Completion units commute with the unique presentation comparisons, using the
counit-normalized constant comparisons; no compatibility square is assumed.
Source: CBC Steps 6--8; Stacks 05S7 and 08TC
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: the constant square follows from adicPresentationComparison_squares. Apply
naturality of et to the canonical strict reduction augmentation, then functorial
Rlim. Naturality of the constant/Rlim unit moves e through the limit, giving exactly
the displayed equality. Strict quotient transitions are retained before taking Rlim. -/
theorem adicPresentationCompletion_transport :
    ∀ K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)),
      adicPresentationUnit d L₁ T₁ (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁) K ≫
          (adicPresentationLimitComparison d T₁ T₂ et K).hom =
        e.hom.app K ≫
          adicPresentationUnit d L₂ T₂ (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂) K := by
  have hl : e.hom ≫ (adicPresentationOrdinaryIso g d L₂ ε₂).hom =
      (adicPresentationOrdinaryIso g d L₁ ε₁).hom := by
    apply Functor.leftDerived_ext (completedOrdinaryPullback g d)
      (completedOrdinaryPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcModules Y (pbcAdicCompletion Y d)) (.up ℤ))
    simpa [adicPresentationOrdinaryIso, Functor.whiskerLeft_comp,
      Category.assoc] using hε
  have ht : et.hom ≫ (adicPresentationTowerIso g d T₂ τ₂).hom =
      (adicPresentationTowerIso g d T₁ τ₁).hom := by
    apply Functor.leftDerived_ext (completedTowerPullback g d)
      (completedTowerPullbackCounit g d)
      (HomotopyCategory.quasiIso (pbcTowers Y (pbcAdicCompletion Y d)) (.up ℤ))
    simpa [adicPresentationTowerIso, Functor.whiskerLeft_comp,
      Category.assoc] using hτ
  have hi : (adicPresentationTowerIso g d T₁ τ₁).inv ≫ et.hom =
      (adicPresentationTowerIso g d T₂ τ₂).inv := by
    apply (cancel_mono (adicPresentationTowerIso g d T₂ τ₂).hom).1
    simp only [Category.assoc, ht, Iso.inv_hom_id]
  have hc : Functor.whiskerRight e.hom (completedDerivedConstant d X) ≫
        (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂).hom =
      (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁).hom ≫
        Functor.whiskerLeft (completedDerivedConstant d Y) et.hom := by
    apply NatTrans.ext
    funext K
    simp only [adicPresentationConstantIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← Category.assoc, ← Functor.map_comp, ← NatTrans.comp_app, hl]
    simpa only [Category.assoc, NatTrans.comp_app] using
      congrArg (fun f ↦
        (completedDerivedConstant d X).map
          (((adicPresentationOrdinaryIso g d L₁ ε₁).hom).app K) ≫
        (completedPullbackConstantIso g d).hom.app K ≫
        f.app ((completedDerivedConstant d Y).obj K)) hi.symm
  intro K
  have hstep :
      (adicPresentationConstantIso g d L₁ ε₁ T₁ τ₁).hom.app K ≫
          T₁.map ((completedReductionTowerUnit d Y).app K) ≫
          et.hom.app ((completedReductionTower Y d).obj K) =
        (completedDerivedConstant d X).map (e.hom.app K) ≫
          (adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂).hom.app K ≫
          T₂.map ((completedReductionTowerUnit d Y).app K) := by
    have hck := congr_app hc K
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hck
    rw [et.hom.naturality, ← Category.assoc, ← hck, Category.assoc]
  dsimp only [adicPresentationUnit, adicPresentationLimitComparison]
  change _ ≫ (completedTowerRlim d X).map (et.hom.app _) = _
  rw [Category.assoc, ← Functor.map_comp, Category.assoc, hstep,
    Functor.map_comp, Functor.map_comp]
  have hu := (completedConstantRlimUnit d X).naturality (e.hom.app K)
  simp only [Functor.id_map, Functor.comp_map] at hu
  simpa only [Category.assoc] using
    congrArg (fun f ↦ f ≫ (completedTowerRlim d X).map
      ((adicPresentationConstantIso g d L₂ ε₂ T₂ τ₂).hom.app K) ≫
        (completedTowerRlim d X).map (T₂.map ((completedReductionTowerUnit d Y).app K)))
      hu.symm
end TransportSquares

-- Restriction is inverse image along the corresponding site object.
private theorem restrictionIso_iff {X : Scheme.{u}} (U : X.ProEt)
    {M N : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}} (f : M ⟶ N) :
    IsIso (((ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).map f) ↔
      IsIso ((proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}).map f) := by
  apply Iff.trans ?_
    (NatIso.isIso_map_iff (restrictionComparison U AddCommGrpCat.{u + 1}).sheafIso f).symm
  let : (ProEt.sliceFrom X U).IsEquivalence :=
    inferInstanceAs (ProEt.sliceEquiv X U).inverse.IsEquivalence
  let W := (whiskeringLeft U.left.ProEtᵒᵖ (Over U)ᵒᵖ
    AddCommGrpCat.{u + 1}).obj (ProEt.sliceFrom X U).op
  let α := (sheafToPresheaf ((ProEt.topology X).over U)
    AddCommGrpCat.{u + 1}).map
      (((ProEt.topology X).overPullback AddCommGrpCat.{u + 1} U).map f)
  constructor
  · intro h
    have := h
    have : IsIso α :=
      (sheafToPresheaf ((ProEt.topology X).over U) AddCommGrpCat.{u + 1}).map_isIso _
    have : IsIso (W.map α) := W.map_isIso α
    rw [← isIso_iff_of_reflects_iso _
      (sheafToPresheaf (ProEt.topology U.left) AddCommGrpCat.{u + 1})]
    change IsIso (W.map α)
    infer_instance
  · intro h
    have := h
    have : IsIso (W.map α) :=
      (sheafToPresheaf (ProEt.topology U.left) AddCommGrpCat.{u + 1}).map_isIso
        ((AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
          U.hom U.prop).map f)
    have : IsIso α := isIso_of_reflects_iso _ W
    exact isIso_of_reflects_iso _
      (sheafToPresheaf ((ProEt.topology X).over U) AddCommGrpCat.{u + 1})

private theorem localInverseImageIso {X Y : Scheme.{u}} (g : X ⟶ Y) (U : Y.ProEt)
    {M N : Sheaf (ProEt.topology Y) AddCommGrpCat.{u + 1}} (f : M ⟶ N)
    (hf : IsIso (((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).map f)) :
    IsIso (((ProEt.topology X).overPullback AddCommGrpCat.{u + 1}
      ((proEtaleBaseChange g).obj U)).map
        ((proEtaleSheafInverseImage g AddCommGrpCat.{u + 1}).map f)) := by
  let V := (proEtaleBaseChange g).obj U
  let g' : V.left ⟶ U.left := pullback.fst U.hom g
  have hsq : V.hom ≫ g = g' ≫ U.hom := by
    exact pullback.condition.symm
  have hi : IsIso ((proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}).map f) :=
    (restrictionIso_iff U f).1 hf
  have := hi
  have hcomp : IsIso (((proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}) ⋙
      proEtaleSheafInverseImage g' AddCommGrpCat.{u + 1}).map f) := by
    change IsIso ((proEtaleSheafInverseImage g' AddCommGrpCat.{u + 1}).map
      ((proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1}).map f))
    infer_instance
  let e : proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} ⋙
      proEtaleSheafInverseImage V.hom AddCommGrpCat.{u + 1} ≅
      proEtaleSheafInverseImage U.hom AddCommGrpCat.{u + 1} ⋙
        proEtaleSheafInverseImage g' AddCommGrpCat.{u + 1} :=
    (AlgebraicGeometry.ProEtale.upperStarComp AddCommGrpCat.{u + 1} V.hom g).symm ≪≫
      eqToIso (congrArg (fun h ↦ proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}) hsq) ≪≫
        AlgebraicGeometry.ProEtale.upperStarComp AddCommGrpCat.{u + 1} g' U.hom
  apply (restrictionIso_iff V _).2
  exact (NatIso.isIso_map_iff e f).2 hcomp

@[irreducible] private noncomputable def finiteUnderlying {X Y : Scheme.{u}} (g : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R ≅ S) :
    proEtaleRingModulePullback g R S c ⋙ SheafOfModules.toSheaf _ ≅
      SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage g AddCommGrpCat.{u + 1} := by
  let hx := SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let theta := hx.choose
  have hn := hx.choose_spec.2.2
  let b : proEtaleRingModulePullback g R S c ⋙ SheafOfModules.toSheaf _ ≅
      proEtaleModuleInverseImage g R ⋙ SheafOfModules.toSheaf _ :=
    NatIso.ofComponents (fun M ↦
      (SheafOfModules.toSheaf _).mapIso (theta ((proEtaleModuleInverseImage g R).obj M)) ≪≫
        ObjectProperty.isoMk _ (Iso.refl _)) (by
          intro M N f
          have h := hn _ _ ((proEtaleModuleInverseImage g R).map f)
          have hleft : (proEtaleRingModulePullback g R S c).map f =
              SheafOfModules.changeOfRingsHomOfUniverses c.hom
                ((proEtaleModuleInverseImage g R).obj M)
                ((proEtaleModuleInverseImage g R).map f) := by rfl
          have hright : ((SheafOfModules.toSheaf _).map
              ((SheafOfModules.restrictScalars
                ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.inv)).map
                  ((proEtaleModuleInverseImage g R).map f))).hom =
              ((SheafOfModules.toSheaf _).map
                ((proEtaleModuleInverseImage g R).map f)).hom := by rfl
          apply ObjectProperty.hom_ext
          simpa only [Functor.comp_map, hleft, hright, Functor.map_comp,
            ObjectProperty.FullSubcategory.comp_hom,
            Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.isoMk_hom,
            ObjectProperty.homMk_hom, Iso.refl_hom, Category.comp_id,
            Category.id_comp] using
              congrArg (fun f ↦ f.hom) (congrArg (SheafOfModules.toSheaf _).map h))
  exact b ≪≫ (proEtale_moduleInverseImage_comparison g R).1.some

section OpenMateTransport
variable (U : Y.ProEt) [hU : IsOpenImmersion U.hom] (n : ℕ)

/-- Finite pullback on the cartesian open square in slice-site coordinates: extend
from U, apply the finite tensor pullback, and restrict to g⁻¹U. This is the canonical
local inverse image; the localized comparison below retains its open counit.
Source: CBC Step 9; Stacks 04J0, 03DI, 09AE
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLocalizedFinitePull :=
  SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U ⋙
    completedReductionFiniteModules g d n ⋙
      SheafOfModules.localizedModuleRestriction (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)

/-- The actual restriction/pullback comparison on the cartesian open square. Its
components are finite pullback of the sheafified open counit, followed by restriction.
Source: CBC Step 9; Stacks 04J0 and 03DI
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationLocalizedComparison :
    SheafOfModules.localizedModuleRestriction (reductionCoefficient Y d n) U ⋙
        adicPresentationLocalizedFinitePull g d U n ⟶
      completedReductionFiniteModules g d n ⋙
        SheafOfModules.localizedModuleRestriction (reductionCoefficient X d n)
          ((proEtaleBaseChange g).obj U) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (SheafOfModules.localizedModuleAdjunctionIndependent
        (reductionCoefficient Y d n) U).counit _ ≫
    (Functor.leftUnitor _).hom

include hU in
/-- The finite localized comparison is invertible, including the empty open.
Source: CBC Step 9; Stacks 04J0 and 09AE
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: identify the open pro-etale site with its slice by weaklyEtale_localization.
An inverse-image test object over g⁻¹U has only the summands factoring through U.
The sheafified open counit is identity on those summands; its finite tensor pullback
and restriction therefore give inverse identity-on-generator maps. This is precisely
the restricted coefficient map and localized tensor comparison of 04J0. -/
theorem adicPresentationLocalizedComparison_isIso :
    IsIso (adicPresentationLocalizedComparison g d U n) := by
  let R := reductionCoefficient Y d n
  let S := reductionCoefficient X d n
  let V := (proEtaleBaseChange g).obj U
  let F := completedReductionFiniteModules g d n
  let RY := SheafOfModules.localizedModuleRestriction R U
  let RX := SheafOfModules.localizedModuleRestriction S V
  let a := SheafOfModules.localizedModuleAdjunctionIndependent R U
  let PY := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let PX := SheafOfModules.toSheaf
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  have : IsIso a.unit := SheafOfModules.localizedUnit_isIso U.hom R
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  change IsIso (RX.map (F.map (a.counit.app M)))
  have hr : IsIso (RY.map (a.counit.app M)) := by
    rw [← isIso_comp_left_iff (a.unit.app (RY.obj M)), a.right_triangle_components]
    infer_instance
  have hs : IsIso (((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).map
      (PY.map (a.counit.app M))) := by
    change IsIso ((SheafOfModules.toSheaf _).map (RY.map (a.counit.app M)))
    infer_instance
  have ht := localInverseImageIso g U (PY.map (a.counit.app M)) hs
  let e := finiteUnderlying g R S (asIso (completedFiniteCoefficientMap g d n))
  have hb : IsIso (((ProEt.topology X).overPullback AddCommGrpCat.{u + 1} V).map
      (PX.map (F.map (a.counit.app M)))) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight e
        ((ProEt.topology X).overPullback AddCommGrpCat.{u + 1} V))
      (a.counit.app M)).2 ht
  have : IsIso ((SheafOfModules.toSheaf _).map (RX.map (F.map (a.counit.app M)))) := hb
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- The inverse open mate uses the actual sheafified presheaf extension and its
uniquely generator-normalized adjunctions, with the canonical finite localized map.
Source: CBC Steps 9--10; Stacks 03DI and 04J0
(blueprint: lem-cbc-adic-pullback-presentation-transport). -/
def adicPresentationInverseMate :=
  (mateEquiv
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
      ((proEtaleBaseChange g).obj U))).symm
    (TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n))

/-- The specified inverse mate is the finite pullback followed by the target open
counit, since the localized pullback was constructed by extension and restriction.
Source: CBC Step 10; Stacks 03DI
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: expand the inverse-mate formula. Naturality moves the source unit across
finite pullback, and the source triangle identity cancels it against the localized
comparison's source counit. The remaining factor is the displayed target counit. -/
theorem adicPresentationInverseMate_counit :
    (adicPresentationInverseMate g d U n).natTrans =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U ⋙
            completedReductionFiniteModules g d n)
          (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
            ((proEtaleBaseChange g).obj U)).counit ≫
        (Functor.rightUnitor _).hom := by
  have _ := hU
  exact inverseMate_counit_formula
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
    (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
      ((proEtaleBaseChange g).obj U)) (completedReductionFiniteModules g d n)

include hU in
/-- Both finite open mates are determined by the same localized comparison, with
j_! definitionally the sheafified extensionByZeroPresheaf on each slice. The square
is the pullback of U.hom along g, and the finite functor is the published tensor pullback.
Source: CBC Steps 9--10; Stacks 03DI, 03DJ and 04J0
(blueprint: lem-cbc-adic-pullback-presentation-transport).
Proof: Step 1 fixes the completed ring map and all finite maps. Step 5 retains their
quotient comparisons. The localized finite map is therefore the same specified
adicPresentationLocalizedComparison. The normalized open units insert summand
generators and the counits evaluate them. Substitute these identical three factors
into the inverse-mate formula to obtain equality with the stated canonical mate. -/
theorem adicPresentationInverseMate_eq
    (m₁ m₂ : TwoSquare (adicPresentationLocalizedFinitePull g d U n)
      (SheafOfModules.localizedModuleExtension (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleExtension (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) (completedReductionFiniteModules g d n))
    (h₁ : mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) m₁ =
          TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n))
    (h₂ : mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U)) m₂ =
          TwoSquare.mk _ _ _ _ (adicPresentationLocalizedComparison g d U n)) :
    m₁ = adicPresentationInverseMate g d U n ∧
      m₂ = adicPresentationInverseMate g d U n := by
  have _ := hU
  constructor
  · exact (mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U))).injective (h₁.trans (Equiv.apply_symm_apply _ _).symm)
  · exact (mateEquiv
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient Y d n) U)
      (SheafOfModules.localizedModuleAdjunctionIndependent (reductionCoefficient X d n)
        ((proEtaleBaseChange g).obj U))).injective (h₂.trans (Equiv.apply_symm_apply _ _).symm)
end OpenMateTransport

end AlgebraicGeometry.Scheme
