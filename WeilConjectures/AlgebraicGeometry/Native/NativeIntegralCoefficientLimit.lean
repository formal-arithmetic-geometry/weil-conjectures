/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
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
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact

/-! # The native uniformizer coefficient cone
Source: integral coefficient comparison (blueprint: lem-twist-native-coefficient-limit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The actual positive uniformizer quotient as an integral module. -/
def nativeCoefficientLevel (n : ℕ) :=
  (Mod.comap (coefficientMap (twistReduction l E n) X)).obj
    (Mod.regular (condensedRingObj (twistFiniteRing l E n) X))

/-- Linear quotient transition, with the specified reduction as its underlying map. -/
def nativeCoefficientTransition (n : ℕ) :
    nativeCoefficientLevel l E X (n + 1) ⟶ nativeCoefficientLevel l E X n :=
  Mod.homMk (coefficientMap (twistFiniteReduction l E n) X) (by
    change (_ ▷ _) ≫ μ[_] ≫ coefficientMap (twistFiniteReduction l E n) X =
      _ ◁ coefficientMap (twistFiniteReduction l E n) X ≫ (_ ▷ _) ≫ μ[_]
    rw [IsMonHom.mul_hom]
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.comp_id, Category.id_comp, twistReduction_comp])

/-- The actual positive uniformizer quotient diagram. -/
def nativeCoefficientSystem := Functor.ofOpSequence (nativeCoefficientTransition l E X)

/-- The actual coefficient reduction, as a morphism from the regular module. -/
def nativeCoefficientProjection (n : ℕ) :
    Mod.regular (condensedRingObj (twistIntegralRing l E) X) ⟶
      nativeCoefficientLevel l E X n :=
  Mod.homMk (coefficientMap (twistReduction l E n) X) (by
    change μ[_] ≫ coefficientMap (twistReduction l E n) X =
      _ ◁ coefficientMap (twistReduction l E n) X ≫ (_ ▷ _) ≫ μ[_]
    rw [IsMonHom.mul_hom, tensorHom_def', Category.assoc])

/-- The coefficient cone with its prescribed quotient projections. -/
def nativeCoefficientCone : Cone (nativeCoefficientSystem l E X) :=
  ⟨Mod.regular _, NatTrans.ofOpSequence (nativeCoefficientProjection l E X) (by
    intro n
    simp only [Functor.const_obj_map, nativeCoefficientSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
    apply Mod.hom_ext
    exact (twistReduction_comp l E X n).symm)⟩

private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousCoefficientRingSheaf X A)

private def continuousMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : continuousAb X A ⟶ continuousAb X B :=
  ⟨{ app := fun _ ↦ AddCommGrpCat.ofHom
      (ULift.ringEquiv.symm.toAddEquiv.toAddMonoidHom.comp
        ((f.compLeftContinuous _ hf).toAddMonoidHom.comp
          ULift.ringEquiv.toAddEquiv.toAddMonoidHom))
     naturality := fun _ _ _ ↦ rfl }⟩

private theorem realization_natural {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    (upperStarFromPoint X).map (twistContinuousMap f hf) ≫
        ContinuousRingUniverse.comparison X B =
      ContinuousRingUniverse.comparison X A ≫ continuousMap X f hf := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison]
  change _ ≫ adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) =
    adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext S x
  rfl

private abbrev continuousFinite (n : ℕ) :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousAb X (Padic.coefficientExtensionRing l E (n + 1))

private def continuousTransition (n : ℕ) :
    continuousFinite l E X (n + 1) ⟶ continuousFinite l E X n :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 2)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 2)) := ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousMap X (Padic.coefficientExtensionTransition l E (n + 1))
    continuous_of_discreteTopology

private def continuousSequence := Functor.ofOpSequence (continuousTransition l E X)

private def continuousProjection (n : ℕ) :
    letI := spectralNorm.normedField ℚ_[l] E
    continuousAb X (Padic.coefficientExtensionIntegers l E) ⟶ continuousFinite l E X n :=
  letI := spectralNorm.normedField ℚ_[l] E
  letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  continuousMap X (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
    (twistReduction_continuous l E n)

private def continuousCone : Cone (continuousSequence l E X) := by
  let := spectralNorm.normedField ℚ_[l] E
  refine ⟨continuousAb X (Padic.coefficientExtensionIntegers l E),
    NatTrans.ofOpSequence (continuousProjection l E X) ?_⟩
  intro n
  dsimp only [continuousSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  ext U f
  rfl

private theorem continuousCone_isLimit : Nonempty (IsLimit (continuousCone l E X)) := by
  let := spectralNorm.normedField ℚ_[l] E
  let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) :=
    Padic.coefficientExtensionPositiveLimitTopology l E
  obtain ⟨⟨e, he, htop⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  have heci : Continuous e.symm :=
    (e.toEquiv.toHomeomorphOfContinuousOpen htop.continuous htop.isOpenMap).symm.continuous
  refine ⟨?_⟩
  apply isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget Ab.{u + 1})
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply e.injective
    apply Subtype.ext
    funext n
    rw [he, he]
    exact congrArg (fun s ↦ (s.val (op n)).down x) hfg
  · intro s
    let t (n : ℕ) : @ContinuousMap U.unop.left
        (Padic.coefficientExtensionRing l E (n + 1)) _ ⊥ := (s.val (op n)).down
    let b (x : U.unop.left) : Padic.coefficientExtensionPositiveLimit l E :=
      ⟨fun n ↦ t n x, by
        apply Subring.mem_iInf.mpr
        intro n
        have hn := s.property (homOfLE n.le_succ).op
        simp only [Functor.comp_map, continuousSequence,
          Functor.ofOpSequence_map_homOfLE_succ] at hn
        exact congrArg (fun f ↦ f.down x) hn⟩
    have hb : Continuous b := by
      apply (continuous_induced_rng
        (f := fun x : Padic.coefficientExtensionPositiveLimit l E ↦ x.val)
        (g := b) (t₂ := @Pi.topologicalSpace ℕ
          (fun n ↦ Padic.coefficientExtensionRing l E (n + 1)) (fun _ ↦ ⊥))).mpr
      apply (continuous_pi (T := fun _ ↦ ⊥))
      intro n
      exact @ContinuousMap.continuous _ _ _ ⊥ (t n)
    refine ⟨ULift.up (⟨fun x ↦ e.symm (b x), heci.comp hb⟩ :
      C(U.unop.left, Padic.coefficientExtensionIntegers l E)), ?_⟩
    apply Subtype.ext
    funext n
    let : TopologicalSpace (Padic.coefficientExtensionRing l E (n.unop + 1)) := ⊥
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1))
      (e.symm (b x)) = _
    rw [← he]
    exact congrArg (fun t : Padic.coefficientExtensionPositiveLimit l E ↦ t.val n.unop)
      (e.apply_symm_apply (b x))

private def realizationTower : nativeCoefficientSystem l E X ⋙
    Mod.forget (condensedRingObj (twistIntegralRing l E) X) ≅ continuousSequence l E X := by
  let e (n : ℕ) :=
    letI : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
    letI : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
    ContinuousRingUniverse.comparison X (Padic.coefficientExtensionRing l E (n + 1))
  have he (n : ℕ) : IsIso (e n) := by
    let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
    let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
    exact ContinuousRingUniverse.comparison_isIso X _
  let t : nativeCoefficientSystem l E X ⋙ Mod.forget _ ⟶ continuousSequence l E X :=
    NatTrans.ofOpSequence e (by
      intro n
      simp only [nativeCoefficientSystem, continuousSequence, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ]
      let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 2)) := ⊥
      let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 2)) := ⟨rfl⟩
      let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
      let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
      exact realization_natural X (Padic.coefficientExtensionTransition l E (n + 1))
        continuous_of_discreteTopology)
  have (n : ℕᵒᵖ) : IsIso (t.app n) := he n.unop
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

/-- The actual native coefficient cone is a limit in integral modules.
Source: integral coefficient comparison (blueprint: lem-twist-native-coefficient-limit).
Proof: compatible continuous quotient functions give a continuous map into their
product subspace. The profinite coefficient tower homeomorphism reconstructs the
unique integral-valued continuous function. Evaluation and the sheaf forgetful
functors reflect the resulting limit. The canonical point-pullback realization
comparisons commute with the quotient maps by adjunction naturality and are
isomorphisms for the totally disconnected integer and finite coefficient rings.
Transport the continuous limit through these comparisons and reflect through the
module forgetful functor. The projections remain the specified reductions. -/
theorem nativeCoefficientCone_isLimit : Nonempty (IsLimit (nativeCoefficientCone l E X)) := by
  refine ⟨?_⟩
  let := spectralNorm.normedField ℚ_[l] E
  have : TotallyDisconnectedSpace (Padic.coefficientExtensionIntegers l E) :=
    (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
  have : IsIso (ContinuousRingUniverse.comparison X
      (Padic.coefficientExtensionIntegers l E)) :=
    ContinuousRingUniverse.comparison_isIso X _
  let e := asIso (ContinuousRingUniverse.comparison X
    (Padic.coefficientExtensionIntegers l E))
  let c := (Mod.forget (condensedRingObj (twistIntegralRing l E) X)).mapCone
    (nativeCoefficientCone l E X)
  have hc : IsLimit ((Cone.postcompose (realizationTower l E X).hom).obj c) := by
    apply IsLimit.ofIsoLimit (continuousCone_isLimit l E X).some
    refine Cone.ext e.symm ?_
    intro n
    change (continuousCone l E X).π.app n = e.inv ≫
      ((Mod.forget _).map ((nativeCoefficientCone l E X).π.app n) ≫
        (realizationTower l E X).hom.app n)
    apply (cancel_epi e.hom).mp
    simp only [Iso.hom_inv_id_assoc]
    let : TopologicalSpace (Padic.coefficientExtensionRing l E (n.unop + 1)) := ⊥
    let : DiscreteTopology (Padic.coefficientExtensionRing l E (n.unop + 1)) := ⟨rfl⟩
    exact (realization_natural X
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n.unop + 1)))
      (twistReduction_continuous l E n.unop)).symm
  exact isLimitOfReflects (Mod.forget _)
    ((IsLimit.postcomposeHomEquiv (realizationTower l E X) c) hc)

end AlgebraicGeometry.ProEtale
