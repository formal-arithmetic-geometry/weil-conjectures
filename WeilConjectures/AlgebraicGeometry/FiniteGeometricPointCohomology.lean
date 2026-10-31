/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomMixedUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.AlgebraicGeometry.CondensedOrdinaryCompactSections
public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
public import Mathlib.Topology.Bases
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
public import WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
public import Mathlib.Topology.Algebra.Order.Field
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.PoincareDuality.Abstract
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.ModuleCat.AB

import WeilConjectures.AlgebraicGeometry.FinitePointCoefficientAdmissibility
import WeilConjectures.AlgebraicGeometry.FinitePointScalarRealization
import WeilConjectures.AlgebraicGeometry.FinitePointScalarRings
import WeilConjectures.AlgebraicGeometry.FinitePointCohomologicalRange
import WeilConjectures.CategoryTheory.BoundedHeartAmplitude
import WeilConjectures.Algebra.Homology.PerfectScalarExtensionWindow
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.AdmissibleDirectImage
import WeilConjectures.AlgebraicGeometry.OpenImmersionLocalizing
import WeilConjectures.AlgebraicGeometry.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.AlgebraicGeometry.FinitePointSectionsExact
import WeilConjectures.AlgebraicGeometry.FinitePointFiniteOrdinaryBound

/-! # Perfect cohomology over the geometric point

Source: latest blueprint, sec-six-functors/sk-lem-finite/_section.md and
sk-lem-finite.proof.md, including the Complement (blueprint: sk-lem-finite).

The predicates below package the clauses of this statement using the existing
ordinary condensed-module operations, scalar sections, derived Hom and scalar extension.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

-- Prefer the canonical small localization over imported larger standard localizations.
attribute [instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Perfectness of a scalar complex and its derived dual, and invertibility of the
canonical signed evaluation into its bidual. The arrow is the existing transpose of
evaluation after the derived Koszul braiding, with coefficient object R in degree zero.
Source: sk-lem-finite, second paragraph (blueprint: sk-lem-finite). -/
def FinitePointScalarDuality (R : Type (u + 1)) [CommRing R]
    (P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R)) : Prop :=
  DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1} P ∧
    DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
      ((ordinaryModuleDerivedInternalHom R).obj
        (op P, (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R))) ∧
    IsIso (@Verdier.bidualityMap
      (DerivedCategory.{u + 1} (ModuleCat.{u + 1} R)) _ _ _
      (DerivedCategory.braidedCategory' _)
      ((DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R)) P)

private theorem scalar_duality_of_perfect (R : Type (u + 1)) [CommRing R]
    (P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R))
    (hP : DerivedCategory.IsPerfectRingComplex P) : FinitePointScalarDuality R P := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} R)
  have h : DerivedCategory.IsPerfect P := hP
  let e := DerivedCategory.singleFunctorObjUnitIso (ModuleCat.{u + 1} R)
  refine ⟨hP, ?_, ?_⟩
  · exact h.ihom_unit.of_iso ((ihom P).mapIso e.symm)
  · exact Verdier.isIso_bidualityMap_of_isDualizable e.symm
      isInvertible_unit h.isDualizable

private theorem scalar_finite_cohomology_of_perfect
    (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    (P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R))
    (hP : DerivedCategory.IsPerfectRingComplex P) :
    DerivedCategory.TStructure.t.bounded P ∧
      ∀ i : ℤ, Module.Finite R
        ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj P) := by
  have h : DerivedCategory.IsPerfect P := hP
  exact ⟨h.bounded, h.finite_homology⟩

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k]

set_option maxHeartbeats 800000 in
-- Several ordinary module-derived functors are elaborated in the same clause.
/-- The common clauses: actual terminal sections identify the point's finite-Tor
constructible subcategory with perfect scalar complexes. Both direct images are in
that subcategory, both scalar complexes and their duals are perfect with signed biduality,
and input cohomology in [a,b] gives scalar cohomology in [a,b+2 dim X]. The empty scheme
has zero direct images, zero scalar complexes and zero scalar duals in every degree.
Source: sk-lem-finite, all coefficient cases and Complement (blueprint: sk-lem-finite). -/
def FinitePointCohomology (X : Over (Spec (.of k))) : Prop :=
  (∃ h : ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj),
    (ObjectProperty.lift
      (DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1} (R := MonObj.Γ Λ) :
        ObjectProperty (DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ))))
      ((constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
          DerivedCategory.finiteTorAmplitude _).ι ⋙
        (condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor) h
      ).IsEquivalence) ∧
  ∀ (c : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ X.left),
    (∀ Q ∈ [(rightDerivedLowerShriekOfCompactification Λ c).obj K.obj,
        (lowerStar Λ X.hom).rightDerivedFunctor.obj K.obj],
      (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
        DerivedCategory.finiteTorAmplitude _) Q ∧ (IsEmpty X.left → IsZero Q)) ∧
    ∀ P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ)),
      P ∈ [(condensedRingCompactCoefficientComplex Λ c).obj K.obj,
        (condensedRingOrdinaryCoefficientComplex Λ X.hom).obj K.obj] →
      FinitePointScalarDuality (MonObj.Γ Λ) P ∧
      (∀ (a b : ℤ), DerivedCategory.homologyConcentratedIn a b K.obj →
        ∀ d : ℕ, topologicalKrullDim X.left = (d : WithBot ℕ∞) →
          DerivedCategory.homologyConcentratedIn a (b + 2 * (d : ℤ)) P) ∧
      (IsEmpty X.left → IsZero P ∧
        IsZero ((ordinaryModuleDerivedInternalHom (MonObj.Γ Λ)).obj
          (op P, (DerivedCategory.singleFunctor _ 0).obj
            (ModuleCat.of (MonObj.Γ Λ) (MonObj.Γ Λ)))))

set_option maxHeartbeats 800000 in
-- Several ordinary module-derived functors are elaborated in the same clause.
/-- Bounded finitely generated scalar cohomology, for both supports. Over the two field
coefficients this says bounded finite-dimensional cohomology; over the integral coefficient
it is membership in D^b_fg. No finite-dimensionality condition on K is assumed.
Source: sk-lem-finite, coefficient-specific Complement (blueprint: sk-lem-finite). -/
def FinitePointFiniteCohomology (X : Over (Spec (.of k))) : Prop :=
  ∀ (c : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ X.left),
    ∀ P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ)),
      P ∈ [(condensedRingCompactCoefficientComplex Λ c).obj K.obj,
        (condensedRingOrdinaryCoefficientComplex Λ X.hom).obj K.obj] →
      DerivedCategory.TStructure.t.bounded P ∧
        ∀ i : ℤ, Module.Finite (MonObj.Γ Λ)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (MonObj.Γ Λ)) i).obj P)

set_option maxHeartbeats 800000 in
-- Several ordinary module-derived functors are elaborated in the same clause.
/-- Both integral scalar complexes have perfect derived reductions modulo every positive
uniformizer power, with one Tor interval chosen before the level and before the support.
The map is the actual quotient homomorphism on condensed coefficients followed by Γ.
Source: sk-lem-finite, integral Complement (blueprint: sk-lem-finite). -/
def FinitePointUniformReductions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Over (Spec (.of k))) : Prop :=
  ∀ (c : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor (DerivedNakayama.integerRing ℓ E) X.left),
    ∃ a b : ℤ, a ≤ b ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ P ∈ [(condensedRingCompactCoefficientComplex
            (DerivedNakayama.integerRing ℓ E) c).obj K.obj,
          (condensedRingOrdinaryCoefficientComplex
            (DerivedNakayama.integerRing ℓ E) X.hom).obj K.obj],
        DerivedCategory.IsPerfectRingComplex.{u + 1, u + 1}
          ((ModuleCat.ordinaryDerivedExtendScalars
            (MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E n))).obj P) ∧
        DerivedCategory.torAmplitudeIn _ a b
          ((ModuleCat.ordinaryDerivedExtendScalars
            (MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E n))).obj P)

private instance ordinaryComplex_commShift {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (condensedRingOrdinaryCoefficientComplex Λ a).CommShift ℤ := by
  dsimp [condensedRingOrdinaryCoefficientComplex]
  infer_instance

private instance compactComplex_commShift {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) :
    (condensedRingCompactCoefficientComplex Λ c).CommShift ℤ := by
  dsimp [condensedRingCompactCoefficientComplex]
  infer_instance

private instance ordinaryComplex_isTriangulated {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (condensedRingOrdinaryCoefficientComplex Λ a).IsTriangulated := by
  dsimp [condensedRingOrdinaryCoefficientComplex]
  infer_instance

private instance compactComplex_isTriangulated {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) :
    (condensedRingCompactCoefficientComplex Λ c).IsTriangulated := by
  dsimp [condensedRingCompactCoefficientComplex]
  infer_instance

private instance ordinaryComplex_additive {X Y : Scheme.{u}} (a : X ⟶ Y) :
    (condensedRingOrdinaryCoefficientComplex Λ a).Additive := by
  dsimp [condensedRingOrdinaryCoefficientComplex]
  infer_instance

private instance compactComplex_additive {X Y : Scheme.{u}} {a : X ⟶ Y}
    (c : Compactification a) :
    (condensedRingCompactCoefficientComplex Λ c).Additive := by
  dsimp [condensedRingCompactCoefficientComplex]
  infer_instance

private theorem direct_images_ctf (ℓ : ℕ) [Fact ℓ.Prime]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    ∀ Q ∈ [(rightDerivedLowerShriekOfCompactification Λ c).obj K.obj,
      (lowerStar Λ X.hom).rightDerivedFunctor.obj K.obj],
      (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
        DerivedCategory.finiteTorAmplitude _) Q := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : (Spec (.of k)).Over (Spec (.of k)) := ⟨𝟙 _⟩
  let : X.hom.IsOver (Spec (.of k)) := ⟨by
    change X.hom ≫ 𝟙 _ = X.hom
    exact Category.comp_id _⟩
  have : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := by
    change LocallyOfFiniteType X.hom
    infer_instance
  have : QuasiCompact (X.left ↘ Spec (.of k)) := by
    change QuasiCompact X.hom
    infer_instance
  have : IsSeparated (X.left ↘ Spec (.of k)) := by
    change IsSeparated X.hom
    infer_instance
  have : LocallyOfFiniteType ((Spec (.of k)) ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (𝟙 (Spec (.of k)))
    infer_instance
  have : QuasiCompact ((Spec (.of k)) ↘ Spec (.of k)) := by
    change QuasiCompact (𝟙 (Spec (.of k)))
    infer_instance
  have : IsSeparated ((Spec (.of k)) ↘ Spec (.of k)) := by
    change IsSeparated (𝟙 (Spec (.of k)))
    infer_instance
  have ho := (openImmersionLowerShriek_localizing ℓ k (ringChar k)
    (Fact.out : (ringChar k).Prime).pos Fact.out Λ hΛ c.i).1 K
  have hc := (properLocalizingHypotheses_admissible ℓ Λ hΛ k c.g).1 ⟨_, ho⟩
  have hn := constructibleFiniteTor_rightDerivedLowerStar_of_admissible ℓ k Λ hΛ
    X.hom K.obj K.property
  intro Q hQ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl
  · exact hc
  · exact hn

private theorem scalar_zero_dual (R : Type (u + 1)) [CommRing R]
    (P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} R)) (hP : IsZero P) :
    IsZero ((ordinaryModuleDerivedInternalHom R).obj
      (op P, (DerivedCategory.singleFunctor _ 0).obj (ModuleCat.of R R))) := by
  let := DerivedCategory.braidedCategory' (ModuleCat.{u + 1} R)
  exact isZero_ihom_obj_of_isZero hP _

private theorem direct_images_zero_of_empty
    (X : Over (Spec (.of k))) (c : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ X.left) (hX : IsEmpty X.left) :
    (∀ Q ∈ [(rightDerivedLowerShriekOfCompactification Λ c).obj K.obj,
      (lowerStar Λ X.hom).rightDerivedFunctor.obj K.obj], IsZero Q) ∧
    (∀ P ∈ [(condensedRingCompactCoefficientComplex Λ c).obj K.obj,
      (condensedRingOrdinaryCoefficientComplex Λ X.hom).obj K.obj], IsZero P) := by
  let := hX
  have hz : IsZero K.obj := isZero_derivedCategory_of_isEmpty' Λ K.obj
  constructor
  · intro Q hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl
    · exact (rightDerivedLowerShriekOfCompactification Λ c).map_isZero hz
    · exact (lowerStar Λ X.hom).rightDerivedFunctor.map_isZero hz
  · intro P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact (condensedRingCompactCoefficientComplex Λ c).map_isZero hz
    · exact (condensedRingOrdinaryCoefficientComplex Λ X.hom).map_isZero hz

private theorem ordinary_complex_isGE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (a : ℤ) [K.IsGE a] :
    ((condensedRingOrdinaryCoefficientComplex Λ f).obj K).IsGE a := by
  have := (lowerStar Λ f).isGE_rightDerivedFunctor_obj K a
  exact (condensedRingCoefficientSections Λ Y).isGE_rightDerivedFunctor_obj _ a

private theorem compact_complex_isGE {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) (a : ℤ) [K.IsGE a] :
    ((condensedRingCompactCoefficientComplex Λ c).obj K).IsGE a := by
  have := (openImmersionLowerShriek Λ c.i).isGE_mapDerivedCategory_obj K a
  have : ((rightDerivedLowerShriekOfCompactification Λ c).obj K).IsGE a := by
    change ((lowerStar Λ c.g).rightDerivedFunctor.obj
      ((openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K)).IsGE a
    exact (lowerStar Λ c.g).isGE_rightDerivedFunctor_obj _ a
  exact (condensedRingCoefficientSections Λ Y).isGE_rightDerivedFunctor_obj _ a

private theorem cohomological_range_of_heart [IsSepClosed k]
    (hr : FinitePointCohomologicalHeartUpperBound Λ k)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) (K : ConstantModelConstructibleFiniteTor Λ X.left)
    (P : DerivedCategory.{u + 1} (ModuleCat.{u + 1} (MonObj.Γ Λ)))
    (hP : P ∈ [(condensedRingCompactCoefficientComplex Λ c).obj K.obj,
      (condensedRingOrdinaryCoefficientComplex Λ X.hom).obj K.obj])
    (a b : ℤ) (hK : DerivedCategory.homologyConcentratedIn a b K.obj)
    (d : ℕ) (hd : topologicalKrullDim X.left = (d : WithBot ℕ∞)) :
    DerivedCategory.homologyConcentratedIn a (b + 2 * (d : ℤ)) P := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)
  let B := ModuleCat.{u + 1} (MonObj.Γ Λ)
  have reduce (T : DerivedCategory A ⥤ DerivedCategory B)
      [T.CommShift ℤ] [T.IsTriangulated]
      (hT : ∀ (M : A), IsConstantModelConstructible Λ X.left M →
        DerivedCategory.homologyConcentratedIn 0 (2 * (d : ℤ))
          (T.obj ((DerivedCategory.singleFunctor A 0).obj M))) :
      DerivedCategory.homologyConcentratedIn a (b + 2 * (d : ℤ)) (T.obj K.obj) := by
    have := hK.1
    have := hK.2
    by_cases hab : a ≤ b
    · let S : A → Prop := fun M ↦ IsZero M ∨ ∃ q : ℤ,
        Nonempty (M ≅ (DerivedCategory.homologyFunctor A q).obj K.obj)
      have hSiso (M N : A) (e : M ≅ N) (hM : S M) : S N := by
        rcases hM with hM | ⟨q, ⟨eM⟩⟩
        · exact Or.inl (hM.of_iso e.symm)
        · exact Or.inr ⟨q, ⟨e.symm ≪≫ eM⟩⟩
      have hheart (M : A) (hM : S M) (i : ℤ) (hi : i < 0 ∨ 2 * (d : ℤ) < i) :
          IsZero ((DerivedCategory.homologyFunctor B i).obj
            (T.obj ((DerivedCategory.singleFunctor A 0).obj M))) := by
        rcases hM with hM | ⟨q, ⟨e⟩⟩
        · exact (DerivedCategory.homologyFunctor B i).map_isZero
            (T.map_isZero ((DerivedCategory.singleFunctor A 0).map_isZero hM))
        · have ht := hT _ (K.property.1.2 q)
          have hz : IsZero ((DerivedCategory.homologyFunctor B i).obj
              (T.obj ((DerivedCategory.singleFunctor A 0).obj
                ((DerivedCategory.homologyFunctor A q).obj K.obj)))) := by
            rcases hi with hi | hi
            · have := ht.1
              exact DerivedCategory.isZero_of_isGE _ 0 i hi
            · have := ht.2
              exact DerivedCategory.isZero_of_isLE _ _ i hi
          exact hz.of_iso ((DerivedCategory.homologyFunctor B i).mapIso
            (T.mapIso ((DerivedCategory.singleFunctor A 0).mapIso e)))
      have hv := DerivedCategory.bounded_heart_amplitude A B T S hSiso
        (Or.inl (isZero_zero A)) 0 (2 * (d : ℤ)) (by omega) hheart a b hab K.obj
        (fun i hi ↦ by
          rcases hi with hi | hi
          · exact DerivedCategory.isZero_of_isGE K.obj a i hi
          · exact DerivedCategory.isZero_of_isLE K.obj b i hi)
        (fun q ↦ Or.inr ⟨q, ⟨Iso.refl _⟩⟩)
      constructor
      · exact (DerivedCategory.isGE_iff _ a).2 fun i hi ↦ hv i (Or.inl (by omega))
      · exact (DerivedCategory.isLE_iff _ _).2 fun i hi ↦ hv i (Or.inr hi)
    · have hz := T.map_isZero
        (DerivedCategory.TStructure.t.isZero K.obj b a (by omega))
      exact ⟨DerivedCategory.TStructure.t.isGE_of_isZero hz a,
        DerivedCategory.TStructure.t.isLE_of_isZero hz (b + 2 * (d : ℤ))⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · apply reduce (condensedRingCompactCoefficientComplex Λ c)
    intro M hM
    have := hr X c M hM d hd _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl rfl)
    exact ⟨compact_complex_isGE Λ c _ 0, finite_point_sections_isLE Λ k _ _⟩
  · apply reduce (condensedRingOrdinaryCoefficientComplex Λ X.hom)
    intro M hM
    have := hr X c M hM d hd _ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr rfl)
    exact ⟨ordinary_complex_isGE Λ X.hom _ 0, finite_point_sections_isLE Λ k _ _⟩

private theorem finite_point_finite_range
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (n : ℕ) (hn : 1 ≤ n)
    (hc : FinitePointCompactHeartUpperBound
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) k) :
    FinitePointCohomologicalHeartUpperBound
      (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) k := by
  intro X _ _ _ c M hM d hd P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · exact hc X c M hM d hd
  · exact finite_point_finite_ordinary_bound ℓ E n hn X M hM d hd.le

private theorem finite_point_cohomology_of_scalar_and_range [IsSepClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (hs : FinitePointScalarRealizationData Λ k)
    (hr : FinitePointCohomologicalHeartUpperBound Λ k)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    FinitePointCohomology Λ k X := by
  obtain ⟨hpoint, hequiv⟩ := hs
  refine ⟨⟨hpoint, hequiv⟩, ?_⟩
  intro c K
  have hc := direct_images_ctf Λ k ℓ hΛ X c K
  constructor
  · intro Q hQ
    exact ⟨hc Q hQ, fun hX ↦ (direct_images_zero_of_empty Λ k X c K hX).1 Q hQ⟩
  · intro P hP
    have hp : DerivedCategory.IsPerfectRingComplex P := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl
      · exact hpoint ⟨_, hc _ (by simp)⟩
      · exact hpoint ⟨_, hc _ (by simp)⟩
    refine ⟨scalar_duality_of_perfect _ P hp,
      cohomological_range_of_heart Λ k hr X c K P hP, fun hX ↦ ?_⟩
    exact
      ⟨(direct_images_zero_of_empty Λ k X c K hX).2 P hP,
        scalar_zero_dual _ P ((direct_images_zero_of_empty Λ k X c K hX).2 P hP)⟩

private theorem finite_point_finite_of_cohomology
    [IsNoetherianRing (MonObj.Γ Λ)] (X : Over (Spec (.of k)))
    (h : FinitePointCohomology Λ k X) : FinitePointFiniteCohomology Λ k X := by
  intro c K P hP
  exact scalar_finite_cohomology_of_perfect _ P ((h.2 c K).2 P hP).1.1

private theorem uniform_reductions_of_cohomology
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (X : Over (Spec (.of k)))
    (h : FinitePointCohomology (DerivedNakayama.integerRing ℓ E) k X) :
    FinitePointUniformReductions k ℓ E X := by
  intro c K
  let Pc := (condensedRingCompactCoefficientComplex (DerivedNakayama.integerRing ℓ E) c).obj
    K.obj
  let Po := (condensedRingOrdinaryCoefficientComplex
    (DerivedNakayama.integerRing ℓ E) X.hom).obj K.obj
  have hc : DerivedCategory.IsPerfectRingComplex Pc := ((h.2 c K).2 Pc (by simp [Pc])).1.1
  have ho : DerivedCategory.IsPerfectRingComplex Po := ((h.2 c K).2 Po (by simp [Po])).1.1
  obtain ⟨ac, bc, hcb, hc⟩ := DerivedCategory.perfect_scalar_extension_window Pc hc
  obtain ⟨ao, bo, hob, ho⟩ := DerivedCategory.perfect_scalar_extension_window Po ho
  refine ⟨min ac ao, max bc bo, le_trans (min_le_left _ _) (le_trans hcb
    (le_max_left _ _)), ?_⟩
  intro n _ P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl
  · obtain ⟨hp, ht⟩ := hc _ (MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E n))
    exact ⟨hp, ht.mono (min_le_left _ _) (le_max_left _ _)⟩
  · obtain ⟨hp, ht⟩ := ho _ (MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E n))
    exact ⟨hp, ht.mono (min_le_right _ _) (le_max_right _ _)⟩

/-- Perfect complexes at the geometric point and finiteness of both kinds of cohomology,
for the four admissible condensed coefficients of the standing finite-field datum.
Finite extension fields are taken inside the fixed algebraic closure; integer coefficients
and their quotients use the recorded valuation ring and chosen uniformizer after the
canonical universe lift `ULift E`. The lift only changes the carrier universe. All derived
categories and reductions are ordinary and uncompleted. No smoothness, connectedness,
properness, or ambient exceptional-adjoint datum is assumed on X.

Source: latest blueprint, sec-six-functors/sk-lem-finite/_section.md and
sk-lem-finite.proof.md, paragraphs 1--2 and Complement (blueprint: sk-lem-finite).

Proof: the coefficient-admissibility theorem supplies the actual admissibility
witnesses. Point scalar realization supplies perfectness of actual sections of
constructible finite-Tor objects. Exact open
extension followed by admissible proper direct image proves the compact-support
constructibility and finite Tor amplitude; the admissible direct-image theorem gives
the ordinary case. Apply point perfectness to these two native images. Perfect objects
are dualizable, their internal dual is perfect, and the canonical biduality map is
invertible. Over the actual Noetherian scalar rings perfectness gives bounded finite
cohomology. Bounded finite-projective models of the two integral outputs provide
one common Tor interval after every quotient scalar extension.
For the numerical bound, right derived functors and exact open extension preserve
the lower bound. Projectivity of the regular point module makes the actual scalar
sections exact, so they preserve the native constructible-heart upper bound. Apply
that bound to the cohomology sheaves of K. The bounded-heart amplitude theorem
combines their shifted truncation layers into [a,b+2 dim X]. If a>b, K is zero.
On an empty scheme every native
complex is zero, and all four additive functors and scalar duals preserve that zero.
-/
theorem finite_geometric_point_cohomology
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (_hℓ : ℓ ≠ D.p) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (∀ n : ℕ, 1 ≤ n →
      FinitePointCohomology (DerivedNakayama.quotientRing ℓ (ULift.{u} E) n) D.k X) ∧
    FinitePointCohomology (DerivedNakayama.integerRing ℓ (ULift.{u} E)) D.k X ∧
    FinitePointCohomology (Profinite.continuousMapRingObj.{u} E) D.k X ∧
    FinitePointCohomology (Profinite.padicAlgClRingObj.{u} ℓ) D.k X ∧
    FinitePointFiniteCohomology (DerivedNakayama.integerRing ℓ (ULift.{u} E)) D.k X ∧
    FinitePointUniformReductions D.k ℓ (ULift.{u} E) X ∧
    FinitePointFiniteCohomology (Profinite.continuousMapRingObj.{u} E) D.k X ∧
    FinitePointFiniteCohomology (Profinite.padicAlgClRingObj.{u} ℓ) D.k X := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [ringChar.eq D.k D.p]; exact _hℓ.symm⟩
  obtain ⟨haA, haO, haE, haQ⟩ := finite_point_coefficient_admissibility ℓ E
  obtain ⟨hsA, hsO, hsE, hsQ⟩ := finite_point_scalar_realization D ℓ _hℓ E
  obtain ⟨hrA, hrO, hrE, hrQ⟩ := finite_point_cohomological_range D ℓ _hℓ E
  have hA (n : ℕ) (hn : 1 ≤ n) := finite_point_cohomology_of_scalar_and_range _ _ ℓ
    (haA n hn) (hsA n hn) (finite_point_finite_range D.k ℓ E n hn (hrA n hn)) X
  have hO := finite_point_cohomology_of_scalar_and_range _ _ ℓ haO hsO hrO X
  have hE := finite_point_cohomology_of_scalar_and_range _ _ ℓ haE hsE hrE X
  have hQ := finite_point_cohomology_of_scalar_and_range _ _ ℓ haQ hsQ hrQ X
  obtain ⟨hno, hne, hnq⟩ := finite_point_scalar_rings ℓ E
  let := hno
  let := hne
  let := hnq
  exact ⟨hA, hO, hE, hQ, finite_point_finite_of_cohomology _ _ X hO,
    uniform_reductions_of_cohomology D.k ℓ (ULift.{u} E) X hO,
    finite_point_finite_of_cohomology _ _ X hE, finite_point_finite_of_cohomology _ _ X hQ⟩

end AlgebraicGeometry.ProEtale.CondensedRing
