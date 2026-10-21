/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.RealizationScalarFunctor
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso
public import Sheaf.Paper.CompletedTowerDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import all Sheaf.Paper.AdicFiniteExchangeEncoding
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientCompletion
import all Sheaf.AlgebraicGeometry.ContinuousCoefficientPullbackIso
import all Sheaf.Paper.CompletedTowerDirectImage

/-! # Naturality of normalized integral coefficient presentations -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable {T U : Scheme.{u}} [IsNoetherian T] [IsNoetherian U]
  [Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim U ≤ n)]
  [Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]
  [Fact (∀ t : U, IsUnit (l : U.presheaf.stalk t))]
variable (h : T ⟶ U)
  (sT : RealizationScalarFunctorData l E T) (sU : RealizationScalarFunctorData l E U)

private theorem inclusion_eq (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E W) :
    s.inclusion = integralRationalCoefficientMap l E W := by
  apply Sheaf.hom_ext
  ext V a
  have hn := s.inclusion_normalization V.unop a
  apply rationalCoefficientValue_ext l E W V
  exact hn

private theorem integral_projection (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E W) (n : ℕ) :
    s.integralIso.hom ≫ continuousCoefficientReduction l E W n =
      pbcAdicProjection W (pbcIntegralDatum l E) n ≫ (s.finiteIso n).hom := by
  apply (cancel_epi s.integralIso.inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  ext V a
  apply ContinuousMap.ext
  intro x
  apply ULift.down_injective
  exact (s.integral_normalization n V a x).symm

private theorem finite_comparison (W : Scheme.{u}) [IsNoetherian W]
    [Fact (∃ n : ℕ, topologicalKrullDim W ≤ n)]
    [Fact (∀ t : W, IsUnit (l : W.presheaf.stalk t))]
    (s : RealizationScalarFunctorData l E W) (n : ℕ) :
    letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom ≫
        (s.finiteIso n).hom =
      (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (integralCoefficientULift l E n).toCommRingCatIso.hom ≫
        continuousCoefficientConstantComparison W (finiteCoefficientRing l E n) := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ (finiteContinuousCoefficientSheaf l W E n).property
  have hu := finiteScalars_constantUnit (pbcIntegralDatum l E) W n
  ext V a
  apply ContinuousMap.ext
  intro x
  have hn := s.finite_normalization n V a x
  have hunit := congrArg (fun z ↦ (z.app V).hom a) hu
  change _ = _ at hunit
  rw [hunit] at hn
  have hmap := congr_app (toSheafify_naturality (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).map (integralCoefficientULift l E n).toCommRingCatIso.hom)) V
  have hmap' := ConcreteCategory.congr_hom hmap a
  have hc := continuousCoefficientConstantComparison_unit W (finiteCoefficientRing l E n)
  have hc' := ConcreteCategory.congr_hom (congr_app hc V)
    (integralCoefficientULift l E n a)
  let e := (integralCoefficientULift l E n).toCommRingCatIso.hom
  let η := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of (PbcQuotient (pbcIntegralDatum l E) n)))
  let η' := toSheafify (ProEt.topology W)
    ((Functor.const W.ProEtᵒᵖ).obj (finiteCoefficientRing l E n))
  let q := continuousCoefficientConstantComparison W (finiteCoefficientRing l E n)
  let m := sheafifyMap (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).map e)
  change (η'.app V) (e a) = (m.app V) ((η.app V) a) at hmap'
  change (q.hom.app V) ((η'.app V) (e a)) = ContinuousMap.const V.unop.left
    (show finiteCoefficientRing l E n from e a) at hc'
  let f : C(V.unop.left, finiteCoefficientRing l E n) :=
    (s.finiteIso n).hom.hom.app V
      ((pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom.hom.app V
        ((η.app V) a))
  change f x = e a at hn
  let g : C(V.unop.left, finiteCoefficientRing l E n) :=
    q.hom.app V ((m.app V) ((η.app V) a))
  change f x = g x
  rw [hn]
  have hg : g = ContinuousMap.const V.unop.left
      (show finiteCoefficientRing l E n from e a) := by
    change (q.hom.app V) ((m.app V) ((η.app V) a)) = _
    rw [← hmap']
    exact hc'
  exact (congrArg (fun z : C(V.unop.left, finiteCoefficientRing l E n) ↦ z x) hg).symm

private theorem finite_pullback_square (n : ℕ) :
    letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
    letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
    completedFiniteCoefficientMap h (pbcIntegralDatum l E) n ≫ (sT.finiteIso n).hom =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map (sU.finiteIso n).hom ≫
        continuousCoefficientPullback (finiteCoefficientRing l E n) h := by
  letI : TopologicalSpace (finiteCoefficientRing l E n) := ⊥
  letI : DiscreteTopology (finiteCoefficientRing l E n) := ⟨rfl⟩
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  apply (cancel_epi
    (L.map (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom)).mp
  change L.map (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).hom ≫
      (L.map (pbcLevelConstantComparison U (pbcIntegralDatum l E) n).inv ≫
        proEtaleConstantInverseImageMap h CommRingCat.{u + 1} _ ≫
          (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).hom) ≫
            (sT.finiteIso n).hom = _
  simp only [← Category.assoc, ← L.map_comp,
    Iso.hom_inv_id, L.map_id, Category.id_comp]
  rw [Category.assoc, finite_comparison l E T sT n]
  rw [Category.assoc, ← L.map_comp_assoc, finite_comparison l E U sU n, L.map_comp,
    Category.assoc, constantComparison_pullback]
  convert congrArg
    (fun z ↦ z ≫ continuousCoefficientConstantComparison T (finiteCoefficientRing l E n))
    (proEtaleConstantInverseImageMap_naturality h
      (integralCoefficientULift l E n).toCommRingCatIso.hom).symm using 1 <;>
    (simp only [Category.assoc])
  rfl


private theorem integral_pullback_square :
    completedCoefficientMap h (pbcIntegralDatum l E) ≫ sT.integralIso.hom =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map sU.integralIso.hom ≫
        integralContinuousPullback l E h := by
  let L := proEtaleSheafInverseImage h CommRingCat.{u + 1}
  apply integralContinuous_hom_ext l E T
  intro n
  change (_ ≫ sT.integralIso.hom) ≫ continuousCoefficientReduction l E T n =
    (L.map sU.integralIso.hom ≫ _) ≫ continuousCoefficientReduction l E T n
  rw [Category.assoc, integral_projection l E T sT n, ← Category.assoc,
    completedCoefficient_projection]
  rw [Category.assoc, finite_pullback_square l E h sT sU n]
  rw [← L.map_comp_assoc, ← integral_projection l E U sU n, L.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (integralContinuousPullback_reduction l E h n).symm

/-- The normalized scalar maps commute with arbitrary scheme pullback.
Source: Bhatt--Scholze, Lemmas 4.2.12, 6.8.2 and Remark 6.8.15.
(blueprint: lem-weil-pbc-realization-coefficient-square)

Proof: a finite coefficient comparison is uniquely determined by its values on
constant sections, since those sections generate the constant sheaf locally.
The finite normalization of sT and sU therefore identifies their comparisons
with the canonical discrete-function comparisons. Their pullback squares commute
on constants, hence on all sections. The completed comparison is determined by
its finite projections: integral_normalization says that those are pointwise
reduction. Separatedness of the complete valuation ring then gives the integral
pullback square. Finally inclusion_normalization uniquely identifies each
inclusion with pointwise inclusion into E. Continuous precomposition commutes
with this inclusion, proving the displayed scalar square. Empty test objects
cause no exception, since equality of their sections is automatic. -/
theorem realizationCoefficientSquare :
    completedCoefficientMap h (pbcIntegralDatum l E) ≫
        (sT.integralIso.hom ≫ sT.inclusion) =
      (proEtaleSheafInverseImage h CommRingCat.{u + 1}).map
          (sU.integralIso.hom ≫ sU.inclusion) ≫
        rationalContinuousPullback l E h := by
  rw [inclusion_eq l E T sT, inclusion_eq l E U sU, ← Category.assoc,
    integral_pullback_square l E h sT sU, Category.assoc,
    integralContinuousPullback_inclusion, ← Category.assoc, ← Functor.map_comp]


end WeilConjectures
