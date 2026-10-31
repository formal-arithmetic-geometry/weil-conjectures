/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Supporting.ConstantCoefficientScalarNormalization
public import WeilConjectures.SmoothPurity.Completed.CompletedPrimitiveCounitComparison
public import WeilConjectures.AlgebraicGeometry.QuotientFrobenius.QuotientCornerFrobeniusStructures
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitReduction
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitAdmissible
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitMultiplicationComponents
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitScalarNaturality

/-! # Completed coefficient units and coherent pullback

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2.
(blueprint: lem-pur-completed-unit-pullback-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] constantSheaf HasDerivedCategory.standard
  Scheme.coefficientProEtaleDirectRingMap WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
  WeilConjectures.PrimitiveCounit.ringMap

namespace WeilConjectures.CompletedUnitPullback
attribute [local irreducible] calculus systemUnit systemObject systemMap systemMultiplication
  finiteMultiplication rationalSource modelScalar modelUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem finiteMultiplication_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (finiteMultiplication l E f n) := by
  have h := Scheme.coefficientProEtaleModuleDirectImage_isRightAdjoint.{u, u} f
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  unfold Scheme.coefficientProEtaleModuleDirectImage at h
  let := h
  unfold finiteMultiplication Scheme.coefficientProEtaleModuleAdjunction
  change IsIso (SheafOfModules.pullbackObjUnitToUnit _)
  infer_instance

private theorem systemMultiplication_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (systemMultiplication l E f) := by
  have h := PrimitiveCounit.direct_isRightAdjoint.{u, u} l E f
  unfold PrimitiveCounit.direct at h
  let := h
  let : (PrimitiveCounit.base f).Final := by
    unfold PrimitiveCounit.base
    infer_instance
  unfold systemMultiplication systemUnit
  change IsIso (SheafOfModules.pullbackObjUnitToUnit _)
  infer_instance

private theorem normalized_iso (W : Scheme.{u})
    {A B : coefficientSequenceDerived l E W} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  intro m n h P
  let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
  let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
  let G := normalizedDVRRes l E W h
  have hn := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
  change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app B =
    (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map en.hom at hn
  constructor
  · intro x y hxy
    apply (cancel_epi en.hom).1
    apply (hA h P).injective
    change (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map (en.hom ≫ x) =
      (coefficientSequenceDerivedTransition l E W h).app A ≫ G.map (en.hom ≫ y)
    change (coefficientSequenceDerivedTransition l E W h).app B ≫ G.map x =
      (coefficientSequenceDerivedTransition l E W h).app B ≫ G.map y at hxy
    simp only [G.map_comp, ← Category.assoc, ← hn]
    simpa only [Category.assoc] using congrArg (fun k ↦ em.hom ≫ k) hxy
  · intro t
    obtain ⟨s, hs⟩ := (hA h P).surjective (em.hom ≫ t)
    refine ⟨en.inv ≫ s, ?_⟩
    apply (cancel_epi em.hom).1
    change em.hom ≫ (coefficientSequenceDerivedTransition l E W h).app B ≫
      G.map (en.inv ≫ s) = em.hom ≫ t
    rw [G.map_comp, ← Category.assoc, hn]
    simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_assoc]
    exact hs

private theorem counit_from_augmentation
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {A : C} {B : D} (r : F.obj A ≅ B) (a : A ≅ G.obj B)
    (ha : a.hom = adj.unit.app A ≫ G.map r.hom) :
    F.map a.inv ≫ r.hom = adj.counit.app B := by
  apply (cancel_epi (F.map a.hom)).1
  simp only [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id,
    Category.id_comp]
  rw [ha, F.map_comp, Category.assoc]
  have hn := adj.counit.naturality r.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [← Category.assoc, adj.left_triangle_components, Category.id_comp]

private theorem core_exists (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Core l E f) := by
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦ IsUnit.invertible (by
    simpa only [map_natCast] using (hX x).map (X.residue x).hom)
  let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦ IsUnit.invertible (by
    simpa only [map_natCast] using (hY y).map (Y.residue y).hom)
  have aX := completedUnitAdmissible l E D hl X
  have aY := completedUnitAdmissible l E D hl Y
  obtain ⟨rX⟩ := completedUnitReduction l E D hl X hX
  obtain ⟨rY⟩ := completedUnitReduction l E D hl Y hY
  have hNX : IsNormalizedCoefficientSequence l E X (systemObject l E X) :=
    normalized_iso l E X rX.comparison
    ((calculus l E X).reduction_normalized _)
  have hNY : IsNormalizedCoefficientSequence l E Y (systemObject l E Y) :=
    normalized_iso l E Y rY.comparison
    ((calculus l E Y).reduction_normalized _)
  let := systemMultiplication_isIso l E f
  have hsys : IsIso (systemMap l E f) := by
    unfold systemMap systemObject
    infer_instance
  let := hsys
  have hNP : IsNormalizedCoefficientSequence l E X
      ((PrimitiveCounit.pull l E f).obj (systemObject l E Y)) :=
    normalized_iso l E X (asIso (systemMap l E f)).symm hNX
  obtain ⟨ρW, ρX, ⟨cmp⟩⟩ := completedPrimitiveCounitComparison l E f X hX hY hX
    (calculus l E X).toCoefficientDerivedSystemReduction
    (calculus l E Y).toCoefficientDerivedSystemReduction
  let d := (PrimitiveCounit.pull l E f).mapIso rY.comparison ≪≫
    asIso (systemMap l E f)
  let e := cmp.geometric.app (integralConstantCoefficientObject l E Y) ≪≫
    (coefficientSequenceLimit l E X).mapIso d ≪≫ rX.augmentation.symm
  refine ⟨{
    admissibleX := aX
    admissibleY := aY
    reductionX := rX
    reductionY := rY
    normalizedX := hNX
    normalizedY := hNY
    normalizedPull := hNP
    finite_iso := finiteMultiplication_isIso l E f
    system_iso := hsys
    finite_components := completedUnitMultiplicationComponents l E f rX rY
    roos := ρX
    realization := cmp.geometric
    realization_model := cmp.geometric_model
    unit := e
    unit_formula := rfl
    coherent_reduction := ?_ }⟩
  have ha := counit_from_augmentation (calculus l E X).adjunction
    rX.comparison rX.augmentation rX.augmentation_eq
  dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [ha]
  have hn := (calculus l E X).adjunction.counit.naturality d.hom
  simpa only [Functor.comp_map, Functor.id_map, Category.assoc, d, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom, Iso.app_hom]
    using congrArg (fun k ↦ (calculus l E X).reduction.map
      (cmp.geometric.hom.app (integralConstantCoefficientObject l E Y)) ≫ k) hn

private theorem rationalMap_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (c : Core l E f) :
    IsIso (rationalMap l E f c.admissibleX.1.1 c.admissibleY.1.1 c.unit.hom) := by
  let e : (constructibleIntegralPullback l E f).obj
        (integralObject l E Y c.admissibleY.1.1) ≅
      integralObject l E X c.admissibleX.1.1 :=
    ObjectProperty.isoMk _ (by
      change (integralDerivedPullback l E f).obj
          (integralConstantCoefficientObject l E Y) ≅ integralConstantCoefficientObject l E X
      exact c.unit)
  let : IsIso (ObjectProperty.homMk c.unit.hom :
      (constructibleIntegralPullback l E f).obj (integralObject l E Y c.admissibleY.1.1) ⟶
        integralObject l E X c.admissibleX.1.1) := by
    change IsIso e.hom
    infer_instance
  have : IsIso ((sfRationalConstructibleLocalization l E X).map e.hom) := inferInstance
  unfold rationalMap
  change IsIso ((rationalSource l E f c.admissibleY.1.1).hom ≫
    (sfRationalConstructibleLocalization l E X).map e.hom)
  infer_instance

/-- Completed coefficient units have uniform zero cohomological and Tor bounds,
and their actual quotient multiplications induce the specified coherent pullback
unit and its rational and common-stage images.

Source: blueprint smooth purity, cor-pur-adic-and-rational-smooth-dualizing-complexes,
proof first sentence; Bhatt--Scholze, Sections 3.5 and 6.5, Lemmas 6.5.9 and 6.8.2
(blueprint: lem-pur-completed-unit-pullback-tower).

Proof:
1. Use the regular completed sheaf in degree zero. Multiplication identifies each
K-flat reduction with the finite regular sheaf: r tensor z maps to pi_n(r)z, with
inverse z to 1 tensor z. The reduction legs are pi_n and the transitions are the
actual quotient maps. The same multiplication proves normalization of the system.
2. The finite quotient maps are surjective. The pro-etale surjective-tower theorem
and the normalized strict Roos comparison identify the augmentation with the map
whose product coordinates are pi_n and whose shifted-product coordinate is zero.
It is a quasi-isomorphism. Its adjoint under reduction/total limit is the comparison
with the regular sequence-site module. Its finite adjoints are the displayed maps.
3. Each finite regular sheaf is constant on W itself and has finite stalks. Tensor
with that rank-one regular module is the identity and hence exact. Thus its single
complex and every reduction have cohomological and Tor interval [0,0], uniformly.
This proves the complete constructible finite-Tor membership of the integral unit.
4. At each level the adjoint of the constant-section ring map is multiplication
b tensor a to b c_f(a), inverse b to b tensor 1. The ring maps commute with quotient
maps, including identities. Hence these are the components of the single strict
systemMultiplication, and its derived systemMap is an isomorphism of normalized systems.
5. The normalized K-flat Roos realization identifies the specified integral pullback
with total limit of the pulled reduction system. Apply that total limit to the
whole-system multiplication and compose with the inverse augmentation on X. This
is unit_formula. Counit naturality and the adjunction triangle, together with the
actual augmentation identification in Step 2, give coherent_reduction in the
system derived category itself. No equality is deduced only from finite evaluations.
6. Raw rationalization sends this very integral unit arrow to v tensor 1, with
inverse the image of its inverse. Its image under the same-stage inclusion is the
common-stage coefficient-unit identification. The two composite inverses are
identities over that finite stage, so both arrows are isomorphisms. In particular
the completed integral unit is a lattice for both units. Canonical algebra-equivalent
small coefficient models transport this calculation. The normalized scalar-unit
and pullback-scalar comparisons commute on every finite tensor generator; Roos and
rationalization preserve that equality, giving model_square. Thus the common-stage
arrow is the image of the literal E-coefficient arrow, with its specified size transport.
The empty schemes, identity morphism, exponent one and ramified coefficient
fields are covered by the same formulas; no nonempty stratum is required. -/
theorem completedUnitPullbackTower (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [IsSeparated (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))] :
    Nonempty (Result P f) := by
  have hX := fun x : X ↦
    P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k)) x
  have hY := fun y : Y ↦
    P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k)) y
  obtain ⟨c⟩ := core_exists P.coefficients.l P.extension P.field
    P.coefficients.different f hX hY
  obtain ⟨m⟩ := core_exists P.coefficients.l (coefficientModel P) P.field
    P.coefficients.different f hX hY
  let := rationalMap_isIso P.coefficients.l P.extension f c
  let := rationalMap_isIso P.coefficients.l (coefficientModel P) f m
  refine ⟨⟨c, m, inferInstance, inferInstance,
    completedUnitScalarNaturality P f c m, ?_⟩⟩
  unfold commonMap
  infer_instance

end WeilConjectures.CompletedUnitPullback
