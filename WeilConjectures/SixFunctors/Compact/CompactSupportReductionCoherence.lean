/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportNormalizedRealization
public import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity
import all WeilConjectures.SixFunctors.Integral.IntegralCompactSupportPrescribedReductions
import all WeilConjectures.SmoothPurity.Compact.CompactSupportFiniteAction
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Quotient coherence of the canonical compact-support reduction isomorphisms -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem quotientTransition_natural
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (S : B ⥤ A) (e : S ⋙ Rm ≅ Rn)
    {K M : C} (f : K ⟶ M) :
    Lm.map f ≫ (am.homEquiv M _).symm
        (an.unit.app M ≫ e.inv.app (Ln.obj M)) =
      (am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)) ≫
        S.map (Ln.map f) := by
  rw [← am.homEquiv_naturality_left_symm, ← am.homEquiv_naturality_right_symm]
  congr 1
  have hu := an.unit.naturality f
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, hu]
  simp only [Category.assoc]
  congr 1
  exact e.inv.naturality (Ln.map f)

private theorem restrictionTransition_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (S S' : A ⥤ B) {Lm : C ⥤ B} {Rm : B ⥤ C} {Ln : C ⥤ A} {Rn : A ⥤ C}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn)
    (h : S = S') (i : S ≅ S') (hi : HEq i (Iso.refl S'))
    (e : S ⋙ Rm ≅ Rn) (e' : S' ⋙ Rm ≅ Rn) (he : HEq e e') (K : C) :
    (am.homEquiv K _).symm (an.unit.app K ≫ e'.inv.app (Ln.obj K)) ≫
        i.inv.app (Ln.obj K) =
      (am.homEquiv K _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)) := by
  subst S'
  have hi' := eq_of_heq hi
  subst i
  have he' := eq_of_heq he
  subst e'
  simp

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)

/-- The input quotient map is the normalized scalar-adjunction transition.
Source: the two normalized definitions of quotient reduction
(blueprint: lem-sf-compact-support-reduction-coherence).
Proof: identify the quotient restriction functors using their identical sectionwise
ring map. Their composition comparisons are the same normalized restriction
compositor. Both reduction maps are adjuncts of the lower scalar unit, and transport
of the adjunction along that identity gives the displayed equality. -/
theorem coefCompactSupportInputTau_eq (W : Scheme.{u})
    (K : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    coefCompactSupportInputTau l E W K n.le_succ =
      normalizedDVRReductionTransition l E W D hl n.le_succ K := by
  let : (sfCompactSupportFiniteRestriction l E W n).Additive := by
    change (SheafOfModules.restrictScalars _).Additive
    infer_instance
  apply restrictionTransition_transport
    (normalizedDVRRes l E W n.le_succ)
    (sfCompactSupportFiniteRestriction l E W n).mapDerivedCategory
    (normalizedDVRIntegralAdjunction l E W (n + 1))
    (normalizedDVRIntegralAdjunction l E W n)
    ?_ (coefCompactSupportRestrictionIso l E W n.le_succ)
    (restriction_iso_adjacent l E W n)
    (normalizedDVRResCompletedComp l E W D hl n.le_succ)
    (sfCompactSupportDerivedRestrictionComp l E W n)
    (restriction_comp_eq l E W D hl n).symm K
  apply derived_functor_congr
  exact congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
    (quotient_adjacent l E W n)

private theorem chosenReduction_coherent
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    sfCompactSupportChosenReduction l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E K (n + 1) ≫
      coefCompactSupportNormalizedTau l E c K.obj n.le_succ =
    normalizedDVRReductionTransition l E Y D hl n.le_succ
        (sfIntegralCompactSupportValue l E D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c K).obj ≫
      (normalizedDVRRes l E Y n.le_succ).map
        (sfCompactSupportChosenReduction l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n) := by
  let : (sfCompactSupportFiniteRestriction l E Y n).Additive := by
    change (SheafOfModules.restrictScalars _).Additive
    infer_instance
  let := integralOperationsDerivedCountableProducts l E Y
  let h := (exists_isDerivedLimit_and_iso
    (sfCompactSupportTerm l E c K.obj) (sfCompactSupportTransition l E c K.obj)).1
  let M := Classical.choose h
  let hM : IsDerivedLimit (sfCompactSupportTransition l E c K.obj) M :=
    Classical.choose_spec h
  let p := Classical.choose hM
  let δ := Classical.choose (Classical.choose_spec hM)
  have hc := Classical.choose_spec (Classical.choose_spec hM)
  apply adjointTransition (normalizedDVRIntegralAdjunction l E Y (n + 1))
    (normalizedDVRIntegralAdjunction l E Y n) (normalizedDVRRes l E Y n.le_succ)
    (normalizedDVRResCompletedComp l E Y D hl n.le_succ)
  have ht :
      (scalarReductionDerivedRestriction l E Y (n + 1)).map
          (coefCompactSupportNormalizedTau l E c K.obj n.le_succ) ≫
        (normalizedDVRResCompletedComp l E Y D hl n.le_succ).hom.app
          (coefCompactSupportLevel l E c K.obj n) =
      sfCompactSupportTransition l E c K.obj n := by
    unfold coefCompactSupportNormalizedTau
    apply restriction_transport
      (normalizedDVRRes l E Y n.le_succ)
      (sfCompactSupportFiniteRestriction l E Y n).mapDerivedCategory
      (scalarReductionDerivedRestriction l E Y (n + 1))
      (scalarReductionDerivedRestriction l E Y n)
      ?_ (coefCompactSupportRestrictionIso l E Y n.le_succ)
      (restriction_iso_adjacent l E Y n)
      (normalizedDVRResCompletedComp l E Y D hl n.le_succ)
      (sfCompactSupportDerivedRestrictionComp l E Y n)
      (restriction_comp_eq l E Y D hl n).symm
    apply derived_functor_congr
    exact congrArg (fun q ↦ SheafOfModules.restrictScalars.{u + 1} q)
      (quotient_adjacent l E Y n)
  calc
    _ = p ≫ Pi.π (sfCompactSupportTerm l E c K.obj) (n + 1) ≫
        sfCompactSupportTransition l E c K.obj n := by
      erw [Category.assoc, ht]
      congr 2
    _ = _ := adjacentRoosProjection _ M p δ hc n

/-- The actual canonical compact-support reductions commute with successor quotients.
Source: blueprint compact-support reduction tower, Definition 6.7.6 and Lemma 6.7.7
of Bhatt--Scholze, and the normalized scalar-adjunction projection construction
(blueprint: lem-sf-compact-support-reduction-coherence).

Proof: the projections of the chosen Roos triangle commute with its adjacent
transition, since the first two maps of that triangle compose to zero. Transpose
this equality through the two scalar adjunctions. The direct restriction compositor
agrees with the normalized DVR restriction compositor by their sectionwise identity
normalization. This gives the quotient square for the chosen projection adjuncts.
Finally transport the square along the actual object equality defining the integral
support functor. Naturality of the scalar-adjunction transition gives precisely the
square for sfCompactSupportFiniteReductionIso. No faithfulness of restriction and
no additional Tor-amplitude hypothesis is needed. -/
theorem sfCompactSupportFiniteReductionIso_coherent
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :
    (sfCompactSupportFiniteReductionIso l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E K (n + 1)).hom ≫
      coefCompactSupportNormalizedTau l E c K.obj n.le_succ =
    normalizedDVRReductionTransition l E Y D hl n.le_succ
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E).obj K).obj ≫
      (normalizedDVRRes l E Y n.le_succ).map
        (sfCompactSupportFiniteReductionIso l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n).hom := by
  let e := (sfIntegralConstructible l E Y).ι.mapIso
    (eqToIso (sfCompactSupportFiniteIntegralFunctor_obj l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) c E K))
  have hn :
      (scalarReductionDerivedExtension l E Y (n + 1)).map e.hom ≫
        normalizedDVRReductionTransition l E Y D hl n.le_succ _ =
      normalizedDVRReductionTransition l E Y D hl n.le_succ _ ≫
        (normalizedDVRRes l E Y n.le_succ).map
          ((scalarReductionDerivedExtension l E Y n).map e.hom) :=
    quotientTransition_natural
    (normalizedDVRIntegralAdjunction l E Y (n + 1))
    (normalizedDVRIntegralAdjunction l E Y n) (normalizedDVRRes l E Y n.le_succ)
    (normalizedDVRResCompletedComp l E Y D hl n.le_succ) e.hom
  change ((scalarReductionDerivedExtension l E Y (n + 1)).map e.hom ≫
      sfCompactSupportChosenReduction l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c E K (n + 1)) ≫
      coefCompactSupportNormalizedTau l E c K.obj n.le_succ =
    normalizedDVRReductionTransition l E Y D hl n.le_succ _ ≫
      (normalizedDVRRes l E Y n.le_succ).map
        ((scalarReductionDerivedExtension l E Y n).map e.hom ≫
          sfCompactSupportChosenReduction l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n)
  erw [Category.assoc, chosenReduction_coherent D l hl E c K n]
  calc
    _ = ((scalarReductionDerivedExtension l E Y (n + 1)).map e.hom ≫
        normalizedDVRReductionTransition l E Y D hl n.le_succ _) ≫
        (normalizedDVRRes l E Y n.le_succ).map
          (sfCompactSupportChosenReduction l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c E K n) := by
      simp only [e, Functor.mapIso_hom, Category.assoc]
      rfl
    _ = _ := by
      erw [hn, Category.assoc, ← Functor.map_comp]

end WeilConjectures
