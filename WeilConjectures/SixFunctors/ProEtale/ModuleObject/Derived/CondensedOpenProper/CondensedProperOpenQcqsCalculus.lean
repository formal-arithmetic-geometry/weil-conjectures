/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CanonicalRightDerivedAdjunctionShift
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
import WeilConjectures.CategoryTheory.Shift.RestrictFullyFaithful
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.IdIso

/-! # Shift compatibility and image triangles of normalized condensed comparisons

Source: Stacks Project, more-etale.tex Tags 0F7B, 0F7F and 0F7J, and derived.tex
Tags 015F, 05SU and 0A8D
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

/-- The components of the specified transformation give a morphism of the two image
triangles, and both image triangles are distinguished. This packages the last clause,
including the connecting arrow, without choosing a different transformation.
Source: Stacks Tags 0145 and 014Y
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus). -/
def ImageTriangleCompatibility
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ] (τ : F ⟶ H) : Prop :=
  ∀ T : Triangle C, T ∈ distTriang C →
    F.mapTriangle.obj T ∈ distTriang E ∧ H.mapTriangle.obj T ∈ distTriang E ∧
      ∃ φ : F.mapTriangle.obj T ⟶ H.mapTriangle.obj T,
        φ.hom₁ = τ.app T.obj₁ ∧ φ.hom₂ = τ.app T.obj₂ ∧ φ.hom₃ = τ.app T.obj₃

/-- Compatibility with every canonical integer shift and with image distinguished
triangles, also for the unique inverse whenever the specified transformation is invertible.
The inverse is quantified as an isomorphism with this exact forward transformation.
Source: Stacks Tags 05SU, 0145 and 0A8D
(blueprint: lem-zl-condensed-proper-open-qcqs-calculus). -/
def ShiftTriangleCompatibility
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ] (τ : F ⟶ H) : Prop :=
  NatTrans.CommShift τ ℤ ∧ ImageTriangleCompatibility τ ∧
    ∀ e : F ≅ H, e.hom = τ →
      NatTrans.CommShift e.inv ℤ ∧ ImageTriangleCompatibility e.inv

private theorem imageTriangle_of_commShift
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ]
    [F.IsTriangulated] [H.IsTriangulated]
    (τ : F ⟶ H) [NatTrans.CommShift τ ℤ] : ImageTriangleCompatibility τ := by
  intro T hT
  refine ⟨F.map_distinguished T hT, H.map_distinguished T hT, ?_⟩
  let φ : F.mapTriangle.obj T ⟶ H.mapTriangle.obj T :=
    { hom₁ := τ.app T.obj₁
      hom₂ := τ.app T.obj₂
      hom₃ := τ.app T.obj₃
      comm₁ := τ.naturality T.mor₁
      comm₂ := τ.naturality T.mor₂
      comm₃ := by
        change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
            (shiftFunctor E (1 : ℤ)).map (τ.app T.obj₁) =
          τ.app T.obj₃ ≫ H.map T.mor₃ ≫ (H.commShiftIso (1 : ℤ)).hom.app T.obj₁
        rw [Category.assoc, NatTrans.shift_app_comm, ← Category.assoc,
          τ.naturality T.mor₃, Category.assoc] }
  exact ⟨φ, rfl, rfl, rfl⟩

private theorem shiftTriangleCompatibility_of_commShift
    {C : Type v₁} {E : Type v₂} [Category.{w₁} C] [Category.{w₂} E]
    [HasShift C ℤ] [HasShift E ℤ] [HasZeroObject C] [HasZeroObject E]
    [Preadditive C] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated C] [Pretriangulated E]
    {F H : C ⥤ E} [F.CommShift ℤ] [H.CommShift ℤ]
    [F.IsTriangulated] [H.IsTriangulated]
    (τ : F ⟶ H) [NatTrans.CommShift τ ℤ] : ShiftTriangleCompatibility τ := by
  refine ⟨inferInstance, imageTriangle_of_commShift τ, ?_⟩
  intro e he
  have hhom : NatTrans.CommShift e.hom ℤ := by
    rw [he]
    infer_instance
  have : NatTrans.CommShift e.hom ℤ := hhom
  have hinv : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  have : NatTrans.CommShift e.inv ℤ := hinv
  exact ⟨hinv, imageTriangle_of_commShift e.inv⟩

private theorem adjunct_commShift
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
    {F : C ⥤ D} {G : C ⥤ E} {L : D ⥤ E} {R : E ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] [L.CommShift ℤ] [R.CommShift ℤ]
    (adj : L ⊣ R) [adj.CommShift ℤ] (τ : F ⟶ G ⋙ R) [τ.CommShift ℤ] :
    NatTrans.CommShift ((Functor.leftUnitor (F ⋙ L)).inv ≫
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom) ℤ := by
  -- The leading unitor has identity components. Removing it avoids an extra
  -- identity-functor shift structure on the domain of the whiskered transformation.
  have he : (Functor.leftUnitor (F ⋙ L)).inv ≫
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom =
      Functor.whiskerRight τ L ≫ (Functor.associator G R L).hom ≫
      Functor.whiskerLeft G adj.counit ≫ (Functor.rightUnitor G).hom := by
    ext X
    simp
  rw [he]
  infer_instance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Shift-triangle compatibility of direct-image restriction. -/
private theorem derivedDirectImageOpenRestriction_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y X' Y' : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {b : Y' ⟶ Y} (sq : CommSq a f' f b) :
    ShiftTriangleCompatibility (derivedDirectImageOpenRestriction Λ sq) := by
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f')
  have : NatTrans.CommShift (derivedOpenCoherencePullbackSquare Λ sq).hom ℤ := by
    dsimp only [derivedOpenCoherencePullbackSquare, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have : NatTrans.CommShift (derivedDirectImageOpenRestriction Λ sq) ℤ :=
    NatTrans.CommShift.mateEquiv (A := ℤ)
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _ (derivedOpenCoherencePullbackSquare Λ sq).hom)
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the normalized proper/open adjunct. -/
private theorem gamma_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {U W Y Z : Scheme.{u}} {j : U ⟶ W} {p : U ⟶ Y}
    {r : W ⟶ Z} {i : Y ⟶ Z} [IsOpenImmersion j] [IsOpenImmersion i]
    [QuasiCompact j] [QuasiCompact i] [IsProper p] [IsProper r]
    (units : OpenUnits Λ) (sq : CommSq j p r i) :
    ShiftTriangleCompatibility (gamma Λ units sq) := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ p).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ r).2.1
  have := (derivedDirectImageOpenRestriction_shiftTriangle Λ sq).1
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (units.unitIso j).hom ℤ := by
    rw [units.normalized]
    infer_instance
  have : NatTrans.CommShift (restriction Λ units sq) ℤ := by
    dsimp only [restriction]
    infer_instance
  have : NatTrans.CommShift (comparisonInverse (restriction Λ units sq)) ℤ := by
    classical
    unfold comparisonInverse
    split_ifs with h
    · exact NatTrans.CommShift.of_iso_inv (asIso (restriction Λ units sq)) ℤ
    · constructor
      intro n
      ext K
      simp
  have : NatTrans.CommShift (gamma Λ units sq) ℤ :=
    adjunct_commShift (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i)
      (comparisonInverse (restriction Λ units sq))
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of pullback compositors. -/
private theorem pComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftTriangleCompatibility (pComp Λ f g).hom := by
  have : NatTrans.CommShift (pComp Λ f g).hom ℤ := by
    dsimp only [pComp, Iso.trans_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the direct-image compositor. -/
private theorem rComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShiftTriangleCompatibility (rComp Λ f g).hom := by
  have := (module_derived_functors_exact_and_comparison_shifts Λ f).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ g).2.1
  have := (module_derived_functors_exact_and_comparison_shifts Λ (f ≫ g)).2.1
  have := (pComp_shiftTriangle Λ f g).1
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ f)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ g)
  have := canonicalRightDerivedAdjunctionShift (upperStarLowerStarAdjunction Λ (f ≫ g))
  have : NatTrans.CommShift (rComp Λ f g).hom ℤ := by
    dsimp only [rComp, Iso.symm_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

/-- Shift-triangle compatibility of the open compositor. -/
private theorem jComp_shiftTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
    [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (j : X ⟶ Y) (i : Y ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] :
    ShiftTriangleCompatibility (jComp Λ j i).hom := by
  have := (pComp_shiftTriangle Λ j i).1
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ j).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).commShift_mapDerivedCategoryAdjunction
  have : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).CommShift ℤ :=
    (openImmersionLowerShriekUpperStarAdjunction Λ (j ≫ i)).commShift_mapDerivedCategoryAdjunction
  have : NatTrans.CommShift (jComp Λ j i).hom ℤ := by
    dsimp only [jComp, Iso.symm_hom]
    infer_instance
  exact shiftTriangleCompatibility_of_commShift _

set_option synthInstance.maxHeartbeats 200000 in
-- The calculus contains many derived-functor instance searches.
end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
