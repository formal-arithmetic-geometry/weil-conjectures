/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerRealizedProperOpenCoordinates
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenModel
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerProperOpenCoordinates
import all WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerRealizedProperOpenCoordinates
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOrdinaryCompEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerOrdinaryUnitEvaluation
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenCore
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareComposition

/-! # A component of geometric open-word normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂]
  (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₀₂ : C₀ ⥤ C₂)
  (G₀₁ : D₀ ⥤ D₁) (G₁₂ : D₁ ⥤ D₂) (G₀₂ : D₀ ⥤ D₂)
  (U₀ : C₀ ⥤ D₀) (U₁ : C₁ ⥤ D₁) (U₂ : C₂ ⥤ D₂)
  [F₀₁.Additive] [F₁₂.Additive] [F₀₂.Additive]
  [G₀₁.Additive] [G₁₂.Additive] [G₀₂.Additive]
  [U₀.Additive] [U₁.Additive] [U₂.Additive]
  [PreservesFiniteLimits F₀₁] [PreservesFiniteColimits F₀₁]
  [PreservesFiniteLimits F₁₂] [PreservesFiniteColimits F₁₂]
  [PreservesFiniteLimits F₀₂] [PreservesFiniteColimits F₀₂]
  [PreservesFiniteLimits G₀₁] [PreservesFiniteColimits G₀₁]
  [PreservesFiniteLimits G₁₂] [PreservesFiniteColimits G₁₂]
  [PreservesFiniteLimits G₀₂] [PreservesFiniteColimits G₀₂]
  [PreservesFiniteLimits U₀] [PreservesFiniteColimits U₀]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits (F₀₁ ⋙ F₁₂)] [PreservesFiniteColimits (F₀₁ ⋙ F₁₂)]
  [PreservesFiniteLimits (G₀₁ ⋙ G₁₂)] [PreservesFiniteColimits (G₀₁ ⋙ G₁₂)]


private theorem derived_conjugated_word
    (q₀₁ : F₀₁ ⋙ U₁ ≅ U₀ ⋙ G₀₁)
    (q₁₂ : F₁₂ ⋙ U₂ ≅ U₁ ⋙ G₁₂)
    (q₀₂ : F₀₂ ⋙ U₂ ≅ U₀ ⋙ G₀₂)
    (cF : F₀₁ ⋙ F₁₂ ≅ F₀₂) (cG : G₀₁ ⋙ G₁₂ ≅ G₀₂)
    (h : ∀ X : C₀, U₂.map (cF.hom.app X) ≫ q₀₂.hom.app X =
      q₁₂.hom.app (F₀₁.obj X) ≫ G₁₂.map (q₀₁.hom.app X) ≫
        cG.hom.app (U₀.obj X)) (K : DerivedCategory C₀) :
    G₁₂.mapDerivedCategory.map ((mapDerivedCategorySquareIso q₀₁).inv.app K) ≫
      (mapDerivedCategorySquareIso q₁₂).inv.app (F₀₁.mapDerivedCategory.obj K) ≫
      U₂.mapDerivedCategory.map
        (((mapDerivedCategoryCompIso F₀₁ F₁₂).symm ≪≫
          mapDerivedCategoryNatIso cF).hom.app K) ≫
      (mapDerivedCategorySquareIso q₀₂).hom.app K =
    ((mapDerivedCategoryCompIso G₀₁ G₁₂).symm ≪≫
      mapDerivedCategoryNatIso cG).hom.app (U₀.mapDerivedCategory.obj K) := by
  have hq (X : C₀) : U₂.map (cF.inv.app X) ≫ q₁₂.hom.app (F₀₁.obj X) ≫
      G₁₂.map (q₀₁.hom.app X) = q₀₂.hom.app X ≫ cG.inv.app (U₀.obj X) := by
    have hh := congrArg (fun t ↦ U₂.map (cF.inv.app X) ≫ t ≫
      cG.inv.app (U₀.obj X)) (h X)
    simp only [Category.assoc, ← U₂.map_comp_assoc, Iso.inv_hom_id_app,
      Iso.hom_inv_id_app, Category.comp_id] at hh
    erw [U₂.map_id, Category.id_comp] at hh
    erw [Category.comp_id] at hh
    exact hh.symm
  have hd := mapDerivedCategorySquareIso_comp F₀₁ F₁₂ F₀₂ G₀₁ G₁₂ G₀₂ U₀ U₁ U₂
    q₀₁ q₁₂ q₀₂ cF.symm cG.symm hq
  generalize h01 : mapDerivedCategorySquareIso q₀₁ = d01 at hd ⊢
  generalize h12 : mapDerivedCategorySquareIso q₁₂ = d12 at hd ⊢
  generalize h02 : mapDerivedCategorySquareIso q₀₂ = d02 at hd ⊢
  have hi := congrArg (fun z ↦ z.inv.app K ≫
    d02.hom.app K) hd
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app, whiskerRight_app,
    associator_hom_app, associator_inv_app, Category.id_comp, Category.comp_id,
    mapDerivedCategoryNatIso_symm, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_app] at hi
  have hF : (mapDerivedCategoryNatIso cF.symm).inv =
      (mapDerivedCategoryNatIso cF).hom := by
    simpa only [Iso.symm_symm_eq] using (mapDerivedCategoryNatIso_symm cF.symm).symm
  have hG : (mapDerivedCategoryNatIso cG.symm).inv =
      (mapDerivedCategoryNatIso cG).hom := by
    simpa only [Iso.symm_symm_eq] using (mapDerivedCategoryNatIso_symm cG.symm).symm
  rw [hF, hG] at hi
  simpa only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom] using hi
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates

attribute [local instance] GraphCoordinates.additive GraphCoordinates.inverseAdditive
  VaryingRing.extensionAdditive VaryingRing.extensionLimits VaryingRing.extensionColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem exact_derived_congr
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    {G H : A ⥤ B} [G.Additive] [H.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (h : G = H) :
    G.mapDerivedCategory = H.mapDerivedCategory := by
  subst H
  rfl

private theorem derived_square_eqToIso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : A ⥤ B} {V : B ⥤ D} {U : A ⥤ C} {G H : C ⥤ D}
    [F.Additive] [V.Additive] [U.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (q : F ⋙ V ≅ U ⋙ G) (h : G = H) :
    Functor.mapDerivedCategorySquareIso (q ≪≫ Functor.isoWhiskerLeft U (eqToIso h)) =
      Functor.mapDerivedCategorySquareIso q ≪≫
        Functor.isoWhiskerLeft U.mapDerivedCategory
          (eqToIso (exact_derived_congr h)) := by
  subst H
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl]

/-- The prescribed ordinary open-coordinate comparison, descended termwise.
Source: fixed graph coordinates
(blueprint: lem-sp-graph-open-composition-normalization). -/
def sequenceOpenCoordinates (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [((g.presentation U).functor).Additive]
    [((g.presentation X).functor).Additive]
    [(VaryingRing.extension (graphRings l E) (graphTransitions l E) j).Additive]
    [PreservesFiniteLimits (g.presentation U).functor]
    [PreservesFiniteColimits (g.presentation U).functor]
    [PreservesFiniteLimits (g.presentation X).functor]
    [PreservesFiniteColimits (g.presentation X).functor]
    [PreservesFiniteLimits
      (VaryingRing.extension (graphRings l E) (graphTransitions l E) j)]
    [PreservesFiniteColimits
      (VaryingRing.extension (graphRings l E) (graphTransitions l E) j)] :
    SpTowerShriek.openD l E b (o.openOp j) ⋙
        (g.presentation X).functor.mapDerivedCategory ≅
      (g.presentation U).functor.mapDerivedCategory ⋙
        VaryingRing.J (graphRings l E) (graphTransitions l E) j :=
  Functor.mapDerivedCategorySquareIso (graphOpenSquare l E b o g j)

set_option maxHeartbeats 20000000 in
private theorem graphOpenSquare_derived (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [((g.presentation U).functor).Additive]
    [((g.presentation X).functor).Additive]
    [(VaryingRing.extension (graphRings l E) (graphTransitions l E) j).Additive]
    [PreservesFiniteLimits
      (VaryingRing.extension (graphRings l E) (graphTransitions l E) j)]
    [PreservesFiniteColimits
      (VaryingRing.extension (graphRings l E) (graphTransitions l E) j)]
    [PreservesFiniteLimits (g.presentation U).functor]
    [PreservesFiniteColimits (g.presentation U).functor]
    [PreservesFiniteLimits (g.presentation X).functor]
    [PreservesFiniteColimits (g.presentation X).functor] :
    Functor.mapDerivedCategorySquareIso (graphOpenSquare l E b o g j) =
      sequenceOpenCoordinates l E b o g j := by
  rfl

/-- The transported termwise ordinary open compositor is the specified model
open compositor, before realization or proper image.
Source: Local pairs, normalized ordinary adjunctions, Stacks 03DI
(blueprint: lem-sp-graph-open-composition-normalization).

Proof: evaluate o.comp_termwise and o.comp_evaluation on complexes concentrated
in degree zero. Apply degree-zero homology and faithful component sections to
identify the supplied ordinary pull compositor with the canonical one under the
section-pinned graph pull coordinates. The push comparisons preserve the given
ordinary units and counits, by their section pins and geometric normalizations.
The adjunction bijection therefore identifies the two ordinary open compositors
obtained by left-adjoint uniqueness. Apply exact derived localization to this
ordinary natural-transformation equation. Naturality of the localization
composition isomorphisms and their associativity identifies its two sides with
the displayed conjugated word and namedJComp, respectively. No derived
joint-faithfulness claim is used. Identities and zero objects use the same units. -/
theorem sequence_open_word (b : SpTowerShriek.Base l E)
    (o : SpTowerShriek.Operations l E b) (g : GraphCoordinates l E b o)
    {U X Z : Scheme.{u}} (j : U ⟶ X) (i : X ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i] (M : SpTowerShriek.D l E U) :
    (VaryingRing.J (graphRings l E) (graphTransitions l E) i).map
        ((sequenceOpenCoordinates l E b o g j).inv.app M) ≫
      (sequenceOpenCoordinates l E b o g i).inv.app
        ((SpTowerShriek.openD l E b (o.openOp j)).obj M) ≫
      (g.presentation Z).functor.mapDerivedCategory.map
        ((sequenceOpenComposition l E b o j i).hom.app M) ≫
      (sequenceOpenCoordinates l E b o g (j ≫ i)).hom.app M =
      (VaryingRing.namedJComp (graphRings l E) (graphTransitions l E)
        j i (j ≫ i) rfl).hom.app ((g.presentation U).functor.mapDerivedCategory.obj M)  := by
  letI := g.additive U
  letI := g.additive X
  letI := g.additive Z
  letI := VaryingRing.extensionAdditive (graphRings l E) (graphTransitions l E) j
  letI := VaryingRing.extensionAdditive (graphRings l E) (graphTransitions l E) i
  letI := VaryingRing.extensionAdditive (graphRings l E) (graphTransitions l E) (j ≫ i)
  letI := VaryingRing.extensionLimits (graphRings l E) (graphTransitions l E) j
  letI := VaryingRing.extensionLimits (graphRings l E) (graphTransitions l E) i
  letI := VaryingRing.extensionLimits (graphRings l E) (graphTransitions l E) (j ≫ i)
  letI := VaryingRing.extensionColimits (graphRings l E) (graphTransitions l E) j
  letI := VaryingRing.extensionColimits (graphRings l E) (graphTransitions l E) i
  letI := VaryingRing.extensionColimits (graphRings l E) (graphTransitions l E) (j ≫ i)
  have h := CategoryTheory.Functor.derived_conjugated_word
    (o.openOp j).extension (o.openOp i).extension (o.openOp (j ≫ i)).extension
    (VaryingRing.extension (graphRings l E) (graphTransitions l E) j)
    (VaryingRing.extension (graphRings l E) (graphTransitions l E) i)
    (VaryingRing.extension (graphRings l E) (graphTransitions l E) (j ≫ i))
    (g.presentation U).functor (g.presentation X).functor (g.presentation Z).functor
    (graphOpenSquare l E b o g j) (graphOpenSquare l E b o g i)
    (graphOpenSquare l E b o g (j ≫ i)) (graphOrdinaryOpenComp l E b o j i)
    (VaryingRing.moduleJComp (graphRings l E) (graphTransitions l E) j i)
    (graph_ordinary_open_composition_of_pull l E b o g j i
      (graph_ordinary_pull_composition l E b o g j i)) M
  rw [← graphOpenSquare_derived l E b o g j,
    ← graphOpenSquare_derived l E b o g i,
    ← graphOpenSquare_derived l E b o g (j ≫ i)]
  simpa only [VaryingRing.namedJComp_rfl, VaryingRing.J, VaryingRing.jComp,
    sequenceOpenComposition, graphOrdinaryOpenComp] using h

end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
