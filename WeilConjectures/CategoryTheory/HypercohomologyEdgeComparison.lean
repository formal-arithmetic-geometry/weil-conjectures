/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.HypercohomologyLeftEdge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.IdentityDerivedHomologyComparison
public import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit

/-!
# Exact comparison and the hypercohomology left edge

Source: Stacks Project, Derived Categories, Tag 015J, functoriality of the truncation
spectral object; the canonical derived base-change unit equation.
(blueprint: lem-pur-hypercohomology-edge-exact-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe uB vB uB' vB' uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B]
  [IsGrothendieckAbelian.{vB} B] [HasDerivedCategory.{vB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B']
  [IsGrothendieckAbelian.{vB'} B'] [HasDerivedCategory.{vB'} B']
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{vC} C]
  (G : B ⥤ C) (G' : B' ⥤ C) (β : B ⥤ B')
  [G.Additive] [G'.Additive] [β.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]

/-- Remove the derived identity from the canonical derived comparison.
Source: the unit definition of derived base change
(blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
abbrev normalizedDerivedBaseChange (e : G ⋙ 𝟭 C ⟶ β ⋙ G') :
    G.rightDerivedFunctorPlus ⟶ β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  G.rightDerivedFunctorPlus.rightUnitor.inv ≫
    whiskerLeft G.rightDerivedFunctorPlus (mapDerivedCategoryPlusIdIso C).inv ≫
    rightDerivedFunctorPlusBaseChange e

/-- The degree-zero base change map, read through `R⁰G ≅ G`, is the given transformation.
Source: Stacks Project, Derived Categories, Tag 05TD, part (3)
(blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
@[reassoc]
lemma rightDerivedBaseChange_zero_rightDerivedZeroIsoSelf (e : G ⋙ 𝟭 C ⟶ β ⋙ G') (Y : B) :
    (rightDerivedBaseChange e 0).app Y ≫ G'.rightDerivedZeroIsoSelf.hom.app (β.obj Y) =
      G.rightDerivedZeroIsoSelf.hom.app Y ≫ e.app Y := by
  rw [← cancel_epi (G.toRightDerivedZero.app Y)]
  have h := rightDerivedBaseChange_zero_unit e Y
  rw [Functor.id_map] at h
  rw [reassoc_of% h, rightDerivedZeroIsoSelf_inv_hom_id_app,
    rightDerivedZeroIsoSelf_inv_hom_id_app_assoc,
    Category.comp_id]

/-- The explicit components of the left-edge target identification.
Source: Stacks Project, Tag 015J (blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
lemma hypercohomologyLeftEdgeTargetIso_hom_app (n : ℕ) (K : DerivedCategory.Plus B) :
    (G.hypercohomologyLeftEdgeTargetIso n).hom.app K =
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.eTruncLTCompETruncGEIso (n : ℤ)).hom.app K)) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map
        (((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).inv.app
          ((DerivedCategory.Plus.homologyFunctor B n).obj K))) ≫
      (DerivedCategory.Plus.homologyFunctor C n).map
        ((G.rightDerivedFunctorPlus.commShiftIso (-(n : ℤ))).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B n).obj K))) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso (-(n : ℤ)) n 0 (by ring)).hom.app
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj
          ((DerivedCategory.Plus.homologyFunctor B n).obj K))) ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0).hom.app
        ((DerivedCategory.Plus.homologyFunctor B n).obj K) ≫
      G.rightDerivedZeroIsoSelf.hom.app ((DerivedCategory.Plus.homologyFunctor B n).obj K) := by
  simp only [hypercohomologyLeftEdgeTargetIso]
  rfl

/-- The morphism of truncation spectral objects induced by the derived base change
`R⁺G ⟶ β⁺ ⋙ R⁺G'` and by the commutation of `β⁺` with truncations.
Source: Stacks Project, Tag 015J, functoriality of the truncation spectral object
(blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
noncomputable def hypercohomologySpectralObjectBaseChange (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) :
    G.hypercohomologySpectralObjectFunctor.obj K ⟶
      G'.hypercohomologySpectralObjectFunctor.obj (β.mapDerivedCategoryPlus.obj K) :=
  ((DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObjectCompMapSpectralObjectIso
      (DerivedCategory.Plus.homologyFunctor C 0) (𝟭 C).mapDerivedCategoryPlus (𝟭 C)
      (fun n ↦ (𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso n)
      (fun a a' h X ↦ (𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso_hom_app_shiftIso
        1 a a' h X) EInt).hom.app
      ((G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt).obj
        (DerivedCategory.Plus.TStructure.t.spectralObjectFunctor.obj K)) ≫
    ((DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt).map
      ((mapTriangulatedSpectralObjectCompIso _ _ EInt).inv.app _ ≫
        (NatTrans.mapTriangulatedSpectralObject (rightDerivedFunctorPlusBaseChange e)
          EInt).app _ ≫
        (mapTriangulatedSpectralObjectCompIso _ _ EInt).hom.app _ ≫
        (G'.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt).map
          ((β.mapDerivedCategoryPlus.mapTriangulatedSpectralObjectIso
            DerivedCategory.Plus.TStructure.t DerivedCategory.Plus.TStructure.t).hom.app K))

/-- The components of `hypercohomologySpectralObjectBaseChange` at `a ≤ b`.
Source: Stacks Project, Tag 015J (blueprint: lem-pur-hypercohomology-edge-exact-comparison). -/
lemma hypercohomologySpectralObjectBaseChange_hom_app (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) (n : ℤ) (a b : EInt) (hab : a ≤ b) :
    ((hypercohomologySpectralObjectBaseChange G G' β e K).hom n).app
        (ComposableArrows.mk₁ (homOfLE hab)) =
      ((𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          (G.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj a).obj
              ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj b).obj K))) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          ((rightDerivedFunctorPlusBaseChange e).app _) ≫
        (DerivedCategory.Plus.homologyFunctor C n).map (G'.rightDerivedFunctorPlus.map
          (β.mapDerivedCategoryPlus.eTruncGELTIsoApp DerivedCategory.Plus.TStructure.t
            DerivedCategory.Plus.TStructure.t a b K).hom) := by
  rw [hypercohomologySpectralObjectBaseChange]
  erw [Abelian.SpectralObject.comp_hom, NatTrans.comp_app]
  simp only [mapHomologicalSpectralObjectCompMapSpectralObjectIso, NatIso.ofComponents_hom_app,
    mapHomologicalSpectralObject_map_hom, Triangulated.SpectralObject.comp_hom,
    mapTriangulatedSpectralObjectCompIso_inv_app_hom,
    NatTrans.mapTriangulatedSpectralObject_app_hom,
    mapTriangulatedSpectralObjectCompIso_hom_app_hom, whiskerRight_app]
  erw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.id_app, NatTrans.id_app,
    Category.id_comp, Category.id_comp, Functor.map_comp]
  erw [NatTrans.id_app, Functor.map_id, Category.id_comp, NatTrans.comp_app, NatTrans.comp_app,
    NatTrans.id_app, Category.id_comp, Functor.map_comp]
  rfl


/-- The truncation comparison of an exact functor on the whole interval is the identity. -/
lemma mapDerivedCategoryPlus_eTruncGELTIsoApp_bot_top (K : DerivedCategory.Plus B) :
    (β.mapDerivedCategoryPlus.eTruncGELTIsoApp DerivedCategory.Plus.TStructure.t
      DerivedCategory.Plus.TStructure.t ⊥ ⊤ K).hom = 𝟙 _ := by
  simp [Functor.eTruncGELTIsoApp, Functor.eTruncGEIsoApp, Functor.eTruncLTIsoApp]


/-- Exact comparison preserves the canonical normalized hypercohomology left edge.
Source: functoriality of the truncation spectral object and the derived base-change
unit equation (blueprint: lem-pur-hypercohomology-edge-exact-comparison).

Proof:
1. Write τ for the normalized derived comparison. It commutes with shifts: the
canonical derived-identity isomorphism does so after restriction to the bounded-below
homotopy category, and `rightDerivedFunctorPlusBaseChange` commutes with shifts by
its unit characterization. The comparison of truncation spectral objects is the
composite of `τ.mapTriangulatedSpectralObject`, the functor-composition comparison,
and the image under RG' of `β.mapTriangulatedSpectralObjectObjIso`.
2. Apply `Abelian.SpectralObject.leftEdge_naturality`. On the interval from bottom
to top its component is H^q(τ_K), because both extended truncations are identities.
3. On the interval [q,q+1), identify each truncation with H^q(K)[-q]. The identity
`mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso`, with ψ the identity,
identifies the β-truncation comparison with β applied to the single-degree
identification, followed by β's shift comparison, its single-functor comparison,
and the single functor applied to its homology comparison.
4. Naturality of τ moves the single-degree identification past τ. Its shift
compatibility and homology-shift naturality reduce the remaining comparison to
an object in degree zero. Apply `rightDerivedBaseChange_zero_unit`: cancel the
invertible degree-zero unit of G, and use the canonical single/derived homology
isomorphisms. This gives e at H^q(K), followed by G' of β's homology comparison.
Substitute this target component in Step 2 and associate the composites. -/
theorem hypercohomologyLeftEdge_exactComparison (e : G ⋙ 𝟭 C ⟶ β ⋙ G')
    (K : DerivedCategory.Plus B) [K.IsGE 0]
    [(β.mapDerivedCategoryPlus.obj K).IsGE 0] (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor C q).map
        ((normalizedDerivedBaseChange G G' β e).app K) ≫
      (G'.hypercohomologySpectralObjectFunctor.obj (β.mapDerivedCategoryPlus.obj K)).leftEdge q ≫
      (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
    (G.hypercohomologySpectralObjectFunctor.obj K).leftEdge q ≫
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
      e.app ((DerivedCategory.Plus.homologyFunctor B q).obj K) ≫
      G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) := by
  have hbot : (DerivedCategory.Plus.homologyFunctor C q).map
      ((normalizedDerivedBaseChange G G' β e).app K) =
      ((hypercohomologySpectralObjectBaseChange G G' β e K).hom q).app
        (ComposableArrows.mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) := by
    rw [hypercohomologySpectralObjectBaseChange_hom_app]
    erw [mapDerivedCategoryPlus_eTruncGELTIsoApp_bot_top, Functor.map_id, Functor.map_id,
      Category.comp_id]
    simp only [NatTrans.comp_app, whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp,
      Functor.map_comp, identityDerivedHomologyComparison]
    rfl
  have hE' : (((𝟭 C).mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
          (G.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj ((q : ℤ) : EInt)).obj
              ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj ((q + 1 : ℤ) : EInt)).obj K))) ≫
        (DerivedCategory.Plus.homologyFunctor C q).map
          ((rightDerivedFunctorPlusBaseChange e).app _) ≫
        (DerivedCategory.Plus.homologyFunctor C q).map (G'.rightDerivedFunctorPlus.map
          (β.mapDerivedCategoryPlus.eTruncGELTIsoApp DerivedCategory.Plus.TStructure.t
            DerivedCategory.Plus.TStructure.t ((q : ℤ) : EInt) ((q + 1 : ℤ) : EInt) K).hom)) ≫
        (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
        e.app ((DerivedCategory.Plus.homologyFunctor B q).obj K) ≫
        G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) := by
    -- Remaining: unfold both target isomorphisms, use
    -- `mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso`, naturality of the
    -- base change and of the shift isomorphisms, then
    -- `rightDerivedBaseChange_zero_rightDerivedZeroIsoSelf`.
    sorry
  have hE : ((hypercohomologySpectralObjectBaseChange G G' β e K).hom q).app
        (ComposableArrows.mk₁ (homOfLE
          (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) ≫
        (G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K) =
      (G.hypercohomologyLeftEdgeTargetIso q).hom.app K ≫
        e.app ((DerivedCategory.Plus.homologyFunctor B q).obj K) ≫
        G'.map ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app K) :=
    (congrArg (· ≫ _) (hypercohomologySpectralObjectBaseChange_hom_app G G' β e K q _ _
      (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))).trans hE'
  have hnat := (reassoc_of% (Abelian.SpectralObject.leftEdge_naturality
    (hypercohomologySpectralObjectBaseChange G G' β e K) (q : ℤ)))
    ((G'.hypercohomologyLeftEdgeTargetIso q).hom.app (β.mapDerivedCategoryPlus.obj K))
  rw [hE] at hnat
  exact (congrArg (· ≫ _) hbot).trans hnat

end CategoryTheory.Functor
