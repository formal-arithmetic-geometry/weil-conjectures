/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CanonicalResolutionDerivedIso
import Sheaf.CategoryTheory.CanonicalResolutionHomologyComparison
import WeilConjectures.CategoryTheory.SpectralSequence.Grothendieck

/-! # Resolution comparisons and the composite derived unit

Source: Stacks Project, derived.tex, Tags 015M and 015N.
(blueprint: lem-pc-grothendieck-resolution-unit-comparison).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private lemma resolutionDerivedIso_comp
    {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] [PreservesFiniteLimits G]
    (hFG : ∀ (J : A) [Injective J], G.rightAcyclic (F.obj J))
    {X : A} (I : InjectiveResolution X) :
    (F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G hFG).hom.app
        ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
        G.rightDerivedFunctorPlus.map (resolutionDerivedIso F I).hom =
      (resolutionDerivedIso (F ⋙ G) I).hom ≫
        G.rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient B).obj
            ⟨(F.mapHomologicalComplex _).obj I.cochainComplex, 0, inferInstance⟩) := by
  let L : CochainComplex.Plus A := ⟨I.cochainComplex, 0, inferInstance⟩
  let H := (HomotopyCategory.Plus.quotient A).obj L
  have : ∀ n, Injective (L.obj.X n) := fun n ↦
    inferInstanceAs (Injective (I.cochainComplex.X n))
  let c := F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G hFG
  have hc : (F ⋙ G).rightDerivedFunctorPlusUnit.app H ≫
      c.hom.app (DerivedCategory.Plus.Qh.obj H) =
        G.rightDerivedFunctorPlusUnit.app (F.mapHomotopyCategoryPlus.obj H) ≫
          G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app H) := by
    dsimp [c, Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic]
    have := F.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_of_rightAcyclic G hFG
    simp only [Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
      Functor.rightDerivedNatTrans_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
    exact Functor.rightDerivedFunctorPlusCompUnit_app F G H
  have hn := c.hom.naturality (resolutionAugmentationIso I).hom
  dsimp [resolutionDerivedIso]
  simp only [Functor.map_comp]
  dsimp only [Functor.comp_map] at hn
  erw [← Category.assoc, ← hn, Category.assoc]
  simp only [Category.assoc]
  congr 1
  apply (cancel_epi ((F ⋙ G).rightDerivedFunctorPlusUnit.app H)).1
  erw [← Category.assoc, hc]
  simp [Category.assoc, H, L]
  rfl

/-- Homology of the canonical resolution comparison transports the composite derived unit.
Source: Stacks Project, Tags 015M and 015N, composition unit and abutment identification.
(blueprint: lem-pc-canonical-resolution-composite-unit-comparison).

Proof: Expand grothendieckSpectralObjectHBotTopIso as the inverse composition comparison
followed by the single-object homology comparison. Apply the ordinary canonical
resolution homology identity to F composed with G and cancel its resolution comparison.
The resulting map is homology of the composition comparison followed by RG applied to
the canonical F comparison. Before applying homology, the defining unit equation for
the composition comparison and its naturality along the resolution augmentation give
resolutionDerivedIso_comp above: invert the GF unit and cancel the F unit on the complex
of injectives. Naturality of the G unit along the F map/extension comparison moves that
comparison to its source. The map/extension comparison for GF equals the composite of
G applied to the F comparison and the G comparison; this equality holds degreewise
from the definitions, including the zero terms in negative degrees. Apply homology and
naturality of homologyFunctorObjQIso, then cancel the extension homology comparisons.
The remaining factors are exactly the inverse G map/extension comparison and the G unit
shown on the right. No positive-degree condition is used.
-/
theorem resolution_composite_unit_transport
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{vA} A] {B : Type uB} [Category.{vB} B]
    [Abelian B] [IsGrothendieckAbelian.{vB} B] {C : Type uC} [Category.{vC} C]
    [Abelian C] [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory A]
    [HasDerivedCategory B] [HasDerivedCategory C] (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics)
    (X : A) (I : InjectiveResolution X) (n : ℕ) :
      (I.isoRightDerivedObj (F ⋙ G) n).inv ≫
          (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv.app X ≫
          (DerivedCategory.Plus.homologyFunctor C n).map
            (G.rightDerivedFunctorPlus.map (canonicalResolutionDerivedIso F I).hom) =
        (((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)).extendHomologyIso
          ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv ≫
        HomologicalComplex.homologyMap
          (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).mapExtendIso
            ComplexShape.embeddingUpNat G).inv (n : ℤ) ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso
          (G.mapCochainComplexPlus.obj
            ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
              ComplexShape.embeddingUpNat, 0, inferInstance⟩) n).inv ≫
        (DerivedCategory.Plus.homologyFunctor C n).map
          (G.rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient B).obj
              ⟨((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).extend
                ComplexShape.embeddingUpNat, 0, inferInstance⟩)) := by sorry

end CategoryTheory
