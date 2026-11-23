/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Exact colimits commute with homology

If colimits of shape `J` are exact in an abelian category `C`, then the homology functors
of short complexes and of homological complexes in `C` preserve colimits of shape `J`.
-/

@[expose] public section

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- If colimits of shape `J` are exact in `C`, then the homology of short complexes in `C`
commutes with colimits of shape `J`. -/
instance CategoryTheory.ShortComplex.preservesColimitsOfShape_homologyFunctor
    (C : Type*) [Category* C] [Abelian C] (J : Type*) [Category* J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) := by
  let L := colim (J := J) (C := C)
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence J C).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₁) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₂) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₃) f } }
  have hc : IsColimit c := ShortComplex.isColimitOfIsColimitπ c
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
  apply preservesColimit_of_preserves_colimit_cocone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun i ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj i)) (by
      intro i j f
      change ShortComplex.homologyMap
        (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  have h : IsColimit ((Cocone.precompose e.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeInvEquiv e.symm _).symm (colimit.isColimit _)
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (S.mapHomologyIso L).symm ?_
  intro i
  dsimp only [Functor.mapCocone, c, Cocone.precompose, colimit.cocone,
    Cocone.functoriality, NatTrans.comp_app, Iso.symm_hom, ShortComplex.homologyFunctor_map]
  rw [Category.assoc]
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

/-- If colimits of shape `J` are exact in `C`, then the homology functors of homological
complexes in `C` commute with colimits of shape `J`. -/
instance HomologicalComplex.preservesColimitsOfShape_homologyFunctor
    (C : Type*) [Category* C] [Abelian C] {ι : Type*} (c : ComplexShape ι)
    (J : Type*) [Category* J] [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] (i : ι) :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor C c i) := by
  let H := HomologicalComplex.shortComplexFunctor C c i
  have : PreservesColimitsOfShape J H :=
    ⟨fun {D} ↦ ⟨fun {s} hs ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone s)
      (isColimitOfPreserves (HomologicalComplex.eval _ c (c.prev i)) hs)
      (isColimitOfPreserves (HomologicalComplex.eval _ c i) hs)
      (isColimitOfPreserves (HomologicalComplex.eval _ c (c.next i)) hs)⟩⟩⟩
  exact inferInstanceAs (PreservesColimitsOfShape J (H ⋙ ShortComplex.homologyFunctor C))
