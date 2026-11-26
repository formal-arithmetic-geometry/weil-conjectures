/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso

/-!
# Exact functors and the shift sequence of the homology of cochain complexes

A functor `F` which preserves homology commutes with the homology functors of cochain
complexes (`Functor.mapHomologicalComplexHomologyIso`). We show that these isomorphisms are
compatible with the shift sequence structure on the homology functors, i.e. with the
isomorphisms `(K⟦n⟧).homology a ≅ K.homology a'` for `n + a = a'`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

/-- The isomorphisms `H^a(F(K)) ≅ F(H^a(K))` are compatible with the isomorphisms
`H^a(K⟦n⟧) ≅ H^{a'}(K)` for `n + a = a'`. -/
lemma mapHomologicalComplexHomologyIso_hom_app_shiftIso (n a a' : ℤ) (h : n + a = a')
    (K : CochainComplex C ℤ) :
    (HomologicalComplex.homologyFunctor D (.up ℤ) a).map
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).inv.app K) ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) a).hom.app (K⟦n⟧) ≫
      F.map (((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso n a a' h).hom.app K) =
    ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso n a a' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) a').hom.app K := by
  have e₁ : ((HomologicalComplex.homologyFunctor C (.up ℤ) 0).shiftIso n a a' h).hom.app K =
      ShortComplex.homologyMap
        ((CochainComplex.shiftShortComplexFunctorIso C n a a' h).hom.app K) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app n a a' h K
  have e₂ : ((HomologicalComplex.homologyFunctor D (.up ℤ) 0).shiftIso n a a' h).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso D n a a' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app n a a' h _
  have key : (HomologicalComplex.shortComplexFunctor D (.up ℤ) a).map
        (((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).inv.app K) ≫
      F.mapShortComplex.map ((CochainComplex.shiftShortComplexFunctorIso C n a a' h).hom.app K) =
      (CochainComplex.shiftShortComplexFunctorIso D n a a' h).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
    ext <;>
      (simp only [comp_obj, mapShortComplex_obj, ShortComplex.map_X₁, ShortComplex.map_X₂,
        ShortComplex.map_X₃, ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
        HomologicalComplex.shortComplexFunctor_map_τ₁,
        HomologicalComplex.shortComplexFunctor_map_τ₂,
        HomologicalComplex.shortComplexFunctor_map_τ₃,
        mapHomologicalComplex_commShiftIso_inv_app_f, CochainComplex.shiftFunctor_obj_X',
        mapHomologicalComplex_obj_X, mapShortComplex_map_τ₁, mapShortComplex_map_τ₂,
        mapShortComplex_map_τ₃, CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₁,
        CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₂,
        CochainComplex.shiftShortComplexFunctorIso_hom_app_τ₃, HomologicalComplex.XIsoOfEq,
        eqToIso.hom, map_units_smul, eqToHom_map, Linear.comp_units_smul, smul_left_cancel_iff]
       erw [Category.id_comp])
  have hμ (L : CochainComplex C ℤ) (b : ℤ) :
      (F.mapHomologicalComplexHomologyIso (.up ℤ) b).hom.app L =
        ((L.sc b).mapHomologyIso F).hom := by
    simp only [comp_obj, mapHomologicalComplexHomologyIso,
      mapHomologicalComplexCompShortComplexFunctorIso, isoWhiskerRight_refl,
      ShortComplex.homologyFunctorIso, Iso.refl_trans, Iso.trans_hom, isoWhiskerLeft_hom,
      Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app,
      HomologicalComplex.homologyFunctorIso_hom_app, associator_inv_app, mapShortComplex_obj,
      associator_hom_app, NatIso.ofComponents_hom_app, whiskerRight_app,
      HomologicalComplex.homologyFunctorIso_inv_app, id_comp]
    erw [Category.id_comp, Category.id_comp, Functor.map_id, Category.comp_id]
  rw [hμ, hμ, e₁, e₂, ← ShortComplex.mapHomologyIso_hom_naturality, ← key,
    ShortComplex.homologyMap_comp, Category.assoc]
  rfl

end CategoryTheory.Functor
