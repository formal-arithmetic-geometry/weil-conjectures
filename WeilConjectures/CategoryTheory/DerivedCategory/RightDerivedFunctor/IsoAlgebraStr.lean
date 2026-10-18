/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraHomology

/-!
# The structure isomorphism of a right derived functor of algebras

Let `F`, `G` be exact additive endofunctors of abelian categories `C`, `D`, `L : C ⥤ D` an
additive functor and `e : L ⋙ G ≅ F ⋙ L`, transporting `L` to
`M = IsoAlgebra.mapOfNatIso e : IsoAlgebra F ⥤ IsoAlgebra G`. For an algebra `K` and an
injective resolution `I` of `K` in `IsoAlgebra F`, the `r`-th homology of `RM(K[0])` has
underlying object the `r`-th homology of the complex `L(I)`
(`CategoryTheory.Endofunctor.IsoAlgebra.homologyRightDerivedFunctorForgetIso`), and its structure
isomorphism is the map induced on homology by the structure isomorphisms
`G (L Iⁿ) ≅ L (F Iⁿ) ≅ L Iⁿ` of the terms of `M(I)`
(`CategoryTheory.Endofunctor.IsoAlgebra.str_homologyRightDerivedFunctorForgetIso`).
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {F : C ⥤ C} {G : D ⥤ D} [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {L : C ⥤ D} [L.Additive] (e : L ⋙ G ≅ F ⋙ L)
  [HasDerivedCategory (IsoAlgebra F)] [HasDerivedCategory (IsoAlgebra G)]
  [EnoughInjectives (IsoAlgebra F)] [HasKInjectiveResolutions (IsoAlgebra F)]

/-- The complex `M(I)` of algebras, for an injective resolution `I` and `M = mapOfNatIso e`. -/
noncomputable abbrev mapResolution {K : IsoAlgebra F} (I : InjectiveResolution K) :
    CochainComplex (IsoAlgebra G) ℕ :=
  ((mapOfNatIso e).mapHomologicalComplex _).obj I.cocomplex

/-- The underlying object of the `r`-th homology of `RM(K[0])`, `M = mapOfNatIso e`, is the
`r`-th homology of `M(I)` for an injective resolution `I` of `K`. -/
noncomputable def homologyRightDerivedFunctorForgetIso {K : IsoAlgebra F}
    (I : InjectiveResolution K) (r : ℕ) :
    (forget G).obj ((DerivedCategory.homologyFunctor _ r).obj
        ((mapOfNatIso e).rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj K))) ≅
      (((mapResolution e I).sc r).map (forget G)).homology :=
  (forget G).mapIso ((mapOfNatIso e).homologyRightDerivedFunctorObjSingleFunctorIso K r ≪≫
      I.isoRightDerivedObj (mapOfNatIso e) r) ≪≫
    (((mapResolution e I).sc r).mapHomologyIso (forget G)).symm

/-- **The structure isomorphism of a right derived functor of algebras.** Through
`homologyRightDerivedFunctorForgetIso`, the structure isomorphism of `Hʳ(RM(K[0]))` is the map
induced on homology by the structure isomorphisms of the terms of `M(I)`. -/
theorem str_homologyRightDerivedFunctorForgetIso {K : IsoAlgebra F}
    (I : InjectiveResolution K) (r : ℕ) :
    ((DerivedCategory.homologyFunctor _ r).obj ((mapOfNatIso e).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj K))).str.hom ≫
        (homologyRightDerivedFunctorForgetIso e I r).hom =
      G.map (homologyRightDerivedFunctorForgetIso e I r).hom ≫
        ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso G).inv ≫
        ShortComplex.homologyMap (((mapResolution e I).sc r).mapNatTrans (strNatTrans G)) := by
  have h := homologyMap_mapNatTrans_strNatTrans G ((mapResolution e I).sc r)
  have h' : ((((mapResolution e I).sc r).map (forget G)).mapHomologyIso G).inv ≫
      ShortComplex.homologyMap (((mapResolution e I).sc r).mapNatTrans (strNatTrans G)) =
      G.map (((mapResolution e I).sc r).mapHomologyIso (forget G)).hom ≫
        ((mapResolution e I).sc r).homology.str.hom ≫
          (((mapResolution e I).sc r).mapHomologyIso (forget G)).inv := by
    rw [← cancel_mono (((mapResolution e I).sc r).mapHomologyIso (forget G)).hom]
    simpa using h
  have hα := ((mapOfNatIso e).homologyRightDerivedFunctorObjSingleFunctorIso K r ≪≫
    I.isoRightDerivedObj (mapOfNatIso e) r).hom.hom.h
  simp only [Iso.trans_hom, comp_hom_f, Functor.map_comp, Category.assoc] at hα
  simp only [homologyRightDerivedFunctorForgetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Functor.map_comp, Category.assoc, h', forget_map, str_hom]
  rw [Iso.map_inv_hom_id_assoc]
  simp only [comp_hom_f, Functor.map_comp, Category.assoc]
  have hβ := hα =≫ (((mapResolution e I).sc r).mapHomologyIso (forget G)).inv
  simp only [Category.assoc] at hβ
  exact hβ.symm

end CategoryTheory.Endofunctor.IsoAlgebra
