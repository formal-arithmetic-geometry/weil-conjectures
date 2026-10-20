/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.SixFunctors.EtaleOpenTensor
import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import Sheaf.Paper.EtaleProEtaleScalarMate
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-! # Scalar extension and open-restriction exchange

Source: Stacks Project, Tag 07A7 (remark-base-change) and Tag 0E47
(remark-compose-base-change-horizontal).

The exact-localization cube argument adapts the private bounded-below cube lemmas of
`WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsPullbackSquare` to localization
of complexes at quasi-isomorphisms. The sheaf comparison calculation uses the same
uniqueness-of-left-adjoints argument as that source.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace CategoryTheory
section
private lemma square_symm {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    (a : F ⋙ G ≅ F' ⋙ G') :
    Functor.mapDerivedCategorySquareIso a.symm =
      (Functor.mapDerivedCategorySquareIso a).symm := by
  apply Iso.ext
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]

private lemma map_square_fac {C D D' E : Type*}
    [Category C] [Category D] [Category D'] [Category E]
    [Abelian C] [Abelian D] [Abelian D'] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
    [HasDerivedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
    [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
    (a : F ⋙ G ≅ F' ⋙ G')
    (aD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
      F'.mapDerivedCategory ⋙ G'.mapDerivedCategory)
    (haD : aD = (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso F' G')
    (K : CochainComplex C ℤ) :
    aD.hom.app (DerivedCategory.Q.obj K) ≫
      G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
      G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app K) := by
  subst aD
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]


private lemma path_fac {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  [Abelian A] [Abelian B] [Abelian C] [Abelian A'] [Abelian B'] [Abelian C']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  (R : A' ⥤ A) (S : B' ⥤ B) (T : C' ⥤ C)
  (F : A ⥤ B) (G : B ⥤ C) (F' : A' ⥤ B') (G' : B' ⥤ C')
  [R.Additive] [S.Additive] [T.Additive] [F.Additive] [G.Additive]
  [F'.Additive] [G'.Additive]
  [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  (aD : R.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
    F'.mapDerivedCategory ⋙ S.mapDerivedCategory)
  (bD : S.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    G'.mapDerivedCategory ⋙ T.mapDerivedCategory)
  (aH : (R.mapHomologicalComplex (.up ℤ)) ⋙ (F.mapHomologicalComplex (.up ℤ)) ⟶
    (F'.mapHomologicalComplex (.up ℤ)) ⋙ (S.mapHomologicalComplex (.up ℤ)))
  (bH : (S.mapHomologicalComplex (.up ℤ)) ⋙ (G.mapHomologicalComplex (.up ℤ)) ⟶
    (G'.mapHomologicalComplex (.up ℤ)) ⋙ (T.mapHomologicalComplex (.up ℤ)))
  (ha : ∀ K, aD.hom.app (DerivedCategory.Q.obj K) ≫
    S.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
    S.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
    F.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (aH.app K))
  (hb : ∀ K, bD.hom.app (DerivedCategory.Q.obj K) ≫
    T.mapDerivedCategory.map (G'.mapDerivedCategoryFactors.hom.app K) ≫
    T.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (bH.app K))
    (K : CochainComplex A' ℤ) :
    G.mapDerivedCategory.map (aD.hom.app (DerivedCategory.Q.obj K)) ≫
      bD.hom.app (F'.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
      T.mapDerivedCategory.map
        (G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K)) ≫
      T.mapDerivedCategory.map
        (G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      T.mapDerivedCategoryFactors.hom.app
        ((G'.mapHomologicalComplex (.up ℤ)).obj ((F'.mapHomologicalComplex (.up ℤ)).obj K)) =
    G.mapDerivedCategory.map
        (F.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K)) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map (aH.app K) ≫
          bH.app ((F'.mapHomologicalComplex (.up ℤ)).obj K)) := by
  have hn := bD.hom.naturality (F'.mapDerivedCategoryFactors.hom.app K)
  have hnat := G.mapDerivedCategoryFactors.hom.naturality (aH.app K)
  simp only [Functor.comp_map, Functor.comp_obj] at hn hnat
  rw [← reassoc_of% hn, hb]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc (aD.hom.app _), ha]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hnat]
end
section Cube
private lemma derived_cube {A B C D A' B' C' D' : Type*}
  [Category A] [Category B] [Category C]
  [Category D] [Category A'] [Category B']
  [Category C'] [Category D']
  [Abelian A] [Abelian B] [Abelian C]
  [Abelian D] [Abelian A'] [Abelian B']
  [Abelian C'] [Abelian D']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
  [HasDerivedCategory C'] [HasDerivedCategory D']
  (R : A' ⥤ A)
  (S : B' ⥤ B)
  (T : C' ⥤ C)
  (U : D' ⥤ D)
  (F : A ⥤ B)
  (G : B ⥤ C)
  (H : A ⥤ D)
  (I : D ⥤ C)
  (F' : A' ⥤ B')
  (G' : B' ⥤ C')
  (H' : A' ⥤ D')
  (I' : D' ⥤ C')
  [R.Additive] [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [S.Additive] [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [T.Additive] [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
  [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
  [I.Additive] [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
  [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
  [I'.Additive] [Limits.PreservesFiniteLimits I'] [Limits.PreservesFiniteColimits I']
  (aD : R.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
    F'.mapDerivedCategory ⋙ S.mapDerivedCategory)
  (aH : (R.mapHomologicalComplex (.up ℤ)) ⋙ (F.mapHomologicalComplex (.up ℤ)) ⟶
    (F'.mapHomologicalComplex (.up ℤ)) ⋙ (S.mapHomologicalComplex (.up ℤ)))
  (ha : ∀ K, aD.hom.app (DerivedCategory.Q.obj K) ≫
    S.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
    S.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) =
    F.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
    F.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (aH.app K))
  (bD : S.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    G'.mapDerivedCategory ⋙ T.mapDerivedCategory)
  (bH : (S.mapHomologicalComplex (.up ℤ)) ⋙ (G.mapHomologicalComplex (.up ℤ)) ⟶
    (G'.mapHomologicalComplex (.up ℤ)) ⋙ (T.mapHomologicalComplex (.up ℤ)))
  (hb : ∀ K, bD.hom.app (DerivedCategory.Q.obj K) ≫
    T.mapDerivedCategory.map (G'.mapDerivedCategoryFactors.hom.app K) ≫
    T.mapDerivedCategoryFactors.hom.app ((G'.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (bH.app K))
  (cD : R.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
    H'.mapDerivedCategory ⋙ U.mapDerivedCategory)
  (cH : (R.mapHomologicalComplex (.up ℤ)) ⋙ (H.mapHomologicalComplex (.up ℤ)) ⟶
    (H'.mapHomologicalComplex (.up ℤ)) ⋙ (U.mapHomologicalComplex (.up ℤ)))
  (hc : ∀ K, cD.hom.app (DerivedCategory.Q.obj K) ≫
    U.mapDerivedCategory.map (H'.mapDerivedCategoryFactors.hom.app K) ≫
    U.mapDerivedCategoryFactors.hom.app ((H'.mapHomologicalComplex (.up ℤ)).obj K) =
    H.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
    H.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (cH.app K))
  (dD : U.mapDerivedCategory ⋙ I.mapDerivedCategory ≅
    I'.mapDerivedCategory ⋙ T.mapDerivedCategory)
  (dH : (U.mapHomologicalComplex (.up ℤ)) ⋙ (I.mapHomologicalComplex (.up ℤ)) ⟶
    (I'.mapHomologicalComplex (.up ℤ)) ⋙ (T.mapHomologicalComplex (.up ℤ)))
  (hd : ∀ K, dD.hom.app (DerivedCategory.Q.obj K) ≫
    T.mapDerivedCategory.map (I'.mapDerivedCategoryFactors.hom.app K) ≫
    T.mapDerivedCategoryFactors.hom.app ((I'.mapHomologicalComplex (.up ℤ)).obj K) =
    I.mapDerivedCategory.map (U.mapDerivedCategoryFactors.hom.app K) ≫
    I.mapDerivedCategoryFactors.hom.app ((U.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (dH.app K))
  (tD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    H.mapDerivedCategory ⋙ I.mapDerivedCategory)
  (tH : (F.mapHomologicalComplex (.up ℤ)) ⋙ (G.mapHomologicalComplex (.up ℤ)) ⟶
    (H.mapHomologicalComplex (.up ℤ)) ⋙ (I.mapHomologicalComplex (.up ℤ)))
  (ht : ∀ K, tD.hom.app (DerivedCategory.Q.obj K) ≫
    I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
    I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (tH.app K))
  (t'D : F'.mapDerivedCategory ⋙ G'.mapDerivedCategory ≅
    H'.mapDerivedCategory ⋙ I'.mapDerivedCategory)
  (t'H : (F'.mapHomologicalComplex (.up ℤ)) ⋙ (G'.mapHomologicalComplex (.up ℤ)) ⟶
    (H'.mapHomologicalComplex (.up ℤ)) ⋙ (I'.mapHomologicalComplex (.up ℤ)))
  (ht' : ∀ K, t'D.hom.app (DerivedCategory.Q.obj K) ≫
    I'.mapDerivedCategory.map (H'.mapDerivedCategoryFactors.hom.app K) ≫
    I'.mapDerivedCategoryFactors.hom.app ((H'.mapHomologicalComplex (.up ℤ)).obj K) =
    G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
    G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map (t'H.app K))
  (hcube : ∀ K, (G.mapHomologicalComplex (.up ℤ)).map (aH.app K) ≫
    bH.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (T.mapHomologicalComplex (.up ℤ)).map (t'H.app K) =
    tH.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (I.mapHomologicalComplex (.up ℤ)).map (cH.app K) ≫
      dH.app ((H'.mapHomologicalComplex (.up ℤ)).obj K)) :
    Functor.whiskerRight aD.hom G.mapDerivedCategory ≫
      Functor.whiskerLeft F'.mapDerivedCategory bD.hom ≫
      Functor.whiskerRight t'D.hom T.mapDerivedCategory =
    Functor.whiskerLeft R.mapDerivedCategory tD.hom ≫
      Functor.whiskerRight cD.hom I.mapDerivedCategory ≫
      Functor.whiskerLeft H'.mapDerivedCategory dD.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) (fun K ↦ ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← cancel_mono (T.mapDerivedCategory.map
      (I'.mapDerivedCategory.map (H'.mapDerivedCategoryFactors.hom.app K)) ≫
    T.mapDerivedCategory.map
      (I'.mapDerivedCategoryFactors.hom.app ((H'.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    T.mapDerivedCategoryFactors.hom.app
      ((I'.mapHomologicalComplex (.up ℤ)).obj ((H'.mapHomologicalComplex (.up ℤ)).obj K)))]
  have hnat := T.mapDerivedCategoryFactors.hom.naturality (t'H.app K)
  have hnat' := tD.hom.naturality (R.mapDerivedCategoryFactors.hom.app K)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat hnat'
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    Category.assoc (t'D.hom.app _), ht' K]
  simp only [Functor.map_comp, Category.assoc]
  rw [hnat]
  slice_lhs 1 5 =>
    rw [path_fac R S T F G F' G' aD bD aH bH ha hb K]
  slice_rhs 2 6 =>
    rw [path_fac R U T H I H' I' cD dD cH dH hc hd K]
  simp only [Category.assoc]
  rw [← reassoc_of% hnat']
  slice_rhs 2 4 => rw [ht]
  simp only [Category.assoc]
  simp only [← DerivedCategory.Q.map_comp]
  rw [Category.assoc, hcube K]

end Cube
private lemma homotopy_cube {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C]
    [Category D] [Category A'] [Category B']
    [Category C'] [Category D']
    [Preadditive A] [Preadditive B] [Preadditive C]
    [Preadditive D] [Preadditive A'] [Preadditive B']
    [Preadditive C'] [Preadditive D']
    (R : A' ⥤ A) [R.Additive]
    (S : B' ⥤ B) [S.Additive]
    (T : C' ⥤ C) [T.Additive]
    (U : D' ⥤ D) [U.Additive]
    (F : A ⥤ B) [F.Additive]
    (G : B ⥤ C) [G.Additive]
    (H : A ⥤ D) [H.Additive]
    (I : D ⥤ C) [I.Additive]
    (F' : A' ⥤ B') [F'.Additive]
    (G' : B' ⥤ C') [G'.Additive]
    (H' : A' ⥤ D') [H'.Additive]
    (I' : D' ⥤ C') [I'.Additive]
    (a : R ⋙ F ⟶ F' ⋙ S)
    (b : S ⋙ G ⟶ G' ⋙ T)
    (c : R ⋙ H ⟶ H' ⋙ U)
    (d : U ⋙ I ⟶ I' ⋙ T)
    (t : F ⋙ G ⟶ H ⋙ I)
    (t' : F' ⋙ G' ⟶ H' ⋙ I')
    (hcube : ∀ L, G.map (a.app L) ≫ b.app (F'.obj L) ≫ T.map (t'.app L) =
      t.app (R.obj L) ≫ I.map (c.app L) ≫ d.app (H'.obj L))
    (K : CochainComplex A' ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex a (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex b (.up ℤ)).app ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (T.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex t' (.up ℤ)).app K) =
    (NatTrans.mapHomologicalComplex t (.up ℤ)).app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (I.mapHomologicalComplex (.up ℤ)).map ((NatTrans.mapHomologicalComplex c (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex d (.up ℤ)).app
        ((H'.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n
  exact hcube (K.X n)


private lemma derived_base_cube {A B C D A' B' C' D' : Type*}
  [Category A] [Category B] [Category C]
  [Category D] [Category A'] [Category B']
  [Category C'] [Category D']
  [Abelian A] [Abelian B] [Abelian C]
  [Abelian D] [Abelian A'] [Abelian B']
  [Abelian C'] [Abelian D']
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
  [HasDerivedCategory C'] [HasDerivedCategory D']
  (R : A' ⥤ A)
  (S : B' ⥤ B)
  (T : C' ⥤ C)
  (U : D' ⥤ D)
  (F : A ⥤ B)
  (G : B ⥤ C)
  (H : A ⥤ D)
  (I : D ⥤ C)
  (F' : A' ⥤ B')
  (G' : B' ⥤ C')
  (H' : A' ⥤ D')
  (I' : D' ⥤ C')
  [R.Additive] [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
  [S.Additive] [Limits.PreservesFiniteLimits S] [Limits.PreservesFiniteColimits S]
  [T.Additive] [Limits.PreservesFiniteLimits T] [Limits.PreservesFiniteColimits T]
  [U.Additive] [Limits.PreservesFiniteLimits U] [Limits.PreservesFiniteColimits U]
  [F.Additive] [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
  [G.Additive] [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
  [H.Additive] [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
  [I.Additive] [Limits.PreservesFiniteLimits I] [Limits.PreservesFiniteColimits I]
  [F'.Additive] [Limits.PreservesFiniteLimits F'] [Limits.PreservesFiniteColimits F']
  [G'.Additive] [Limits.PreservesFiniteLimits G'] [Limits.PreservesFiniteColimits G']
  [H'.Additive] [Limits.PreservesFiniteLimits H'] [Limits.PreservesFiniteColimits H']
  [I'.Additive] [Limits.PreservesFiniteLimits I'] [Limits.PreservesFiniteColimits I']
  (a : R ⋙ F ≅ F' ⋙ S)
  (b : S ⋙ G ≅ G' ⋙ T)
  (c : R ⋙ H ≅ H' ⋙ U)
  (d : U ⋙ I ≅ I' ⋙ T)
  (t : F ⋙ G ⟶ H ⋙ I)
  (t' : F' ⋙ G' ⟶ H' ⋙ I')
  (aD : R.mapDerivedCategory ⋙ F.mapDerivedCategory ≅
    F'.mapDerivedCategory ⋙ S.mapDerivedCategory)
  (bD : S.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    G'.mapDerivedCategory ⋙ T.mapDerivedCategory)
  (cD : R.mapDerivedCategory ⋙ H.mapDerivedCategory ≅
    H'.mapDerivedCategory ⋙ U.mapDerivedCategory)
  (dD : U.mapDerivedCategory ⋙ I.mapDerivedCategory ≅
    I'.mapDerivedCategory ⋙ T.mapDerivedCategory)
  (tD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅
    H.mapDerivedCategory ⋙ I.mapDerivedCategory)
  (t'D : F'.mapDerivedCategory ⋙ G'.mapDerivedCategory ≅
    H'.mapDerivedCategory ⋙ I'.mapDerivedCategory)
  (haD : aD = (Functor.mapDerivedCategoryCompIso R F).symm ≪≫
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso F' S)
  (hbD : bD = (Functor.mapDerivedCategoryCompIso S G).symm ≪≫
    Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryCompIso G' T)
  (hcD : cD = (Functor.mapDerivedCategoryCompIso R H).symm ≪≫
    Functor.mapDerivedCategoryNatIso c ≪≫ Functor.mapDerivedCategoryCompIso H' U)
  (hdD : dD = (Functor.mapDerivedCategoryCompIso U I).symm ≪≫
    Functor.mapDerivedCategoryNatIso d ≪≫ Functor.mapDerivedCategoryCompIso I' T)
  (ht : ∀ K, tD.hom.app (DerivedCategory.Q.obj K) ≫
    I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
    I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t (.up ℤ)).app K))
  (ht' : ∀ K, t'D.hom.app (DerivedCategory.Q.obj K) ≫
    I'.mapDerivedCategory.map (H'.mapDerivedCategoryFactors.hom.app K) ≫
    I'.mapDerivedCategoryFactors.hom.app ((H'.mapHomologicalComplex (.up ℤ)).obj K) =
    G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactors.hom.app K) ≫
    G'.mapDerivedCategoryFactors.hom.app ((F'.mapHomologicalComplex (.up ℤ)).obj K) ≫
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex t' (.up ℤ)).app K))
  (hcube : ∀ L, G.map (a.hom.app L) ≫ b.hom.app (F'.obj L) ≫ T.map (t'.app L) =
    t.app (R.obj L) ≫ I.map (c.hom.app L) ≫ d.hom.app (H'.obj L)) :
    Functor.whiskerRight aD.hom G.mapDerivedCategory ≫
      Functor.whiskerLeft F'.mapDerivedCategory bD.hom ≫
      Functor.whiskerRight t'D.hom T.mapDerivedCategory =
    Functor.whiskerLeft R.mapDerivedCategory tD.hom ≫
      Functor.whiskerRight cD.hom I.mapDerivedCategory ≫
      Functor.whiskerLeft H'.mapDerivedCategory dD.hom := by
  apply derived_cube R S T U F G H I F' G' H' I'
    (aD := aD) (bD := bD) (cD := cD) (dD := dD) (tD := tD) (t'D := t'D)
    (aH := NatTrans.mapHomologicalComplex a.hom (.up ℤ))
    (bH := NatTrans.mapHomologicalComplex b.hom (.up ℤ))
    (cH := NatTrans.mapHomologicalComplex c.hom (.up ℤ))
    (dH := NatTrans.mapHomologicalComplex d.hom (.up ℤ))
    (tH := NatTrans.mapHomologicalComplex t (.up ℤ))
    (t'H := NatTrans.mapHomologicalComplex t' (.up ℤ))
  · intro K
    exact map_square_fac R F F' S a aD haD K
  · intro K
    exact map_square_fac S G G' T b bD hbD K
  · intro K
    exact map_square_fac R H H' U c cD hcD K
  · intro K
    exact map_square_fac U I I' T d dD hdD K
  · intro K
    exact ht K
  · intro K
    exact ht' K
  · intro K
    exact homotopy_cube R S T U F G H I F' G' H' I'
      a.hom b.hom c.hom d.hom t t' hcube K

end CategoryTheory

private theorem scalar_path
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C]
    [Category A'] [Category B'] [Category C']
    {ta : A ⥤ A'} {ra : A' ⥤ A} {tb : B ⥤ B'} {rb : B' ⥤ B}
    {tc : C ⥤ C'} {rc : C' ⥤ C}
    (aa : ta ⊣ ra) (ab : tb ⊣ rb) (ac : tc ⊣ rc)
    {f : A ⥤ B} {g : B ⥤ C} {f' : A' ⥤ B'} {g' : B' ⥤ C'}
    (ef : ra ⋙ f ⟶ f' ⋙ rb) (eg : rb ⋙ g ⟶ g' ⋙ rc)
    (mf : f ⋙ tb ⟶ ta ⋙ f') (mg : g ⋙ tc ⟶ tb ⋙ g')
    (hf : ∀ K, f.map (aa.unit.app K) ≫ ef.app (ta.obj K) =
      ab.unit.app (f.obj K) ≫ rb.map (mf.app K))
    (hg : ∀ K, g.map (ab.unit.app K) ≫ eg.app (tb.obj K) =
      ac.unit.app (g.obj K) ≫ rc.map (mg.app K)) (K : A) :
    ac.unit.app (g.obj (f.obj K)) ≫ rc.map
        (mg.app (f.obj K) ≫ g'.map (mf.app K)) =
      g.map (f.map (aa.unit.app K)) ≫ g.map (ef.app (ta.obj K)) ≫
        eg.app (f'.obj (ta.obj K)) := by
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← hg]
  have hn := eg.naturality (mf.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← g.map_comp, ← hf, g.map_comp]

private theorem scalar_cube
    {ZA WA VA UA ZB WB VB UB : Type*}
    [Category ZA] [Category WA] [Category VA] [Category UA]
    [Category ZB] [Category WB] [Category VB] [Category UB]
    {tz : ZA ⥤ ZB} {rz : ZB ⥤ ZA} {tw : WA ⥤ WB} {rw : WB ⥤ WA}
    {tv : VA ⥤ VB} {rv : VB ⥤ VA} {tu : UA ⥤ UB} {ru : UB ⥤ UA}
    (az : tz ⊣ rz) (aw : tw ⊣ rw) (av : tv ⊣ rv) (au : tu ⊣ ru)
    {f : ZA ⥤ WA} {g : WA ⥤ UA} {h : ZA ⥤ VA} {j : VA ⥤ UA}
    {f' : ZB ⥤ WB} {g' : WB ⥤ UB} {h' : ZB ⥤ VB} {j' : VB ⥤ UB}
    (ef : rz ⋙ f ⟶ f' ⋙ rw) (eg : rw ⋙ g ⟶ g' ⋙ ru)
    (eh : rz ⋙ h ⟶ h' ⋙ rv) (ej : rv ⋙ j ⟶ j' ⋙ ru)
    (mf : f ⋙ tw ⟶ tz ⋙ f') (mg : g ⋙ tu ⟶ tw ⋙ g')
    (mh : h ⋙ tv ⟶ tz ⋙ h') (mj : j ⋙ tu ⟶ tv ⋙ j')
    (hf : ∀ K, f.map (az.unit.app K) ≫ ef.app (tz.obj K) =
      aw.unit.app (f.obj K) ≫ rw.map (mf.app K))
    (hg : ∀ K, g.map (aw.unit.app K) ≫ eg.app (tw.obj K) =
      au.unit.app (g.obj K) ≫ ru.map (mg.app K))
    (hh : ∀ K, h.map (az.unit.app K) ≫ eh.app (tz.obj K) =
      av.unit.app (h.obj K) ≫ rv.map (mh.app K))
    (hj : ∀ K, j.map (av.unit.app K) ≫ ej.app (tv.obj K) =
      au.unit.app (j.obj K) ≫ ru.map (mj.app K))
    (c : f ⋙ g ⟶ h ⋙ j) (c' : f' ⋙ g' ⟶ h' ⋙ j')
    (hc : ∀ L, g.map (ef.app L) ≫ eg.app (f'.obj L) ≫ ru.map (c'.app L) =
      c.app (rz.obj L) ≫ j.map (eh.app L) ≫ ej.app (h'.obj L)) (K : ZA) :
    tu.map (c.app K) ≫ mj.app (h.obj K) ≫ j'.map (mh.app K) =
      mg.app (f.obj K) ≫ g'.map (mf.app K) ≫ c'.app (tz.obj K) := by
  apply (au.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  have hu := au.unit.naturality (c.app K)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← hu]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc]
  have hp := scalar_path az av au eh ej mh mj hh hj K
  have hq := scalar_path az aw au ef eg mf mg hf hg K
  simp only [Functor.map_comp] at hp hq
  rw [hp, reassoc_of% hq]
  have hn := c.naturality (az.unit.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [← reassoc_of% hn, ← hc]


private theorem exchange_cancel {C D : Type*} [Category C] [Category D]
    {A B X Y : D} {P Q : C} (i : A ≅ B) (j : P ≅ Q) (F : C ⥤ D)
    (f : B ⟶ X) (g : X ⟶ F.obj Q) (h : A ⟶ Y) (q : Y ⟶ F.obj P)
    (e : i.hom ≫ f ≫ g = h ≫ q ≫ F.map j.hom) :
    f ≫ g ≫ F.map j.inv = i.inv ≫ h ≫ q := by
  have hh := congrArg (fun z ↦ i.inv ≫ z ≫ F.map j.inv) e
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp,
    Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id] using hh

namespace AlgebraicGeometry.Etale

/-- Cache the exact inverse-image functor and its structural instances once for each
scheme morphism, rather than resynthesizing them at every use in the cube. -/
private abbrev exactPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X :=
  D((f)^*[ModuleCat.{u + 1} A])


private lemma conjugate_unique {C D : Type*} [Category* C] [Category* D]
    {F F' : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) (b : F' ⊣ G) :
    conjugateEquiv b a (a.leftAdjointUniq b).hom = 𝟙 G := by
  simp [Adjunction.leftAdjointUniq]

private lemma conjugate_assoc_inv {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : B ⥤ C} {R₂ : C ⥤ B}
    {L₃ : C ⥤ D} {R₃ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₁ L₂ L₃).inv = (Functor.associator R₃ R₂ R₁).inv := by
  apply (cancel_epi (Functor.associator R₃ R₂ R₁).hom).mp
  rw [← conjugateEquiv_associator_hom a b c, conjugateEquiv_comp]
  simp only [Iso.inv_hom_id]
  rw [conjugateEquiv_associator_hom]
  simp


private lemma coefficient_comp
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) :
    Functor.isoWhiskerLeft (Sheaf.restrictScalars S.smallEtaleTopology φ)
        (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (upperStarRestrictScalarsIsoSheaf φ p) (h)^*[ModuleCat.{u + 1} Λ] ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (p)^*[ModuleCat.{u + 1} Λ'] (upperStarRestrictScalarsIsoSheaf φ h) ≪≫
      (Functor.associator _ _ _).symm =
    upperStarRestrictScalarsIsoSheaf φ d ≪≫
      Functor.isoWhiskerRight (upperStarComp (ModuleCat.{u + 1} Λ') h p d hd)
        (Sheaf.restrictScalars Y.smallEtaleTopology φ) := by
  have := (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).isRightAdjoint
  let aS := Sheaf.restrictCoextendScalarsAdj S.smallEtaleTopology φ
  let aX := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let aY := Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h
  let f := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) d
  let b' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p
  let c' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') h
  let f' := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') d
  apply Iso.ext
  apply (conjugateEquiv ((b'.comp c').comp aY) (aS.comp f)).injective
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _ (aS.comp (b.comp c)),
    ← conjugateEquiv_comp _ ((aS.comp b).comp c),
    ← conjugateEquiv_comp _ ((b'.comp aX).comp c),
    ← conjugateEquiv_comp _ (b'.comp (aX.comp c)),
    ← conjugateEquiv_comp _ (b'.comp (c'.comp aY)),
    ← conjugateEquiv_comp _ (f'.comp aY)]
  rw [conjugate_assoc_inv, conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, conjugate_assoc_inv, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight]
  have hp := conjugate_unique (aS.comp b) (b'.comp aX)
  have hh := conjugate_unique (aX.comp c) (c'.comp aY)
  have hd' := conjugate_unique (aS.comp f) (f'.comp aY)
  simp only [aS, aX, aY, b, c, f, b', c', f', upperStarRestrictScalarsIsoSheaf] at hp hh hd' ⊢
  erw [hp, hh, hd']
  simp only [upperStarComp, Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv,
    Iso.symm_inv, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext F
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.associator_hom_app, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id]
  rfl

private lemma coefficient_comp_app
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S Y : Scheme.{u}} (h : Y ⟶ X) (p : X ⟶ S) (d : Y ⟶ S)
    (hd : d = h ≫ p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (upperStarComp (ModuleCat.{u + 1} Λ) h p d hd).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) =
    (upperStarRestrictScalarsIsoSheaf φ d).hom.app L ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((upperStarComp (ModuleCat.{u + 1} Λ') h p d hd).hom.app L) := by
  have key := congr_app (congrArg Iso.hom (coefficient_comp φ h p d hd)) L
  simpa using key

private lemma coefficient_square
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p) (L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (h)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ p).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ h).hom.app ((p)^*[ModuleCat.{u + 1} Λ'].obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).map
        ((squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L) ≫
      (e)^*[ModuleCat.{u + 1} Λ].map ((upperStarRestrictScalarsIsoSheaf φ g).hom.app L) ≫
      (upperStarRestrictScalarsIsoSheaf φ e).hom.app ((g)^*[ModuleCat.{u + 1} Λ'].obj L) := by
  rw [← cancel_epi ((upperStarComp (ModuleCat.{u + 1} Λ) h p (e ≫ g) sq.w).hom.app
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj L))]
  simp only [squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (coefficient_comp_app φ h p (e ≫ g) sq.w L),
    ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (coefficient_comp_app φ e g (e ≫ g) rfl L).symm

private def exactRestrictScalarsIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)

private theorem exactRestriction_cube
    {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}
    (sq : CommSq e h g p)
    (L : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    ((exactPullback Λ h)).map
        ((exactRestrictScalarsIso φ p).hom.app L) ≫
      (exactRestrictScalarsIso φ h).hom.app
        ((D((p)^*[ModuleCat.{u + 1} Λ'])).obj L) ≫
      (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.map
        ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom.app L) =
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
        ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategory.obj L) ≫
      ((exactPullback Λ e)).map
        ((exactRestrictScalarsIso φ g).hom.app L) ≫
      (exactRestrictScalarsIso φ e).hom.app
        ((D((g)^*[ModuleCat.{u + 1} Λ'])).obj L) := by
  have key := CategoryTheory.derived_base_cube
    (R := Sheaf.restrictScalars S.smallEtaleTopology φ)
    (S := Sheaf.restrictScalars X.smallEtaleTopology φ)
    (T := Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (U := Sheaf.restrictScalars T.smallEtaleTopology φ)
    (F := (p)^*[ModuleCat.{u + 1} Λ])
    (G := (h)^*[ModuleCat.{u + 1} Λ])
    (H := (g)^*[ModuleCat.{u + 1} Λ])
    (I := (e)^*[ModuleCat.{u + 1} Λ])
    (F' := (p)^*[ModuleCat.{u + 1} Λ'])
    (G' := (h)^*[ModuleCat.{u + 1} Λ'])
    (H' := (g)^*[ModuleCat.{u + 1} Λ'])
    (I' := (e)^*[ModuleCat.{u + 1} Λ'])
    (a := upperStarRestrictScalarsIsoSheaf φ p)
    (aD := exactRestrictScalarsIso φ p)
    (haD := rfl)
    (b := upperStarRestrictScalarsIsoSheaf φ h)
    (bD := exactRestrictScalarsIso φ h)
    (hbD := rfl)
    (c := upperStarRestrictScalarsIsoSheaf φ g)
    (cD := exactRestrictScalarsIso φ g)
    (hcD := rfl)
    (d := upperStarRestrictScalarsIsoSheaf φ e)
    (dD := exactRestrictScalarsIso φ e)
    (hdD := rfl)
    (t := (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom)
    (tD := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq)
    (ht := by
      intro K
      exact CategoryTheory.map_square_fac _ _ _ _
        (squareUpperStarIso (ModuleCat.{u + 1} Λ) sq) _ rfl K)
    (t' := (squareUpperStarIso (ModuleCat.{u + 1} Λ') sq).hom)
    (t'D := exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} Λ') sq)
    (ht' := by
      intro K
      exact CategoryTheory.map_square_fac _ _ _ _
        (squareUpperStarIso (ModuleCat.{u + 1} Λ') sq) _ rfl K)
    (hcube := coefficient_square φ sq)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] using congr_app key L


private theorem coefficient_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ A) (adjA : Q ⊣ P)
    (P' : C ⥤ D) (Q' : D ⥤ C) (adjB : Q' ⊣ P')
    (S : B ⥤ D) (R : D ⥤ B) (adjX : S ⊣ R)
    (S' : A ⥤ C) (R' : C ⥤ A) (adjT : S' ⊣ R')
    (e : R ⋙ Q ≅ Q' ⋙ R')
    (hk : IsIso (((mateEquiv adjX adjT).symm
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans)) (K : A)
    (c : S.obj (P.obj K) ⟶ P'.obj (S'.obj K))
    (hc : Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) ≫
      R'.map (Q'.map c ≫ adjB.counit.app (S'.obj K)) =
        adjA.counit.app K ≫ adjT.unit.app K) :
    Q'.map c ≫ adjB.counit.app (S'.obj K) =
      (asIso (((mateEquiv adjX adjT).symm
        (TwoSquare.mk _ _ _ _ e.hom)).natTrans)).inv.app (P.obj K) ≫
        S'.map (adjA.counit.app K) := by
  let k := ((mateEquiv adjX adjT).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans
  have : IsIso k := hk
  change _ = (asIso k).inv.app (P.obj K) ≫ _
  apply (cancel_epi ((asIso k).hom.app (P.obj K))).mp
  rw [Iso.hom_inv_id_app_assoc]
  apply (adjT.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, asIso_hom, R'.map_comp, ← Category.assoc]
  have hu := unit_mateEquiv_symm adjX adjT (TwoSquare.mk _ _ _ _ e.hom) (P.obj K)
  change Q.map (adjX.unit.app (P.obj K)) ≫ e.hom.app (S.obj (P.obj K)) =
    adjT.unit.app (Q.obj (P.obj K)) ≫ R'.map (k.app (P.obj K)) at hu
  rw [← hu]
  simpa only [R'.map_comp, Category.assoc, Functor.comp_map, Functor.id_map,
    Functor.comp_obj, Functor.id_obj] using
    hc.trans (adjT.unit.naturality (adjA.counit.app K))

private theorem inverse_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {U : B ⥤ A} {M : C ⥤ D} {V : D ⥤ C}
    (a : L ⊣ U) (b : M ⊣ V)
    {G G' : A ⥤ C} {H H' : B ⥤ D}
    (x : TwoSquare U H G V) (e : G ≅ G') (f : H ≅ H') :
    ((mateEquiv a b).symm
      (TwoSquare.mk U H' G' V
        (Functor.whiskerLeft U e.inv ≫ x.natTrans ≫ Functor.whiskerRight f.hom V))).natTrans =
      Functor.whiskerRight e.inv M ≫ ((mateEquiv a b).symm x).natTrans ≫
        Functor.whiskerLeft L f.hom := by
  ext z
  simp only [mateEquiv_symm_apply, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
    Category.assoc]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [Category.id_comp]
  have he := e.inv.naturality (a.unit.app z)
  dsimp only [Functor.comp_obj, Functor.id_obj] at he
  rw [← M.map_comp_assoc, he, M.map_comp]
  simp only [Category.assoc]
  have hf := b.counit.naturality (f.hom.app (L.obj z))
  dsimp only [Functor.comp_map, Functor.id_map] at hf
  erw [Category.comp_id]
  erw [Category.id_comp]
  rw [hf]

private theorem exactAdj_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso _ (.up ℤ))
  intro K
  change (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      (DerivedCategory.Qh.obj K) =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).unit.app
      (DerivedCategory.Qh.obj K) ≫ R((f)_*[ModuleCat.{u + 1} A]).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).hom.app _)
  apply (cancel_mono (R((f)_*[ModuleCat.{u + 1} A]).map
    ((f)^*[ModuleCat.{u + 1} A].mapDerivedCategoryFactorsh.hom.app K))).mp
  rw [Category.assoc, ← Functor.map_comp]
  have he := congr_app
    ((f)^*[ModuleCat.{u + 1} A].leftDerivedFunctorIsoMapDerivedCategory_hom_fac) K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at he
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
  rw [he]
  have h1 := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory
    (.up ℤ) |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      (f)^*[ModuleCat.{u + 1} A].mapDerivedCategoryFactorsh.hom
      (f)_*[ModuleCat.{u + 1} A].rightDerivedFunctorUnit K
  have h2 := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).mapHomotopyCategory
    (.up ℤ) |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      (f)^*[ModuleCat.{u + 1} A].leftDerivedFunctorCounit
      (f)_*[ModuleCat.{u + 1} A].rightDerivedFunctorUnit K
  exact h1.trans h2.symm

@[irreducible] private def exactScalarPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exactPullback A f) ⋙ scalarExtension φ X ≅
      scalarExtension φ Y ⋙ (exactPullback B f) :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _ ≪≫
    (ProEtale.scalarPullbackEtaleIso φ f).symm ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)

private theorem exactScalarPullback_hom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (q : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (exactScalarPullback q f).hom =
      ((mateEquiv
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q))
        (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q))).symm
        (TwoSquare.mk _ _ _ _
          (exactRestrictScalarsIso q f).hom)).natTrans := by
  unfold exactScalarPullback exactRestrictScalarsIso
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso q f).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f
  have h := inverse_mate_transport a b x e e'
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf q f)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars Y.smallEtaleTopology q)
          e.inv ≫ x.natTrans ≫
          Functor.whiskerRight e'.hom
            (Sheaf.derivedRestrictScalars X.smallEtaleTopology q)) := by
    ext M
    dsimp only [x, e, e', scalarRestrictionPullbackIso, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
      ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
  rw [heq, h]
  rfl

private theorem finiteCoefficient_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A X) :
    L((f)^*[ModuleCat.{u + 1} B]).map (finiteCoefficientDirectImageMap φ f K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
        ((scalarExtension φ X).obj K) =
    (ProEtale.scalarPullbackEtaleIso φ f).hom.app (R((f)_*[ModuleCat.{u + 1} A]).obj K) ≫
      (scalarExtension φ X).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K) := by
  exact coefficient_counit _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f) _ _
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)) _ _
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (finiteCoefficientRestrictionPullback φ f) (ProEtale.scalarPullbackReverse_isIso φ f).2
    K (finiteCoefficientDirectImageMap φ f K)
    (finiteCoefficientDirectImageMap_existsUnique φ f K).choose_spec.1

private theorem exactCoefficient_counit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A X) :
    (exactPullback B f).map (finiteCoefficientDirectImageMap φ f K) ≫
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).counit.app
        ((scalarExtension φ X).obj K) =
    (exactScalarPullback φ f).inv.app (R((f)_*[ModuleCat.{u + 1} A]).obj K) ≫
      (scalarExtension φ X).map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K) := by
  rw [exactAdj_eq, exactAdj_eq]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).inv.naturality
    (finiteCoefficientDirectImageMap φ f K)
  rw [reassoc_of% hn, finiteCoefficient_counit φ f K]
  simp only [exactScalarPullback, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc,
    ← Functor.map_comp]
  rw [Iso.hom_inv_id_app_assoc]

private theorem exactScalarPullback_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A Y) :
    (exactPullback A f).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)).unit.app K) ≫
      (exactRestrictScalarsIso φ f).hom.app ((scalarExtension φ Y).obj K) =
    (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).unit.app
          ((exactPullback A f).obj K) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((exactScalarPullback φ f).hom.app K) := by
  rw [exactScalarPullback_hom]
  exact unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (TwoSquare.mk _ _ _ _ (exactRestrictScalarsIso φ f).hom) K

private theorem sheafComparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStarRestrictScalarsIsoSheaf φ f = upperStarRestrictScalarsIso φ f := by
  apply Iso.ext
  apply (conjugateEquiv
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ))
    ((Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))).injective
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  dsimp only [upperStarRestrictScalarsIsoSheaf, Adjunction.leftAdjointUniq]
  erw [Equiv.apply_symm_apply]
  rfl

private theorem openComparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j := by
  rw [sheafComparison_eq]
  have hsite : (mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j)
      (TwoSquare.mk (Sheaf.restrictScalars Y.smallEtaleTopology φ)
        (openImmersionRestriction (ModuleCat.{u + 1} B) j)
        (openImmersionRestriction (ModuleCat.{u + 1} A) j)
        (Sheaf.restrictScalars X.smallEtaleTopology φ)
        (𝟙 _))).natTrans = (lowerStarCompRestrictScalarsIso φ j).hom := by
    ext F b : 5
    simp only [mateEquiv, Equiv.coe_fn_mk, openImmersionRestrictionLowerStarAdjunction,
      localizationRestrictionLowerStarAdjunction, Functor.comp_obj, Functor.id_obj,
      Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft,
      Functor.whiskeringLeft_obj_obj, Adjunction.op_unit, Adjunction.op_counit,
      NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.leftUnitor_hom_app,
      Category.comp_id, Category.id_comp, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc, Functor.leftUnitor_inv_app, Functor.op_obj, NatTrans.op_app,
      lowerStarCompRestrictScalarsIso, Iso.refl_hom, NatTrans.id_app]
    simp only [CategoryTheory.Functor.map_id]
    change (ModuleCat.restrictScalars φ).map (F.obj.map _) ≫ 𝟙 _ ≫
      (ModuleCat.restrictScalars φ).map (F.obj.map _) = 𝟙 _
    rw [Category.id_comp, ← Functor.map_comp, ← Functor.map_comp]
    simp only [Functor.op_map, NatTrans.op_app, Quiver.Hom.unop_op,
      Functor.op_obj, Opposite.unop_op]
    rw [← op_comp, Adjunction.right_triangle_components
      (MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance trivial)]
    erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  let w := TwoSquare.mk (Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (openImmersionRestriction (ModuleCat.{u + 1} B) j)
    (openImmersionRestriction (ModuleCat.{u + 1} A) j)
    (Sheaf.restrictScalars X.smallEtaleTopology φ) (𝟙 _)
  have hb := mateEquiv_leftAdjointUniq
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
    (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j) w
  have hs : mateEquiv
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j) w =
      TwoSquare.mk _ _ _ _ (lowerStarCompRestrictScalarsIso φ j).hom := by
    apply TwoSquare.ext
    intro M
    exact congr_app hsite M
  rw [hs] at hb
  have he := congrArg
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)).symm hb
  simp only [Equiv.symm_apply_apply] at he
  have he' := congrArg TwoSquare.natTrans he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  have hm := congr_app he' M
  dsimp only [openRestrictScalarsIso, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.ofComponents_inv_app, Iso.refl_inv]
  erw [Category.comp_id]
  exact hm

set_option backward.isDefEq.respectTransparency true

private theorem exactScalarPullback_open_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    exactScalarPullback φ j = openScalarRestriction φ j := by
  have he : exactRestrictScalarsIso φ j = (openDerivedRestrictScalarsIso φ j).symm := by
    unfold exactRestrictScalarsIso openDerivedRestrictScalarsIso
    rw [← openComparison_eq, CategoryTheory.square_symm]
  apply Iso.ext
  rw [exactScalarPullback_hom]
  change ((mateEquiv
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))).symm
      (TwoSquare.mk _ _ _ _ (exactRestrictScalarsIso φ j).hom)).natTrans = _
  rw [he]
  rfl

/-- Changing constant coefficients commutes with exchange along an open base map.
The comparison on each horizontal inverse image is the specified scalar mate.
Source: Stacks Project, sites-cohomology.tex, Tags 07A7 and 0E47
(blueprint: lem-sp-open-restriction-scalar-exchange).

Proof: the restriction-of-scalars comparison commutes with the square of inverse
images: identify both composites with inverse image along the common composite
scheme morphism, and use uniqueness of the left adjoints of the sectionwise
coextension/direct-image functors. Descend that identity through exact localization.
Take mates under the scalar adjunctions. The resulting scalar/pullback cube has
horizontal edges openScalarRestriction and vertical edges the inverse scalar mates
of finiteCoefficientRestrictionPullback. Those vertical edges are invertible by
scalarPullbackReverse_isIso. Taking geometric mates of the cube gives the assertion:
finiteCoefficientDirectImageMap is precisely the mate of the inverse vertical edge
by its defining counit equation and uniqueness. Mate pasting gives the two paths
shown here, without inverting either direct-image coefficient map. This argument
uses no boundedness, properness, cartesianness, or flatness assumption. -/
theorem openRestriction_scalar_exchange
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V W Z : Scheme.{u}}
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i]
    (sq : CommSq k r p i) (M : DerivedCategoryModule A V) :
    D((i)^*[ModuleCat.{u + 1} B]).map (finiteCoefficientDirectImageMap φ p M) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app
        ((scalarExtension φ V).obj M) ≫
      R((r)_*[ModuleCat.{u + 1} B]).map ((openScalarRestriction φ k).inv.app M) =
    (openScalarRestriction φ i).inv.app (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (scalarExtension φ W).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M) ≫
      finiteCoefficientDirectImageMap φ r (D((k)^*[ModuleCat.{u + 1} A]).obj M) := by
  change (exactPullback B i).map (finiteCoefficientDirectImageMap φ p M) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq).app
        ((scalarExtension φ V).obj M) ≫
      R((r)_*[ModuleCat.{u + 1} B]).map ((openScalarRestriction φ k).inv.app M) =
    (openScalarRestriction φ i).inv.app (R((p)_*[ModuleCat.{u + 1} A]).obj M) ≫
      (scalarExtension φ W).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app M) ≫
      finiteCoefficientDirectImageMap φ r ((exactPullback A k).obj M)
  let qp : R((p)_*[ModuleCat.{u + 1} A]) ⋙ scalarExtension φ Z ⟶
      scalarExtension φ V ⋙ R((p)_*[ModuleCat.{u + 1} B]) :=
    { app := finiteCoefficientDirectImageMap φ p
      naturality := by
        intro K L f
        exact finiteCoefficientDirectImageMap_naturality φ p f }
  let qr : R((r)_*[ModuleCat.{u + 1} A]) ⋙ scalarExtension φ W ⟶
      scalarExtension φ U ⋙ R((r)_*[ModuleCat.{u + 1} B]) :=
    { app := finiteCoefficientDirectImageMap φ r
      naturality := by
        intro K L f
        exact finiteCoefficientDirectImageMap_naturality φ r f }
  have hc (K : DerivedCategoryModule A Z) :
      (scalarExtension φ U).map
          ((exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K) ≫
        (openScalarRestriction φ k).hom.app ((exactPullback A p).obj K) ≫
        (exactPullback B k).map ((exactScalarPullback φ p).hom.app K) =
      (exactScalarPullback φ r).hom.app ((exactPullback A i).obj K) ≫
        (exactPullback B r).map ((openScalarRestriction φ i).hom.app K) ≫
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom.app
          ((scalarExtension φ Z).obj K) := by
    rw [← exactScalarPullback_open_eq φ i, ← exactScalarPullback_open_eq φ k]
    let fiA : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A W :=
      (exactPullback A i)
    let frA : DerivedCategoryModule A W ⥤ DerivedCategoryModule A U :=
      (exactPullback A r)
    let fpA : DerivedCategoryModule A Z ⥤ DerivedCategoryModule A V :=
      (exactPullback A p)
    let fkA : DerivedCategoryModule A V ⥤ DerivedCategoryModule A U :=
      (exactPullback A k)
    let fiB : DerivedCategoryModule B Z ⥤ DerivedCategoryModule B W :=
      (exactPullback B i)
    let frB : DerivedCategoryModule B W ⥤ DerivedCategoryModule B U :=
      (exactPullback B r)
    let fpB : DerivedCategoryModule B Z ⥤ DerivedCategoryModule B V :=
      (exactPullback B p)
    let fkB : DerivedCategoryModule B V ⥤ DerivedCategoryModule B U :=
      (exactPullback B k)
    exact scalar_cube
      (ZA := DerivedCategoryModule A Z) (WA := DerivedCategoryModule A W)
      (VA := DerivedCategoryModule A V) (UA := DerivedCategoryModule A U)
      (ZB := DerivedCategoryModule B Z) (WB := DerivedCategoryModule B W)
      (VB := DerivedCategoryModule B V) (UB := DerivedCategoryModule B U)
      (tz := scalarExtension φ Z) (tw := scalarExtension φ W)
      (tv := scalarExtension φ V) (tu := scalarExtension φ U)
      (rz := Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
      (rw := Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
      (rv := Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
      (ru := Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
      (f := fiA) (g := frA)
      (h := fpA) (j := fkA)
      (f' := fiB) (g' := frB)
      (h' := fpB) (j' := fkB)
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))
      (exactRestrictScalarsIso φ i).hom (exactRestrictScalarsIso φ r).hom
      (exactRestrictScalarsIso φ p).hom (exactRestrictScalarsIso φ k).hom
      (exactScalarPullback φ i).hom (exactScalarPullback φ r).hom
      (exactScalarPullback φ p).hom (exactScalarPullback φ k).hom
      (exactScalarPullback_unit φ i) (exactScalarPullback_unit φ r)
      (exactScalarPullback_unit φ p) (exactScalarPullback_unit φ k)
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom
      (exactRestriction_cube φ sq) K
  have h := Adjunction.coefficient_exchange_of_counit
    (C₁ := DerivedCategoryModule A Z) (C₂ := DerivedCategoryModule A V)
    (C₃ := DerivedCategoryModule A W) (C₄ := DerivedCategoryModule A U)
    (D₁ := DerivedCategoryModule B Z) (D₂ := DerivedCategoryModule B V)
    (D₃ := DerivedCategoryModule B W) (D₄ := DerivedCategoryModule B U)
    (U := (exactPullback A p)) (R := R((p)_*[ModuleCat.{u + 1} A]))
    (V := (exactPullback A r)) (S := R((r)_*[ModuleCat.{u + 1} A]))
    (Ue := (exactPullback B p)) (Re := R((p)_*[ModuleCat.{u + 1} B]))
    (Ve := (exactPullback B r)) (Se := R((r)_*[ModuleCat.{u + 1} B]))
    (G := (exactPullback A i)) (H := (exactPullback A k))
    (Ge := (exactPullback B i)) (He := (exactPullback B k))
    (T₁ := scalarExtension φ Z) (T₂ := scalarExtension φ V)
    (T₃ := scalarExtension φ W) (T₄ := scalarExtension φ U)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) r)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) r)
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom
    (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} B) sq).hom
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq)
    (mateEquiv_counit _ _ _) (mateEquiv_counit _ _ _)
    (exactScalarPullback φ p) (exactScalarPullback φ r)
    (openScalarRestriction φ i).hom (openScalarRestriction φ k).hom
    qp qr (exactCoefficient_counit φ p) (exactCoefficient_counit φ r) hc M
  exact exchange_cancel
    ((openScalarRestriction φ i).app (R((p)_*[ModuleCat.{u + 1} A]).obj M))
    ((openScalarRestriction φ k).app M) R((r)_*[ModuleCat.{u + 1} B])
    _ _ _ _ h

end AlgebraicGeometry.Etale
