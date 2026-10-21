/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Sheaf.CategoryTheory.Abelian.RHomDerivedRoof
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp

/-!
# Derived transport of represented functors

Source: Stacks Project, derived.tex, Tags 05TH, 05TI, 070I and 015F;
representability and coherence calculation in the DAG
(blueprint: lem-pur-derived-representable-transport).

The comparisons below use the left Kan extension unit, the exact termwise derived
functor, and the roof-normalized comparison of `exists_rhom_hom_derived_roof`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u₁ u₂ u₃ v w₁ w₂ w₃ wAb

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂} [Category.{v} A] [Category.{v} B]
  [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  [HasDerivedCategory.{wAb} AddCommGrpCat.{v}]

/-- The termwise transformation followed by the target derived unit and exact
localization comparison. Source: Stacks Tags 05TI and 015F
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportUnit
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus) :=
  whiskerRight (NatTrans.mapHomotopyCategoryPlus tau) DerivedCategory.Plus.Qh ≫
    whiskerRight (mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ S'))).inv
      DerivedCategory.Plus.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft L.mapHomotopyCategoryPlus S'.rightDerivedFunctorPlusUnit ≫
    (associator _ _ _).inv ≫
    whiskerRight L.mapDerivedCategoryPlusFactorsh.inv S'.rightDerivedFunctorPlus ≫
    (associator _ _ _).hom

/-- The canonical comparison is the Kan factorization of `representableTransportUnit`.
Source: Stacks Tag 05TI (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportComparison
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus :=
  S.rightDerivedFunctorPlus.rightDerivedDesc S.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A) _ (representableTransportUnit L S S' tau)

/-- The roof-normalized RHom equivalence supplied by the recorded roof theorem.
Its normalization determines it on every injective representative.
Source: Stacks Tag 070I (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportRoof (P : A) (X : DerivedCategory.Plus A) (a : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
        ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlus.obj X) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :=
  Classical.choose (exists_rhom_hom_derived_roof P) X a

/-- Derive the inverse representing isomorphism, then apply the roof equivalence.
Source: Stacks Tags 05TI and 070I
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representedTransportHomEquiv
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S) (X : DerivedCategory.Plus A) (a : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
        (S.rightDerivedFunctorPlus.obj X) ≃+
      ((DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :=
  ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).mapIso
    ((rightDerivedFunctorPlusNatIso θ.symm).app X)).addCommGroupIsoToAddEquiv.trans
      (representableTransportRoof P X a)

/-- Apply the exact derived functor to a shifted morphism and precompose with `d⁻¹`.
The displayed single and shift isomorphisms are the termwise ones.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportHom
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P : A} {P' : B} (d : L.obj P ≅ P') (X : DerivedCategory.Plus A) (a : ℤ)
    (f : (DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :
    (DerivedCategory.singleFunctor B 0).obj P' ⟶
      (L.mapDerivedCategoryPlus.obj X).obj⟦a⟧ :=
  (DerivedCategory.singleFunctor B 0).map d.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫ L.mapDerivedCategory.map f ≫
    (L.mapDerivedCategory.commShiftIso a).hom.app X.obj

/-- The inverse of a localized resolution, transported through the fully faithful
bounded below inclusion and the canonical quotient comparisons.
Source: Stacks Tag 05RU (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportResolutionInverse
    {F I : CochainComplex.Plus A} (e : F ⟶ I) [QuasiIso e.hom] :
    (DerivedCategory.Plus.Q (C := A)).obj I ⟶ (DerivedCategory.Plus.Q (C := A)).obj F :=
  (DerivedCategory.Plus.ι (C := A)).preimage
    ((DerivedCategory.quotientCompQhIso A).inv.app I.obj ≫
      CategoryTheory.inv (DerivedCategory.Q.map e.hom) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app F.obj)

/-- The canonical map from the termwise injective model to the derived value at the
original complex. Its inverse-resolution arrow is taken after localization.
Source: Stacks Tags 05TH and 05TI
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportModel
    (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    {F I : CochainComplex.Plus A} (e : F ⟶ I) [QuasiIso e.hom] :
    (DerivedCategory.Plus.Q (C := AddCommGrpCat.{v})).obj
        (S.mapCochainComplexPlus.obj I) ⟶
      S.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.Q (C := A)).obj F) :=
  S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
    S.rightDerivedFunctorPlus.map (representableTransportResolutionInverse e)

/-- The exact termwise identification on a bounded below complex.
Source: Stacks Tag 015F (blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportExactIso
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (F : CochainComplex.Plus A) :
    L.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.Q (C := A)).obj F) ≅
      (DerivedCategory.Plus.Q (C := B)).obj (L.mapCochainComplexPlus.obj F) :=
  L.mapDerivedCategoryPlusFactorsh.app ((HomotopyCategory.Plus.quotient A).obj F)

/-- The chain map in the injective model: first the termwise transformation, then
apply the target functor to the comparison of resolutions.
Source: Stacks Tags 05TH and 05TI
(blueprint: lem-pur-derived-representable-transport). -/
noncomputable def representableTransportChainMap
    (L : A ⥤ B) [L.Additive]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S')
    (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj) :
    S.mapCochainComplexPlus.obj I ⟶ S'.mapCochainComplexPlus.obj J :=
  ObjectProperty.homMk
    ((NatTrans.mapHomologicalComplex tau (ComplexShape.up ℤ)).app I.obj ≫
      (mapHomologicalComplexCompIso (Iso.refl (L ⋙ S')) (ComplexShape.up ℤ)).inv.app
        I.obj ≫
      (S'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)

private lemma transport_fac
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    S.rightDerivedFunctorPlusUnit ≫
        whiskerLeft DerivedCategory.Plus.Qh (representableTransportComparison L S S' tau) =
      representableTransportUnit L S S' tau := by
  exact S.rightDerivedFunctorPlus.rightDerived_fac _ _ _ _

private lemma transport_ext
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S')
    (b : S.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus)
    (hb : S.rightDerivedFunctorPlusUnit ≫ whiskerLeft DerivedCategory.Plus.Qh b =
      representableTransportUnit L S S' tau) :
    b = representableTransportComparison L S S' tau := by
  apply S.rightDerivedFunctorPlus.rightDerived_ext S.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A)
  exact hb.trans (transport_fac L S S' tau).symm

omit [EnoughInjectives A] in
private lemma transport_unit_app
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') (K : HomotopyCategory.Plus A) :
    (representableTransportUnit L S S' tau).app K =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus tau).app K) ≫
        S'.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        S'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp [representableTransportUnit, mapHomotopyCategoryPlusCompIso_refl_inv_app]

omit [EnoughInjectives A] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_quotient_hom (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app K = 𝟙 _ :=
  CategoryTheory.Quotient.lift.isLift_hom _ _ _ K

omit [EnoughInjectives A] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_quotient_inv (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 _ :=
  CategoryTheory.Quotient.lift.isLift_inv _ _ _ K

private lemma transport_fac_app
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') (K : HomotopyCategory.Plus A) :
    S.rightDerivedFunctorPlusUnit.app K ≫
        (representableTransportComparison L S S' tau).app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus tau).app K) ≫
        S'.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        S'.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  exact (congr_app (transport_fac L S S' tau) K).trans (transport_unit_app L S S' tau K)

private noncomputable def transport_cycle
    (K : CochainComplex.Plus AddCommGrpCat.{v}) (a : ℤ)
    (x : AddMonoidHom.ker (K.obj.sc a).g.hom) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (DerivedCategory.Plus.Q.obj K) :=
  (DerivedCategory.Plus.homologyFunctorObjQIso K a).inv
    (K.obj.homologyπ a ((K.obj.sc a).abCyclesIso.inv x))

private lemma transport_cycle_map
    {K J : CochainComplex.Plus AddCommGrpCat.{v}} (φ : K ⟶ J) (a : ℤ)
    (x : AddMonoidHom.ker (K.obj.sc a).g.hom)
    (y : AddMonoidHom.ker (J.obj.sc a).g.hom) (hxy : φ.hom.f a x.val = y.val) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (DerivedCategory.Plus.Q.map φ) (transport_cycle K a x) = transport_cycle J a y := by
  have hn : (DerivedCategory.Plus.homologyFunctorObjQIso K a).inv ≫
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (DerivedCategory.Plus.Q.map φ) =
      HomologicalComplex.homologyMap φ.hom a ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso J a).inv := by
    apply (cancel_mono (DerivedCategory.Plus.homologyFunctorObjQIso J a).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality]
    simp
  unfold transport_cycle
  rw [← AddCommGrpCat.comp_apply, hn, AddCommGrpCat.comp_apply]
  congr 1
  erw [← AddCommGrpCat.comp_apply, HomologicalComplex.homologyπ_naturality,
    AddCommGrpCat.comp_apply]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (J.obj.iCycles a)).1 inferInstance
  rw [← AddCommGrpCat.comp_apply, HomologicalComplex.cyclesMap_i,
    AddCommGrpCat.comp_apply]
  dsimp only [HomologicalComplex.iCycles]
  erw [ShortComplex.abCyclesIso_inv_apply_iCycles,
    ShortComplex.abCyclesIso_inv_apply_iCycles]
  exact hxy

private lemma transport_homEquiv_naturality
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    {X Y : DerivedCategory.Plus A} (g : X ⟶ Y) (a : ℤ)
    (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj X)) :
    representedTransportHomEquiv P S θ Y a
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          (S.rightDerivedFunctorPlus.map g) α) =
      representedTransportHomEquiv P S θ X a α ≫
        ((DerivedCategory.Plus.ι (C := A)).map g)⟦a⟧' := by
  change representableTransportRoof P Y a
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
      ((rightDerivedFunctorPlusNatIso θ.symm).hom.app Y)
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (S.rightDerivedFunctorPlus.map g) α)) = _
  rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp,
    (rightDerivedFunctorPlusNatIso θ.symm).hom.naturality,
    Functor.map_comp, AddCommGrpCat.comp_apply]
  exact (Classical.choose_spec (exists_rhom_hom_derived_roof P)).1 X Y g a _

omit [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_hom_naturality
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {P : A} {P' : B} (d : L.obj P ≅ P') {X Y : DerivedCategory.Plus A}
    (g : X ⟶ Y) (a : ℤ) (f : (DerivedCategory.singleFunctor A 0).obj P ⟶ X.obj⟦a⟧) :
    representableTransportHom L d Y a (f ≫ ((DerivedCategory.Plus.ι (C := A)).map g)⟦a⟧') =
      representableTransportHom L d X a f ≫
        ((DerivedCategory.Plus.ι (C := B)).map (L.mapDerivedCategoryPlus.map g))⟦a⟧' := by
  simp only [representableTransportHom, Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]
  rfl

private lemma transport_roof_injective
    (P : A) (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k))
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    representableTransportRoof P (DerivedCategory.Plus.Q.obj I) a
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          ((preadditiveCoyoneda.obj (op P)).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient A).obj I))
          (transport_cycle ((preadditiveCoyoneda.obj (op P)).mapCochainComplexPlus.obj I)
            a ⟨f, by
              change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
              rw [CochainComplex.next]
              exact hf⟩)) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app I.obj)⟦a⟧' := by
  let := hi
  obtain ⟨n, hn⟩ := I.2
  let := hn
  let r : CochainComplex.KInjectiveResolutionChoice I.obj :=
    { complex := I.obj
      map := 𝟙 I.obj
      quasiIso := inferInstance
      isKInjective := CochainComplex.isKInjective_of_injective I.obj n }
  have h := (Classical.choose_spec (exists_rhom_hom_derived_roof P)).2
    I r I.2 hi a f hf
  have he : (DerivedCategory.Plus.ι (C := A)).preimageIso
      (X := DerivedCategory.Plus.Q.obj I) (Y := DerivedCategory.Plus.Q.obj I)
      ((DerivedCategory.quotientCompQhIso A).symm.app I.obj ≪≫
        asIso (DerivedCategory.Q.map (𝟙 I.obj)) ≪≫
        (DerivedCategory.quotientCompQhIso A).app I.obj) =
      Iso.refl (DerivedCategory.Plus.Q.obj I) := by
    apply Iso.ext
    apply (DerivedCategory.Plus.ι (C := A)).map_injective
    change (DerivedCategory.Plus.ι (C := A)).map
      ((DerivedCategory.Plus.ι (C := A)).preimage _) = 𝟙 _
    rw [Functor.map_preimage]
    simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, asIso_hom,
      Functor.map_id]
    erw [transport_quotient_inv]
    erw [Category.id_comp, Category.id_comp]
    rfl
  dsimp only [r] at h
  rw [he] at h
  simp only [Iso.refl_inv, Functor.map_id, AddCommGrpCat.id_apply,
    IsIso.inv_id, Category.id_comp] at h
  simpa only [representableTransportRoof, transport_cycle,
    rightDerivedComplexWithResolution, mapCochainComplexPlus] using! h

private lemma transport_unit_cycle_map
    (S T : A ⥤ AddCommGrpCat.{v}) [S.Additive] [T.Additive] (σ : S ⟶ T)
    (I : CochainComplex.Plus A) (a : ℤ)
    (x : AddMonoidHom.ker ((S.mapCochainComplexPlus.obj I).obj.sc a).g.hom)
    (y : AddMonoidHom.ker ((T.mapCochainComplexPlus.obj I).obj.sc a).g.hom)
    (hxy : σ.app (I.obj.X a) x.val = y.val) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        ((rightDerivedFunctorPlusNatTrans σ).app (DerivedCategory.Plus.Q.obj I))
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          (S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
          (transport_cycle (S.mapCochainComplexPlus.obj I) a x)) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        (T.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
        (transport_cycle (T.mapCochainComplexPlus.obj I) a y) := by
  erw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, rightDerivedFunctorPlusNatTrans_app,
    Functor.map_comp, AddCommGrpCat.comp_apply]
  congr 1
  let φ : S.mapCochainComplexPlus.obj I ⟶ T.mapCochainComplexPlus.obj I :=
    ObjectProperty.homMk ((NatTrans.mapHomologicalComplex σ (.up ℤ)).app I.obj)
  exact transport_cycle_map φ a x y (by exact hxy)

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_represented_closed
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (θ.hom.app (I.obj.X a) f) ∈
      AddMonoidHom.ker ((S.mapCochainComplexPlus.obj I).obj.sc a).g.hom := by
  have h := ConcreteCategory.congr_hom (θ.hom.naturality (I.obj.d a (a + 1))) f
  change S.map (I.obj.d a ((ComplexShape.up ℤ).next a))
    (θ.hom.app (I.obj.X a) f) = 0
  rw [CochainComplex.next]
  change θ.hom.app (I.obj.X (a + 1)) (f ≫ I.obj.d a (a + 1)) =
    S.map (I.obj.d a (a + 1)) (θ.hom.app (I.obj.X a) f) at h
  rw [hf, map_zero] at h
  exact h.symm

private noncomputable def transport_representedClass
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I)) :=
  (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
    (S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I))
    (transport_cycle (S.mapCochainComplexPlus.obj I) a
      ⟨θ.hom.app (I.obj.X a) f, transport_represented_closed P S θ I a f hf⟩)

private lemma transport_represented_norm
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k))
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    representedTransportHomEquiv P S θ (DerivedCategory.Plus.Q.obj I) a
        (transport_representedClass P S θ I a f hf) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q ≫
      ((DerivedCategory.quotientCompQhIso A).hom.app I.obj)⟦a⟧' := by
  change representableTransportRoof P _ a
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
      ((rightDerivedFunctorPlusNatTrans θ.inv).app _)
      (transport_representedClass P S θ I a f hf)) = _
  unfold transport_representedClass
  rw [transport_unit_cycle_map S (preadditiveCoyoneda.obj (op P)) θ.inv I a _
    ⟨f, by
      change f ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0
      rw [CochainComplex.next]
      exact hf⟩ (by simp)]
  exact transport_roof_injective P I hi a f hf

private lemma transport_represented_surjective
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) [S.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k))
    (a : ℤ) (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I))) :
    ∃ (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0),
      transport_representedClass P S θ I a f hf = α := by
  let := hi
  let V := preadditiveCoyoneda.obj (op P)
  let J := V.mapCochainComplexPlus.obj I
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a
  let T := (J.obj.sc a).abCyclesIso.inv ≫ J.obj.homologyπ a ≫
    (DerivedCategory.Plus.homologyFunctorObjQIso J a).inv ≫
    H.map (V.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I)) ≫
    H.map ((rightDerivedFunctorPlusNatIso θ).hom.app (DerivedCategory.Plus.Q.obj I))
  have hT : Function.Surjective T :=
    (AddCommGrpCat.epi_iff_surjective T).1 inferInstance
  obtain ⟨x, hx⟩ := hT α
  have hf : x.val ≫ I.obj.d a (a + 1) = 0 := by
    have hx := x.property
    change x.val ≫ I.obj.d a ((ComplexShape.up ℤ).next a) = 0 at hx
    rw [CochainComplex.next] at hx
    exact hx
  refine ⟨x.val, hf, ?_⟩
  have h := transport_unit_cycle_map V S θ.hom I a x
    ⟨θ.hom.app (I.obj.X a) x.val, transport_represented_closed P S θ I a x.val hf⟩ rfl
  exact h.symm.trans hx

omit [EnoughInjectives B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_Q_faithful
    {K J : CochainComplex B ℤ} [J.IsKInjective] (f g : K ⟶ J)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    Nonempty (Homotopy f g) := by
  apply Nonempty.intro
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient B (.up ℤ)).obj K) J).1
  change DerivedCategory.Q.map f = DerivedCategory.Q.map g
  exact h

omit [EnoughInjectives A] [HasDerivedCategory A]
  [EnoughInjectives B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_lift
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {F I : CochainComplex.Plus A} (J : CochainComplex.Plus B)
    (e : F ⟶ I) [QuasiIso e.hom]
    (e' : L.mapCochainComplexPlus.obj F ⟶ J)
    (hj : ∀ k : ℤ, Injective (J.obj.X k)) :
    ∃ t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
      Nonempty (Homotopy
        ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t) e'.hom) ∧
      (∀ t' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
        Nonempty (Homotopy
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t') e'.hom) →
        Nonempty (Homotopy t t')) := by
  let := hj
  obtain ⟨n, hn⟩ := J.2
  let := hn
  have : J.obj.IsKInjective := CochainComplex.isKInjective_of_injective J.obj n
  let Le := (L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom
  let LI := (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
  have : QuasiIso Le := inferInstance
  let u : DerivedCategory.Q.obj LI ⟶ DerivedCategory.Q.obj J.obj :=
    CategoryTheory.inv (DerivedCategory.Q.map Le) ≫ DerivedCategory.Q.map e'.hom
  obtain ⟨q, hq⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient B (.up ℤ)).obj LI) J.obj).2
      ((DerivedCategory.quotientCompQhIso B).inv.app LI ≫ u ≫
        (DerivedCategory.quotientCompQhIso B).hom.app J.obj)
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient B (.up ℤ)).map_surjective q
  have ht : DerivedCategory.Q.map t = u := by
    erw [transport_quotient_inv, transport_quotient_hom,
      Category.id_comp, Category.comp_id] at hq
    exact hq
  refine ⟨t, ?_, ?_⟩
  · apply transport_Q_faithful
    rw [Functor.map_comp, ht]
    simp [u]
  · intro t' ht'
    apply transport_Q_faithful
    apply (cancel_epi (DerivedCategory.Q.map Le)).1
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact (DerivedCategory.Q_map_eq_of_homotopy B
      (show Homotopy (Le ≫ t) e'.hom from
        (transport_Q_faithful (Le ≫ t) e'.hom (by
          rw [Functor.map_comp, ht]; simp [u])).some)).trans
      (DerivedCategory.Q_map_eq_of_homotopy B ht'.some).symm

omit [EnoughInjectives A] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_resolution_inverse
    {F I : CochainComplex.Plus A} (e : F ⟶ I) [QuasiIso e.hom]
    [IsIso ((DerivedCategory.Plus.Q (C := A)).map e)] :
    representableTransportResolutionInverse e =
      CategoryTheory.inv ((DerivedCategory.Plus.Q (C := A)).map e) := by
  have hIso : IsIso ((DerivedCategory.Plus.Q (C := A)).map e) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso e.hom›)
  apply (cancel_epi ((DerivedCategory.Plus.Q (C := A)).map e)).1
  erw [IsIso.hom_inv_id]
  apply (DerivedCategory.Plus.ι (C := A)).map_injective
  simp only [Functor.map_comp, Functor.map_id, representableTransportResolutionInverse,
    Functor.map_preimage]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient A (.up ℤ)).map e.hom) ≫
    ((DerivedCategory.quotientCompQhIso A).inv.app I.obj ≫
      CategoryTheory.inv (DerivedCategory.Q.map e.hom) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app F.obj) = _
  simp only [transport_quotient_inv, transport_quotient_hom]
  change DerivedCategory.Q.map e.hom ≫
    (𝟙 _ ≫ CategoryTheory.inv (DerivedCategory.Q.map e.hom) ≫ 𝟙 _) = 𝟙 _
  simp

private lemma transport_model_formula
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S')
    {F I : CochainComplex.Plus A} (J : CochainComplex.Plus B)
    (e : F ⟶ I) [QuasiIso e.hom]
    (e' : L.mapCochainComplexPlus.obj F ⟶ J) [QuasiIso e'.hom]
    (t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj)
    (ht : Nonempty (Homotopy
      ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t) e'.hom)) :
    representableTransportModel S e ≫
        (representableTransportComparison L S S' tau).app
          ((DerivedCategory.Plus.Q (C := A)).obj F) =
      DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) ≫
        representableTransportModel S' e' ≫
        S'.rightDerivedFunctorPlus.map (representableTransportExactIso L F).inv := by
  let Q₁ := DerivedCategory.Plus.Q (C := A)
  let Q₂ := DerivedCategory.Plus.Q (C := B)
  have he : IsIso (Q₁.map e) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso e.hom›)
  have he' : IsIso (Q₂.map e') :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 ‹QuasiIso e'.hom›)
  let Le : L.mapCochainComplexPlus.obj F ⟶ L.mapCochainComplexPlus.obj I :=
    L.mapCochainComplexPlus.map e
  let t₀ : L.mapCochainComplexPlus.obj I ⟶ J := ObjectProperty.homMk t
  have htQ : Q₂.map Le ≫ Q₂.map t₀ = Q₂.map e' := by
    apply (DerivedCategory.Plus.ι (C := B)).map_injective
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map Le.hom) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map t) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient B (.up ℤ)).map e'.hom)
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map (HomotopyCategory.eq_of_homotopy _ _ ht.some)
  dsimp only [representableTransportModel]
  rw [transport_resolution_inverse, transport_resolution_inverse]
  rw [Category.assoc, (representableTransportComparison L S S' tau).naturality]
  rw [← Category.assoc, transport_fac_app]
  dsimp only [representableTransportExactIso]
  have hn := S'.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient B).map t₀)
  have hc : DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus tau).app
        ((HomotopyCategory.Plus.quotient A).obj I)) ≫
      DerivedCategory.Plus.Qh.map (S'.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.quotient B).map t₀)) := by
    rw [← Functor.map_comp]
    rfl
  simp only [Functor.comp_map] at hn
  rw [hc]
  simp only [Category.assoc]
  erw [reassoc_of% hn]
  simp only [Functor.comp_map]
  congr 1
  congr 1
  simp only [← Functor.map_comp]
  congr 1
  have hLe : QuasiIso Le.hom := by
    change QuasiIso ((L.mapHomologicalComplex (.up ℤ)).map e.hom)
    infer_instance
  have heL : IsIso (Q₂.map Le) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        (inferInstanceAs (QuasiIso Le.hom)))
  apply (cancel_epi (Q₂.map Le)).1
  have hnL := L.mapDerivedCategoryPlusFactorsh.inv.naturality
    ((HomotopyCategory.Plus.quotient A).map e)
  simp only [Functor.comp_map] at hnL
  erw [← Category.assoc, hnL, Category.assoc, ← Functor.map_comp]
  erw [IsIso.hom_inv_id, Functor.map_id, Category.comp_id]
  erw [← Category.assoc, ← Category.assoc, htQ]
  simp only [Iso.app_inv, Category.assoc]
  erw [IsIso.hom_inv_id_assoc]

omit [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_cocycle_formula
    (L : A ⥤ B) [L.Additive]
    (P : A) (P' : B) (d : L.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S') (tau : S ⟶ L ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
    (t : (L.mapHomologicalComplex (.up ℤ)).obj I.obj ⟶ J.obj)
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    (d.inv ≫ L.map f ≫ t.f a) ≫ J.obj.d a (a + 1) = 0 ∧
      S'.map (t.f a) (tau.app (I.obj.X a) (θ.hom.app (I.obj.X a) f)) =
        θ'.hom.app (J.obj.X a) (d.inv ≫ L.map f ≫ t.f a) := by
  constructor
  · rw [Category.assoc, Category.assoc, t.comm]
    change d.inv ≫ L.map f ≫ L.map (I.obj.d a (a + 1)) ≫ t.f (a + 1) = 0
    rw [← L.map_comp_assoc, hf, L.map_zero]
    simp
  · rw [← h]
    have hh := ConcreteCategory.congr_hom (C := AddCommGrpCat.{v})
      (θ'.hom.naturality (t.f a))
      (show P' ⟶ L.obj (I.obj.X a) from d.inv ≫ L.map f)
    simp only [AddCommGrpCat.comp_apply] at hh
    dsimp [preadditiveCoyoneda, preadditiveCoyonedaObj] at hh
    simpa only [Category.assoc] using! hh.symm

omit [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] in
private lemma transport_represented_model_map
    (L : A ⥤ B) [L.Additive]
    (P : A) (P' : B) (d : L.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S') (tau : S ⟶ L ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
    (t : (L.mapHomologicalComplex (.up ℤ)).obj I.obj ⟶ J.obj)
    (a : ℤ) (f : P ⟶ I.obj.X a) (hf : f ≫ I.obj.d a (a + 1) = 0) :
    ∃ hg : (d.inv ≫ L.map f ≫ t.f a) ≫ J.obj.d a (a + 1) = 0,
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          (DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t))
          (transport_cycle (S.mapCochainComplexPlus.obj I) a
            ⟨θ.hom.app (I.obj.X a) f, transport_represented_closed P S θ I a f hf⟩) =
        transport_cycle (S'.mapCochainComplexPlus.obj J) a
          ⟨θ'.hom.app (J.obj.X a) (d.inv ≫ L.map f ≫ t.f a),
            transport_represented_closed P' S' θ' J a _ hg⟩ := by
  have hc := transport_cocycle_formula L P P' d S S' θ θ' tau h I J t a f hf
  refine ⟨hc.1, transport_cycle_map _ a _ _ ?_⟩
  exact hc.2

omit [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_exact_inv
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (I : CochainComplex.Plus A) :
    (DerivedCategory.Plus.ι (C := B)).map (representableTransportExactIso L I).inv =
      L.mapDerivedCategoryFactors.inv.app I.obj := by
  have hh : (DerivedCategory.Plus.ι (C := B)).map (representableTransportExactIso L I).hom =
      L.mapDerivedCategoryFactors.hom.app I.obj := by
    dsimp only [representableTransportExactIso]
    erw [ι_map_mapDerivedCategoryPlusFactorsh_hom_app, mapDerivedCategoryFactorsh_hom_app]
    simp [transport_quotient_hom, transport_quotient_inv, mapHomotopyCategoryFactors,
      Quotient.lift.isLift_inv]
  change ((DerivedCategory.Plus.ι (C := B)).mapIso
    (representableTransportExactIso L I)).inv = (L.mapDerivedCategoryFactors.app I.obj).inv
  exact congrArg Iso.inv (Iso.ext hh)

omit [EnoughInjectives A] [EnoughInjectives B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_shifted_map
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (P : A) (I : CochainComplex.Plus A) (a : ℤ)
    (f : (CochainComplex.singleFunctor A 0).obj P ⟶ I.obj⟦a⟧) :
    (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫
        ShiftedHom.map (ShiftedHom.map f DerivedCategory.Q) L.mapDerivedCategory =
      DerivedCategory.Q.map ((L.mapCochainComplexSingleFunctor 0).inv.app P) ≫
        ShiftedHom.map (ShiftedHom.map f (L.mapHomologicalComplex (.up ℤ))) DerivedCategory.Q ≫
          (L.mapDerivedCategoryFactors.inv.app I.obj)⟦a⟧' := by
  have hn := ShiftedHom.map_naturality_2 f L.mapDerivedCategoryFactors
  rw [ShiftedHom.comp_map, ShiftedHom.comp_map] at hn
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] at hn
  erw [← hn, ← Category.assoc,
    L.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app P]

omit [EnoughInjectives A] [EnoughInjectives B]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory AddCommGrpCat] in
private lemma transport_chain_single
    (L : A ⥤ B) [L.Additive]
    {P : A} {P' : B} (d : L.obj P ≅ P')
    (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
    (hf : f ≫ I.obj.d a (a + 1) = 0)
    (J : CochainComplex.Plus B)
    (t : (L.mapHomologicalComplex (.up ℤ)).obj I.obj ⟶ J.obj)
    (hg : (d.inv ≫ L.map f ≫ t.f a) ≫ J.obj.d a (a + 1) = 0) :
    (CochainComplex.singleFunctor B 0).map d.inv ≫
      (L.mapCochainComplexSingleFunctor 0).inv.app P ≫
      ShiftedHom.map
        (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf))
        (L.mapHomologicalComplex (.up ℤ)) ≫ t⟦a⟧' =
    Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk (d.inv ≫ L.map f ≫ t.f a) (zero_add a) (a + 1) rfl hg) := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp [ShiftedHom.map]
  simp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors, Functor.comp_obj,
    CochainComplex.shiftFunctor_obj_X', HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso_refl, Iso.refl_hom, Iso.refl_inv, Category.id_comp,
    Functor.mapCochainComplexSingleFunctor, HomologicalComplex.singleMapHomologicalComplex,
    NatIso.ofComponents_inv_app, ↓reduceDIte, eqToHom_refl,
    Cocycle.equivHomShift_symm_apply, Functor.mapHomologicalComplex_map_f,
    Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.fromSingleMk_coe,
    zero_add, Cochain.rightShift_v, Cochain.fromSingleMk_v,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq, eqToIso.inv,
    Functor.map_comp, Category.comp_id, Category.assoc, eqToHom_naturality]
  erw [Category.id_comp, eqToHom_map]

private lemma transport_formula_injective
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (P : A) (P' : B) (d : L.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive]
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S') (tau : S ⟶ L ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (I : CochainComplex.Plus A) (hi : ∀ k : ℤ, Injective (I.obj.X k)) (a : ℤ)
    (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
      (S.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj I))) :
    representedTransportHomEquiv P' S' θ'
        (L.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj I)) a
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
          ((representableTransportComparison L S S' tau).app (DerivedCategory.Plus.Q.obj I)) α) =
      representableTransportHom L d (DerivedCategory.Plus.Q.obj I) a
        (representedTransportHomEquiv P S θ (DerivedCategory.Plus.Q.obj I) a α) := by
  obtain ⟨f, hf, rfl⟩ := transport_represented_surjective P S θ I hi a α
  let LI := L.mapCochainComplexPlus.obj I
  obtain ⟨n, hn⟩ := LI.2
  let := hn
  obtain ⟨J₀, _, e', he'⟩ := CochainComplex.Plus.exists_quasiIso_injective LI n
  let J := (InjectiveObject.ι B).mapCochainComplexPlus.obj J₀
  have hj (k : ℤ) : Injective (J.obj.X k) := (J₀.obj.X k).2
  have : QuasiIso e'.hom := he'
  have hm := transport_model_formula L S S' tau J (𝟙 I) e' e'.hom
    ⟨Homotopy.ofEq (by simp)⟩
  obtain ⟨hg, hgmap⟩ := transport_represented_model_map L P P' d S S' θ θ' tau h
    I J e'.hom a f hf
  let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a
  let q := representableTransportResolutionInverse e' ≫ (representableTransportExactIso L I).inv
  have hm' : S.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient A).obj I) ≫
      (representableTransportComparison L S S' tau).app (DerivedCategory.Plus.Q.obj I) =
      DerivedCategory.Plus.Q.map
        (representableTransportChainMap L S S' tau I J e'.hom) ≫
        S'.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient B).obj J) ≫
        S'.rightDerivedFunctorPlus.map q := by
    dsimp only [representableTransportModel] at hm
    rw [transport_resolution_inverse (𝟙 I)] at hm
    simp only [Functor.map_id, IsIso.inv_id] at hm
    erw [Functor.map_id, Category.comp_id] at hm
    simpa only [q, Functor.map_comp, Category.assoc] using! hm
  unfold transport_representedClass
  erw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, hm', Functor.map_comp,
    Functor.map_comp, AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, hgmap]
  erw [transport_homEquiv_naturality P' S' θ' q a]
  erw [transport_represented_norm P' S' θ' J hj a _ hg,
    transport_represented_norm P S θ I hi a f hf]
  simp only [transport_quotient_hom]
  erw [Functor.map_id, Functor.map_id, Category.comp_id, Category.comp_id]
  have hq : (DerivedCategory.Plus.ι (C := B)).map q =
      CategoryTheory.inv (DerivedCategory.Q.map e'.hom) ≫
        L.mapDerivedCategoryFactors.inv.app I.obj := by
    simp only [q, Functor.map_comp, representableTransportResolutionInverse,
      Functor.map_preimage, transport_quotient_hom, transport_quotient_inv,
      transport_exact_inv]
    erw [Category.id_comp, Category.comp_id]
  rw [hq]
  change _ = (DerivedCategory.singleFunctor B 0).map d.inv ≫
    (L.mapDerivedCategorySingleFunctor 0).inv.app P ≫
      ShiftedHom.map (ShiftedHom.map
        (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add a) _ rfl hf))
        DerivedCategory.Q) L.mapDerivedCategory
  erw [transport_shifted_map L P I a
    (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk f (zero_add a) _ rfl hf))]
  have hnum := transport_chain_single L d I a f hf J e'.hom hg
  have hnum' :
      (ShiftedHom.mk₀ 0 rfl ((CochainComplex.singleFunctor B 0).map d.inv ≫
        (L.mapCochainComplexSingleFunctor 0).inv.app P)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.fromSingleMk f (zero_add a) _ rfl hf))
            (L.mapHomologicalComplex (.up ℤ))).comp
              (ShiftedHom.mk₀ 0 rfl e'.hom) (zero_add a)) (add_zero a) =
      Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (d.inv ≫ L.map f ≫ e'.hom.f a)
          (zero_add a) _ rfl hg) := by
    simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc] using hnum
  have hn := congrArg (fun x ↦ ShiftedHom.map x DerivedCategory.Q) hnum'
  rw [ShiftedHom.map_comp, ShiftedHom.map_comp,
    ShiftedHom.map_mk₀, ShiftedHom.map_mk₀] at hn
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    Functor.map_comp, Category.assoc] at hn
  rw [← hn]
  rw [Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    IsIso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [Functor.map_comp, Category.assoc]
  rfl

/-- The canonical comparison, its injective model and its represented Hom formula.
Source: Stacks Tags 05TH, 05TI, 070I and 015F, with the representability calculation
(blueprint: lem-pur-derived-representable-transport).

Proof: The left Kan extension property factors the termwise transformation followed
by the target unit, and makes that factorization unique. Exactness of L preserves
quasi-isomorphisms. A bounded below complex of injectives J is K-injective, so the
localized arrow Q(e') Q(Le)⁻¹ lifts to a chain map t, unique up to homotopy, and
t Le is homotopic to e'. Naturality of the derived comparison at e, its factorization
at I and naturality of the target unit at t give the displayed model formula; only
units at I and J are inverted, and LI need not be injective. The representing square
and naturality of the target representing isomorphism give the cocycle formula.
Derive the inverse representing isomorphisms and apply the roof-normalized RHom
comparison. The roof is Q(e')⁻¹ Q(t) Q(Lf) d⁻¹. Cancel Q(t) Q(Le) = Q(e') and use
the termwise shift comparison to obtain the asserted exact-functor action on Hom.
Every class has a cocycle representative. A boundary has zero localized single
map, and applying additive functors to homotopies gives equal derived maps.
The canonical comparison and the roof normalization therefore remove all choices. -/
theorem derived_representable_transport
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (P : A) (P' : B) (d : L.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] [PreservesFiniteLimits S] [PreservesFiniteLimits S']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S') (tau : S ⟶ L ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f)) :
    (S.rightDerivedFunctorPlusUnit ≫
        whiskerLeft DerivedCategory.Plus.Qh (representableTransportComparison L S S' tau) =
      representableTransportUnit L S S' tau) ∧
    (∀ b : S.rightDerivedFunctorPlus ⟶
        L.mapDerivedCategoryPlus ⋙ S'.rightDerivedFunctorPlus,
      S.rightDerivedFunctorPlusUnit ≫ whiskerLeft DerivedCategory.Plus.Qh b =
        representableTransportUnit L S S' tau →
      b = representableTransportComparison L S S' tau) ∧
    (∀ (F I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
        (e : F ⟶ I) [QuasiIso e.hom]
        (e' : L.mapCochainComplexPlus.obj F ⟶ J) [QuasiIso e'.hom]
        (_hi : ∀ k : ℤ, Injective (I.obj.X k))
        (_hj : ∀ k : ℤ, Injective (J.obj.X k)),
      ∃ t : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
        Nonempty (Homotopy
          ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t) e'.hom) ∧
        (∀ t' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj,
          Nonempty (Homotopy
            ((L.mapHomologicalComplex (ComplexShape.up ℤ)).map e.hom ≫ t') e'.hom) →
          Nonempty (Homotopy t t')) ∧
        (representableTransportModel S e ≫
            (representableTransportComparison L S S' tau).app
              ((DerivedCategory.Plus.Q (C := A)).obj F) =
          DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) ≫
            representableTransportModel S' e' ≫
            S'.rightDerivedFunctorPlus.map (representableTransportExactIso L F).inv) ∧
        (∀ (a : ℤ) (f : P ⟶ I.obj.X a) (_hf : f ≫ I.obj.d a (a + 1) = 0),
          (d.inv ≫ L.map f ≫ t.f a) ≫ J.obj.d a (a + 1) = 0 ∧
          S'.map (t.f a) (tau.app (I.obj.X a) (θ.hom.app (I.obj.X a) f)) =
            θ'.hom.app (J.obj.X a) (d.inv ≫ L.map f ≫ t.f a))) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P' S' θ' (L.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison L S S' tau).app X) α) =
        representableTransportHom L d X a (representedTransportHomEquiv P S θ X a α)) := by
  refine ⟨transport_fac L S S' tau, transport_ext L S S' tau, ?_, ?_⟩
  · intro F I J e he e' he' hi hj
    obtain ⟨t, ht, hut⟩ := transport_lift L J e e' hj
    refine ⟨t, ht, hut, transport_model_formula L S S' tau J e e' t ht, ?_⟩
    intro a f hf
    exact transport_cocycle_formula L P P' d S S' θ θ' tau h I J t a f hf
  · intro X a α
    obtain ⟨n, hn⟩ := X.2
    have : X.IsGE n := (X.isGE_ι_obj_iff n).1 hn
    obtain ⟨I₀, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso X n
    let I := (InjectiveObject.ι A).mapCochainComplexPlus.obj I₀
    have hi (k : ℤ) : Injective (I.obj.X k) := (I₀.obj.X k).2
    let H := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a
    let β := H.map (S.rightDerivedFunctorPlus.map e.inv) α
    have hb := transport_formula_injective L P P' d S S' θ θ' tau h I hi a β
    have hβ : H.map (S.rightDerivedFunctorPlus.map e.hom) β = α := by
      simp [β, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
    rw [← hβ]
    have hnat := (representableTransportComparison L S S' tau).naturality e.hom
    erw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, hnat,
      Functor.map_comp, AddCommGrpCat.comp_apply, transport_homEquiv_naturality,
      hb, transport_homEquiv_naturality, transport_hom_naturality]
    rw [hβ]
    simp [Category.assoc, ← Functor.map_comp]




set_option linter.unusedSectionVars false in
/-- Boundaries vanish and homotopic comparisons give the same derived model map.
Together with the resolution-uniform formula in `derived_representable_transport`,
this expresses independence of resolutions, comparison maps and cocycle representatives.
Source: Stacks Tags 05RU and 070I
(blueprint: lem-pur-derived-representable-transport).

Proof: A boundary f = g d has null-homotopic single-complex map: the only nonzero
homotopy component is (-1)^a g, which compensates for the shifted differential.
Localization through the homotopy category kills this map. Applying S' to a
homotopy and precomposing with the termwise transformation gives a homotopy of
the model chain maps, so their localized maps coincide. The model formula is
equal to the single canonical comparison for every resolution, proving the
remaining independence assertions. -/
theorem derived_representable_transport_independence
    (L : A ⥤ B) [L.Additive]
    (P : A) (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') :
    (∀ (I : CochainComplex.Plus A) (a : ℤ) (f : P ⟶ I.obj.X a)
        (hf : f ≫ I.obj.d a (a + 1) = 0),
      (∃ g : P ⟶ I.obj.X (a - 1), g ≫ I.obj.d (a - 1) a = f) →
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk f (zero_add a) (a + 1) rfl hf)) DerivedCategory.Q = 0) ∧
    (∀ (I : CochainComplex.Plus A) (J : CochainComplex.Plus B)
        (t t' : (L.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj ⟶ J.obj),
      Nonempty (Homotopy t t') →
      DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t) =
        DerivedCategory.Plus.Q.map (representableTransportChainMap L S S' tau I J t')) := by
  constructor
  · intro I a f hf hb
    have hc := (Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add a)
      (a + 1) rfl hf (a - 1) (by omega)).2 hb
    have hz := (CohomologyClass.toHom_mk_eq_zero_iff _).2 hc
    rw [CohomologyClass.toHom_mk, HomotopyCategory.quotient_map_eq_zero_iff] at hz
    obtain ⟨hz⟩ := hz
    simp only [ShiftedHom.map]
    rw [DerivedCategory.Q_map_eq_of_homotopy A hz]
    simp
  · intro I J t t' ht
    apply (DerivedCategory.Plus.ι (C := AddCommGrpCat.{v})).map_injective
    change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map _) = DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ _).map _)
    congr 1
    apply HomotopyCategory.eq_of_homotopy
    exact ((S'.mapHomotopy ht.some).compLeft
      ((NatTrans.mapHomologicalComplex tau (ComplexShape.up ℤ)).app I.obj ≫
        (mapHomologicalComplexCompIso (Iso.refl (L ⋙ S')) (ComplexShape.up ℤ)).inv.app
          I.obj))

variable {C : Type u₃} [Category.{v} C] [Abelian C] [EnoughInjectives C]
  [HasDerivedCategory.{w₃} C]

private lemma transport_comparison_comp
    (L : A ⥤ B) (L₂ : B ⥤ C) [L.Additive] [L₂.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    (S'' : C ⥤ AddCommGrpCat.{v}) [S.Additive] [S'.Additive] [S''.Additive]
    (tau : S ⟶ L ⋙ S') (tau₂ : S' ⟶ L₂ ⋙ S'') :
    representableTransportComparison (L ⋙ L₂) S S''
          (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv) ≫
        whiskerRight (mapDerivedCategoryPlusCompIso L L₂).hom S''.rightDerivedFunctorPlus =
      representableTransportComparison L S S' tau ≫
        whiskerLeft L.mapDerivedCategoryPlus (representableTransportComparison L₂ S' S'' tau₂) ≫
        (associator L.mapDerivedCategoryPlus L₂.mapDerivedCategoryPlus
          S''.rightDerivedFunctorPlus).inv := by
  apply S.rightDerivedFunctorPlus.rightDerived_ext S.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso A)
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_inv_app,
    Category.comp_id]
  erw [reassoc_of% (transport_fac_app (L ⋙ L₂) S S''
    (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv) K)]
  erw [reassoc_of% (transport_fac_app L S S' tau K)]
  erw [← Functor.map_comp]
  have hc : (L ⋙ L₂).mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (mapDerivedCategoryPlusCompIso L L₂).hom.app (DerivedCategory.Plus.Qh.obj K) =
      L₂.mapDerivedCategoryPlusFactorsh.inv.app (L.mapHomotopyCategoryPlus.obj K) ≫
        L₂.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
    apply (cancel_mono (L₂.mapDerivedCategoryPlus.map
      (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      L₂.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K))).1
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [mapDerivedCategoryPlusCompIso_hom_app_factorsh]
    erw [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app,
      Iso.inv_hom_id_app]
    rfl
  erw [hc, Functor.map_comp]
  erw [(representableTransportComparison L₂ S' S'' tau₂).naturality]
  erw [reassoc_of% (transport_fac_app L₂ S' S'' tau₂
    (L.mapHomotopyCategoryPlus.obj K))]
  have ht : (NatTrans.mapHomotopyCategoryPlus
      (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv)).app K =
      (NatTrans.mapHomotopyCategoryPlus tau).app K ≫
        (NatTrans.mapHomotopyCategoryPlus tau₂).app (L.mapHomotopyCategoryPlus.obj K) := by
    simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app]
    rfl
  erw [ht, Functor.map_comp]
  simp only [Category.assoc, Functor.comp_map]
  rfl

/-- Composition of canonical derived comparisons and of the represented Hom formula.
The total representing isomorphism is `L₂(d)` followed by `d₂`; the total underived
transformation is `tau` followed by `L(tau₂)`.
Source: Stacks Tags 05TI and 015F; Kan uniqueness and inverse-composition calculation
(blueprint: lem-pur-derived-representable-transport).

Proof: Compose the defining factorization equations. The composite factors exactly
the termwise total transformation followed by the final derived unit. Uniqueness
of the source Kan factorization identifies it with the total comparison under
the canonical exact-functor composition isomorphism. Apply the two representing
squares successively; the inverse of L₂(d) d₂ is d₂⁻¹ L₂(d⁻¹).
Apply the Hom formula twice. Functoriality, the single-complex identifications and
the termwise shift comparisons identify this with the Hom formula for the total
datum. No functor is required to preserve injective objects. -/
theorem derived_representable_transport_comp
    (L : A ⥤ B) (L₂ : B ⥤ C) [L.Additive] [L₂.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    (P : A) (P' : B) (P'' : C) (d : L.obj P ≅ P') (d₂ : L₂.obj P' ≅ P'')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    (S'' : C ⥤ AddCommGrpCat.{v}) [S.Additive] [S'.Additive] [S''.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteLimits S'] [PreservesFiniteLimits S'']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S')
    (θ'' : preadditiveCoyoneda.obj (op P'') ≅ S'')
    (tau : S ⟶ L ⋙ S') (tau₂ : S' ⟶ L₂ ⋙ S'')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (h₂ : ∀ (M : B) (f : P' ⟶ M),
      θ''.hom.app (L₂.obj M) (d₂.inv ≫ L₂.map f) = tau₂.app M (θ'.hom.app M f)) :
    (∀ (M : A) (f : P ⟶ M),
      θ''.hom.app ((L ⋙ L₂).obj M)
          ((L₂.mapIso d ≪≫ d₂).inv ≫ (L ⋙ L₂).map f) =
        (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv).app M
          (θ.hom.app M f)) ∧
    (representableTransportComparison (L ⋙ L₂) S S''
          (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv) ≫
        whiskerRight (mapDerivedCategoryPlusCompIso L L₂).hom S''.rightDerivedFunctorPlus =
      representableTransportComparison L S S' tau ≫
        whiskerLeft L.mapDerivedCategoryPlus (representableTransportComparison L₂ S' S'' tau₂) ≫
        (associator L.mapDerivedCategoryPlus L₂.mapDerivedCategoryPlus
          S''.rightDerivedFunctorPlus).inv) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P'' S'' θ'' ((L ⋙ L₂).mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison (L ⋙ L₂) S S''
              (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv)).app X) α) ≫
        ((mapDerivedCategoryCompIso L L₂).hom.app X.obj)⟦a⟧' =
      representableTransportHom L₂ d₂ (L.mapDerivedCategoryPlus.obj X) a
        (representableTransportHom L d X a (representedTransportHomEquiv P S θ X a α))) := by
  have hc := transport_comparison_comp L L₂ S S' S'' tau tau₂
  refine ⟨?_, hc, ?_⟩
  · intro M f
    simp only [Iso.trans_inv, mapIso_inv, Functor.comp_obj, Functor.comp_map,
      NatTrans.comp_app, whiskerLeft_app, associator_inv_app, Category.comp_id,
      AddCommGrpCat.comp_apply, Category.assoc]
    change θ''.hom.app (L₂.obj (L.obj M))
      (d₂.inv ≫ L₂.map d.inv ≫ L₂.map (L.map f)) =
      tau₂.app (L.obj M) (tau.app M (θ.hom.app M f))
    rw [← L₂.map_comp, h₂, h]
  · intro X a α
    have hn := transport_homEquiv_naturality P'' S'' θ''
      ((mapDerivedCategoryPlusCompIso L L₂).hom.app X) a
      ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
        ((representableTransportComparison (L ⋙ L₂) S S''
          (tau ≫ whiskerLeft L tau₂ ≫ (associator L L₂ S'').inv)).app X) α)
    simp only [ι_map_mapDerivedCategoryPlusCompIso_hom_app] at hn
    erw [← hn, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
    have hx := congr_app hc X
    simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      associator_inv_app, Category.comp_id] at hx
    rw [hx, Functor.map_comp, AddCommGrpCat.comp_apply]
    erw [(derived_representable_transport L₂ P' P'' d₂ S' S'' θ' θ'' tau₂ h₂).2.2.2,
      (derived_representable_transport L P P' d S S' θ θ' tau h).2.2.2]

private lemma transport_comparison_coherence
    (L T : A ⥤ B) [L.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (zeta : L ≅ T)
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] (tau : S ⟶ L ⋙ S') (tauT : S ⟶ T ⋙ S')
    (htau : tau ≫ whiskerRight zeta.hom S' = tauT) :
    representableTransportComparison L S S' tau ≫
        whiskerRight (mapDerivedCategoryPlusNatIso zeta).hom S'.rightDerivedFunctorPlus =
      representableTransportComparison T S S' tauT := by
  apply transport_ext T S S' tauT
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← Category.assoc, transport_fac_app]
  rw [transport_unit_app]
  have hz : L.mapDerivedCategoryPlusFactorsh.inv.app K ≫
      (mapDerivedCategoryPlusNatIso zeta).hom.app (DerivedCategory.Plus.Qh.obj K) =
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus zeta.hom).app K) ≫
        T.mapDerivedCategoryPlusFactorsh.inv.app K := by
    apply (cancel_mono (T.mapDerivedCategoryPlusFactorsh.hom.app K)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [mapDerivedCategoryPlusNatIso_hom_app_factorsh]
    simp
  have ht : (NatTrans.mapHomotopyCategoryPlus tauT).app K =
      (NatTrans.mapHomotopyCategoryPlus tau).app K ≫
        S'.mapHomotopyCategoryPlus.map
          ((NatTrans.mapHomotopyCategoryPlus zeta.hom).app K) := by
    rw [← htau, NatTrans.mapHomotopyCategoryPlus_comp]
    rfl
  rw [Category.assoc, Category.assoc, ← Functor.map_comp, hz, Functor.map_comp]
  have hnat := S'.rightDerivedFunctorPlusUnit.naturality
    ((NatTrans.mapHomotopyCategoryPlus zeta.hom).app K)
  simp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat]
  rw [← DerivedCategory.Plus.Qh.map_comp_assoc, ht]

set_option linter.unusedVariables false in
/-- Coherent identifications of exact functors preserve the canonical comparison and
its represented Hom formula. This applies in particular to identified composites.
Source: Stacks Tags 05RU, 05TI and 015F; naturality and Kan uniqueness
(blueprint: lem-pur-derived-representable-transport).

Proof: Localize the termwise natural isomorphism zeta. Naturality of the target
unit shows that postcomposing the first comparison by RS'(D zeta) factors the
second underived transformation. Kan uniqueness identifies it with the second
comparison. Naturality of D zeta at the morphism from P[0] to X[a], compatibility
with the termwise shifts, and dT zeta_P = d identify the two Hom formulas.
This also covers arbitrary coherently identified composites, by the composition
clause and the canonical localized composition identifications. -/
theorem derived_representable_transport_coherence
    (L T : A ⥤ B) [L.Additive] [T.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (zeta : L ≅ T) (P : A) (P' : B) (d : L.obj P ≅ P') (dT : T.obj P ≅ P')
    (S : A ⥤ AddCommGrpCat.{v}) (S' : B ⥤ AddCommGrpCat.{v})
    [S.Additive] [S'.Additive] [PreservesFiniteLimits S] [PreservesFiniteLimits S']
    (θ : preadditiveCoyoneda.obj (op P) ≅ S)
    (θ' : preadditiveCoyoneda.obj (op P') ≅ S')
    (tau : S ⟶ L ⋙ S') (tauT : S ⟶ T ⋙ S')
    (h : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (L.obj M) (d.inv ≫ L.map f) = tau.app M (θ.hom.app M f))
    (hT : ∀ (M : A) (f : P ⟶ M),
      θ'.hom.app (T.obj M) (dT.inv ≫ T.map f) = tauT.app M (θ.hom.app M f))
    (hd : zeta.hom.app P ≫ dT.hom = d.hom)
    (htau : tau ≫ whiskerRight zeta.hom S' = tauT) :
    (representableTransportComparison L S S' tau ≫
        whiskerRight (mapDerivedCategoryPlusNatIso zeta).hom S'.rightDerivedFunctorPlus =
      representableTransportComparison T S S' tauT) ∧
    (∀ (X : DerivedCategory.Plus A) (a : ℤ)
        (α : (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).obj
          (S.rightDerivedFunctorPlus.obj X)),
      representedTransportHomEquiv P' S' θ' (L.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison L S S' tau).app X) α) ≫
        ((mapDerivedCategoryNatIso zeta).hom.app X.obj)⟦a⟧' =
      representedTransportHomEquiv P' S' θ' (T.mapDerivedCategoryPlus.obj X) a
          ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
            ((representableTransportComparison T S S' tauT).app X) α)) := by
  have hc := transport_comparison_coherence L T zeta S S' tau tauT htau
  refine ⟨hc, ?_⟩
  intro X a α
  have hn := transport_homEquiv_naturality P' S' θ'
    ((mapDerivedCategoryPlusNatIso zeta).hom.app X) a
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} a).map
      ((representableTransportComparison L S S' tau).app X) α)
  simp only [ι_map_mapDerivedCategoryPlusNatIso_hom_app] at hn
  erw [← hn, ← AddCommGrpCat.comp_apply, ← Functor.map_comp]
  have hx := congr_app hc X
  change (representableTransportComparison L S S' tau).app X ≫
    S'.rightDerivedFunctorPlus.map ((mapDerivedCategoryPlusNatIso zeta).hom.app X) =
    (representableTransportComparison T S S' tauT).app X at hx
  rw [hx]
  rfl

end CategoryTheory.Functor
