/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraLeftAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.WeilSheaf.FiniteLeray
import WeilConjectures.WeilSheaf.DirectImageRestriction
import WeilConjectures.WeilSheaf.UpperStarComp
import WeilConjectures.WeilSheaf.IsotypicPullback
import Mathlib.CategoryTheory.Localization.Adjunction
import WeilConjectures.WeilSheaf.Localization
import WeilConjectures.WeilSheaf.ProperBaseChange
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-! # Proper/open interchange for native Weil complexes

The source is the bounded constructible full subcategory of the ordinary native derived
category. The target is the ordinary derived category of all pro-etale Weil sheaves.

## Implementation details

The comparison morphism `j_! Rp'_* K ⟶ Rp_* j'_! K` is constructed as a morphism of the native
derived category (the adjunct of the inverse of the comparison `j^* Rp_* j'_! K ≅ Rp'_* K`
obtained from K-injective representatives), so it includes the Weil structure. Its
invertibility is then detected after forgetting the Weil structure, using the open-closed
localization sequence and continuous-adic proper base change on the closed complement, which
only applies to bounded constructible inputs.

## References

Stacks Project, Tag 0F7B.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor

namespace CategoryTheory

private theorem inverseMate_app
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) (M : C) :
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β)).app M) =
      L₂.map (G.map (a₁.unit.app M)) ≫
        L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M)) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.mk, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_id, Category.id_comp]
  change _ ≫ _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.comp_id]

private noncomputable def inverseMateNatTrans
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (β : R₁ ⋙ G ⟶ H ⋙ R₂) : G ⋙ L₂ ⟶ L₁ ⋙ H where
  app M := L₂.map (G.map (a₁.unit.app M)) ≫
    L₂.map (β.app (L₁.obj M)) ≫ a₂.counit.app (H.obj (L₁.obj M))
  naturality M N f := by
    have h := (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ β))).naturality f
    simpa only [inverseMate_app] using h

end CategoryTheory

namespace AlgebraicGeometry

private noncomputable def nativeOpenAdjunction
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    ProEtaleWeilSheaf.extensionByZero k₀ l j ⊣ ProEtaleWeilSheaf.upperStar k₀ l j := by
  apply IsoAlgebra.mapOfNatIsoLeftAdjunction
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l _)
    (ProEtale.adicUpperStarLowerStarAdjunction l _)
    _ _ _ (ProEtale.mateEquiv_adicUpperStarGeometricFiberMapCompFrobeniusIso_inv l j _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar l _)
    (ProEtale.adicOpenImmersionLowerShriekToLowerStar_geometricFiberMapCompFrobeniusIso l j _)
  intro K
  exact ProEtale.adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar
    _ K

private theorem nativeOpenAdjunction_unit_isIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U S : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
    [S.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ S) [j.IsOver (Spec (CommRingCat.of k₀))] [IsOpenImmersion j] :
    IsIso (nativeOpenAdjunction k₀ l j).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h : IsIso ((IsoAlgebra.forget _).map
      ((nativeOpenAdjunction k₀ l j).unit.app M)) := by
    change IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).unit.app M.carrier)
    infer_instance
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

end AlgebraicGeometry

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private noncomputable def exactDerivedAdjunction (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory := by
  letI : CatCommSq (L.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q R.mapDerivedCategory := ⟨R.mapDerivedCategoryFactors.symm⟩
  exact (adj.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

private theorem exactDerivedAdjunction_unit_isIso (adj : L ⊣ R) [IsIso adj.unit] :
    IsIso adj.exactDerivedAdjunction.unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  let M : CochainComplex C ℤ := DerivedCategory.Q.objPreimage K
  have hM : IsIso (adj.exactDerivedAdjunction.unit.app
      (DerivedCategory.Q.obj M)) := by
    unfold exactDerivedAdjunction
    rw [Adjunction.localization_unit_app]
    have : ∀ n : ℤ, IsIso
        (((adj.mapHomologicalComplex (.up ℤ)).unit.app M).f n) := by
      intro n
      change IsIso (adj.unit.app (M.X n))
      infer_instance
    have := HomologicalComplex.Hom.isIso_of_components
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app M)
    infer_instance
  exact (NatTrans.isIso_app_iff_of_iso adj.exactDerivedAdjunction.unit
    (DerivedCategory.Q.objObjPreimageIso K)).mp hM

private theorem exactDerivedAdjunction_counit_isIso_of_isZero
    {Z : Type*} [Category Z] [Abelian Z] [HasDerivedCategory Z]
    (adj : L ⊣ R) [IsIso adj.unit]
    (iUp : D ⥤ Z) [iUp.Additive]
    [PreservesFiniteLimits iUp] [PreservesFiniteColimits iUp]
    (h₀ : ∀ M, IsZero (iUp.obj (L.obj M)))
    (hdet : ∀ F, IsZero (iUp.obj F) → IsZero (R.obj F) → IsZero F)
    {K : DerivedCategory D} (hK : IsZero (iUp.mapDerivedCategory.obj K)) :
    IsIso (adj.exactDerivedAdjunction.counit.app K) := by
  let adj' := adj.exactDerivedAdjunction
  have := adj.exactDerivedAdjunction_unit_isIso
  obtain ⟨W, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle
    (adj'.counit.app K)
  have hr : IsIso (R.mapDerivedCategory.map (adj'.counit.app K)) :=
    IsIso.of_isIso_fac_left (adj'.right_triangle_components K)
  have hi : IsIso (iUp.mapDerivedCategory.map (adj'.counit.app K)) :=
    isIso_of_source_target_iso_zero _
      (DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj h₀ _).isoZero
      hK.isoZero
  have hW : IsZero W := DerivedCategory.isZero_of_isZero_mapDerivedCategory_obj hdet
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (iUp.mapDerivedCategory.map_distinguished _ hT)).2 hi)
    ((Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      (R.mapDerivedCategory.map_distinguished _ hT)).2 hr)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).1 hW

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

attribute [local irreducible] nativeOpenAdjunction

private noncomputable def nativeOpenBaseChangeMap
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) :
    ProEtaleWeilSheaf.lowerStar k₀ l p ⋙ ProEtaleWeilSheaf.upperStar k₀ l j ⟶
      ProEtaleWeilSheaf.upperStar k₀ l b ⋙ ProEtaleWeilSheaf.lowerStar k₀ l q :=
  inverseMateNatTrans (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l b)
    (ProEtaleWeilSheaf.upperStarLowerStarAdjunction k₀ l j)
    (ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom

@[reassoc]
private theorem adicLowerStarCongr_trans
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g h : P ⟶ X}
    (e : f = g) (e' : g = h) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).hom.app M ≫
      (ProEtale.adicLowerStarCongr l e').hom.app M =
        (ProEtale.adicLowerStarCongr l (e.trans e')).hom.app M := by
  subst e
  subst e'
  apply Mod.hom_ext
  simp only [Mod.comp_hom', ProEtale.adicLowerStarCongr_hom_app_hom,
    ProEtale.lowerStarCongr_rfl, Iso.refl_hom, NatTrans.id_app]
  exact Category.id_comp _

private theorem adicLowerStarCongr_inv
    (l : ℕ) [Fact l.Prime] {P X : Scheme.{u}} {f g : P ⟶ X}
    (e : f = g) (M : ProEtale.AdicSheaf l P) :
    (ProEtale.adicLowerStarCongr l e).inv.app M =
      (ProEtale.adicLowerStarCongr l e.symm).hom.app M := by
  subst e
  apply Mod.hom_ext
  rfl

private theorem nativeLowerStarSquareIso_underlying
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {V U P X : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
    [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    (sq : CommSq q b j p) (M : ProEtaleWeilSheaf k₀ l V) :
    ((ProEtaleWeilSheaf.lowerStarSquareIso k₀ l sq.w.symm).hom.app M).hom.f =
      (ProEtale.adicSquareLowerStarIso l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).hom.app M.carrier := by
  simp only [ProEtaleWeilSheaf.lowerStarSquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, IsoAlgebra.comp_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_hom_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCompIso_inv_app_hom_f,
    ProEtaleWeilSheaf.lowerStarCongr_hom_app_hom_f,
    Iso.trans_inv, ProEtale.adicSquareLowerStarIso]
  simp only [Category.assoc, adicLowerStarCongr_inv]
  rw [adicLowerStarCongr_trans_assoc, adicLowerStarCongr_trans_assoc]

private theorem nativeUpperStar_map_hom_f
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {V P : Scheme.{u}}
    [V.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    (b : V ⟶ P) [b.IsOver (Spec (CommRingCat.of k₀))]
    {M N : ProEtaleWeilSheaf k₀ l P} (f : M ⟶ N) :
    ((ProEtaleWeilSheaf.upperStar k₀ l b).map f).hom.f =
      (ProEtale.adicUpperStar l (Scheme.Hom.geometricFiberMap b (comp_over b _))).map
        f.hom.f := rfl

section NativeOpenBaseChange

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {V U P X : Scheme.{u}}
  [V.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
  [P.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
  (q : V ⟶ U) (b : V ⟶ P) (j : U ⟶ X) (p : P ⟶ X)
  [q.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
  [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
  [IsOpenImmersion b] [IsOpenImmersion j]

omit [IsOpenImmersion b] [IsOpenImmersion j] in
private theorem nativeOpenBaseChangeMap_underlying (sq : CommSq q b j p)
    (M : ProEtaleWeilSheaf k₀ l P) :
    ((nativeOpenBaseChangeMap k₀ l q b j p sq).app M).hom.f =
      (ProEtale.adicBaseChangeMap l
        (CommSq.mk (show Scheme.Hom.geometricFiberMap q (comp_over q _) ≫
            Scheme.Hom.geometricFiberMap j (comp_over j _) =
          Scheme.Hom.geometricFiberMap b (comp_over b _) ≫
            Scheme.Hom.geometricFiberMap p (comp_over p _) by
          rw [← Scheme.Hom.geometricFiberMap_comp, ← Scheme.Hom.geometricFiberMap_comp]
          exact Scheme.Hom.geometricFiberMap_congr sq.w _ _))).app M.carrier := by
  simp only [nativeOpenBaseChangeMap, inverseMateNatTrans,
    ProEtale.adicBaseChangeMap, inverseMate_app,
    IsoAlgebra.comp_hom_f, ProEtaleWeilSheaf.lowerStar_map_hom_f,
    nativeUpperStar_map_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_unit_app_hom_f,
    ProEtaleWeilSheaf.upperStarLowerStarAdjunction_counit_app_hom_f]
  rw [nativeLowerStarSquareIso_underlying k₀ l q b j p sq]
  rfl

attribute [local irreducible] nativeOpenBaseChangeMap

private theorem nativeOpenBaseChangeMap_isIso (hsq : IsPullback q b j p) :
    IsIso (nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq) := by
  have hgeo := Scheme.Hom.isPullback_geometricFiberMap_of_isPullback (k := k₀) hsq
    (comp_over q _) (comp_over b _) (comp_over j _) (comp_over p _)
  have := ProEtale.isIso_adicBaseChangeMap_of_isPullback l hgeo
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso ((IsoAlgebra.forget _).map
      ((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M)) := by
    change IsIso (((nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq).app M).hom.f)
    rw [nativeOpenBaseChangeMap_underlying]
    infer_instance
  exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)

private noncomputable def nativeDerivedOpenBaseChangeIso (hsq : IsPullback q b j p) :
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor ⋙
      (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory ≅
        (ProEtaleWeilSheaf.upperStar k₀ l b).mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor := by
  have := nativeOpenBaseChangeMap_isIso k₀ l q b j p hsq
  have := (nativeOpenAdjunction k₀ l b).preservesKInjectiveComplexes
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso
      (asIso (nativeOpenBaseChangeMap k₀ l q b j p hsq.toCommSq)) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    Functor.isoWhiskerRight
      (ProEtaleWeilSheaf.upperStar k₀ l b).rightDerivedFunctorIsoMapDerivedCategory _

end NativeOpenBaseChange

private noncomputable def nativeOpenExtensionCompIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))]
    (s : A ⟶ B) (b : B ⟶ C)
    [s.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [IsOpenImmersion b] :
    ProEtaleWeilSheaf.extensionByZero k₀ l s ⋙
      ProEtaleWeilSheaf.extensionByZero k₀ l b ≅
        ProEtaleWeilSheaf.extensionByZero k₀ l (s ≫ b) :=
  (((nativeOpenAdjunction k₀ l s).comp (nativeOpenAdjunction k₀ l b)).ofNatIsoRight
    (ProEtaleWeilSheaf.upperStarCompIso k₀ l s b).symm).leftAdjointUniq
      (nativeOpenAdjunction k₀ l (s ≫ b))

private noncomputable def nativeOpenFactorRestrictionIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {A B C : Scheme.{u}}
    [A.Over (Spec (CommRingCat.of k₀))] [B.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₀))]
    (s : A ⟶ B) (b : B ⟶ C) (a : A ⟶ C)
    [s.IsOver (Spec (CommRingCat.of k₀))] [b.IsOver (Spec (CommRingCat.of k₀))]
    [a.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion s] [IsOpenImmersion b] [IsOpenImmersion a] (h : s ≫ b = a) :
    ProEtaleWeilSheaf.extensionByZero k₀ l a ⋙
      ProEtaleWeilSheaf.upperStar k₀ l b ≅
        ProEtaleWeilSheaf.extensionByZero k₀ l s := by
  subst a
  have := nativeOpenAdjunction_unit_isIso k₀ l b
  exact Functor.isoWhiskerRight (nativeOpenExtensionCompIso k₀ l s b).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (nativeOpenAdjunction k₀ l b).unit).symm ≪≫
    Functor.rightUnitor _

private theorem nativeOpenExtension_disjoint
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    {U X Z : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) (i : Z ⟶ X)
    [j.IsOver (Spec (CommRingCat.of k₀))] [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j] (h : Set.range j.base ∩ Set.range i.base = ∅)
    (M : ProEtaleWeilSheaf k₀ l U) :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).obj
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j).obj M)) := by
  apply (ProEtaleWeilSheaf.isZero_iff _).2
  apply ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek
    (Scheme.Hom.geometricFiberMap j (comp_over j _))
    (Scheme.Hom.geometricFiberMap i (comp_over i _)) _ M.carrier
  rw [Scheme.Hom.range_geometricFiberMap, Scheme.Hom.range_geometricFiberMap,
    ← Set.preimage_inter, h]
  simp

private noncomputable def nativeOpenProperRestrictionIso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U' P U X : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ P) (p' : U' ⟶ U) (j : U ⟶ X) (p : P ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [IsOpenImmersion j] [IsProper p] [IsProper p']
    (hc : j' ≫ p = p' ≫ j) :
    ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor) ⋙
        (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory ≅
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor := by
  let V := pullback p j
  let b : V ⟶ P := pullback.fst p j
  let q : V ⟶ U := pullback.snd p j
  let s : U' ⟶ V := pullback.lift j' p' hc
  let : V.Over (Spec (CommRingCat.of k₀)) :=
    ⟨b ≫ P ↘ Spec (CommRingCat.of k₀)⟩
  have : b.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    dsimp only [q, b]
    rw [← comp_over j (Spec (CommRingCat.of k₀)), ← Category.assoc,
      ← pullback.condition, Category.assoc, comp_over]
    rfl⟩
  have hsb : s ≫ b = j' := pullback.lift_fst _ _ _
  have hsq : s ≫ q = p' := pullback.lift_snd _ _ _
  have : s.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change s ≫ b ≫ P ↘ Spec (CommRingCat.of k₀) = _
    rw [← Category.assoc, hsb, comp_over]⟩
  have : IsOpenImmersion b := inferInstanceAs (IsOpenImmersion (pullback.fst p j))
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p j))
  have : IsOpenImmersion (s ≫ b) := hsb.symm ▸ inferInstance
  have : IsOpenImmersion s := IsOpenImmersion.of_comp s b
  have : IsProper (s ≫ q) := hsq.symm ▸ inferInstance
  have : IsProper s := IsProper.of_comp s q
  let eb : (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
      (ProEtaleWeilSheaf.upperStar k₀ l b).mapDerivedCategory ≅
        (ProEtaleWeilSheaf.extensionByZero k₀ l s).mapDerivedCategory :=
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso (nativeOpenFactorRestrictionIso k₀ l s b j' hsb)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (nativeDerivedOpenBaseChangeIso k₀ l q b j p
      (IsPullback.of_hasPullback p j).flip) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eb _ ≪≫
    Functor.isoWhiskerRight
      ((ProEtaleWeilSheaf.extensionByZero k₀ l s).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
        Functor.rightDerivedFunctorNatIso
          (asIso (ProEtaleWeilSheaf.extensionByZeroToLowerStar k₀ l s))) _ ≪≫
    (ProEtaleWeilSheaf.rightDerivedLowerStarCompIso k₀ l s q).symm ≪≫
    Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarCongr k₀ l hsq)

attribute [local irreducible] nativeDerivedOpenBaseChangeIso nativeOpenProperRestrictionIso

private theorem nativeProperBoundaryZero
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)]
    {U' P U X Z : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [P.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (P ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ P) (p' : U' ⟶ U) (j : U ⟶ X) (p : P ⟶ X) (i : Z ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [j.IsOver (Spec (CommRingCat.of k₀))] [p.IsOver (Spec (CommRingCat.of k₀))]
    [i.IsOver (Spec (CommRingCat.of k₀))]
    [IsOpenImmersion j'] [QuasiCompact j'] [IsOpenImmersion j]
    [IsProper p] [IsClosedImmersion i]
    (hc : j' ≫ p = p' ≫ j)
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (K : WeilComplex k₀ l U') :
    IsZero ((ProEtaleWeilSheaf.upperStar k₀ l i).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor.obj
        ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory.obj K.obj))) := by
  let d : pullback p i ⟶ P := pullback.fst p i
  let q : pullback p i ⟶ Z := pullback.snd p i
  let : (pullback p i).Over (Spec (CommRingCat.of k₀)) :=
    ⟨d ≫ P ↘ Spec (CommRingCat.of k₀)⟩
  have : d.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : q.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    dsimp only [q, d]
    rw [← comp_over i (Spec (CommRingCat.of k₀)), ← Category.assoc,
      ← pullback.condition, Category.assoc, comp_over]
    rfl⟩
  have : IsProper q := inferInstanceAs (IsProper (pullback.snd p i))
  have hJK : WeilComplex.objectProperty k₀ l P
      ((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory.obj K.obj) :=
    ⟨(ProEtaleWeilSheaf.extensionByZero k₀ l j').bounded_mapDerivedCategory_obj K.property.1,
      fun n ↦ (WeilSheaf.objectProperty k₀ l P).prop_of_iso
        (((ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategoryHomologyFunctorIso
          n).app K.obj) (WeilSheaf.isAdicConstructibleSheaf_extensionByZero
            j' _ (K.property.2 n))⟩
  let JK : WeilComplex k₀ l P := ⟨_, hJK⟩
  have hdisj : Set.range j'.base ∩ Set.range d.base = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    rintro x ⟨⟨a, rfl⟩, ⟨z, hz⟩⟩
    have he : i.base (q.base z) = j.base (p'.base a) := by
      calc
        i.base (q.base z) = p.base (d.base z) := by
          exact (congrArg (fun f : pullback p i ⟶ X ↦ f.base z)
            (pullback.condition (f := p) (g := i))).symm
        _ = p.base (j'.base a) := by rw [hz]
        _ = j.base (p'.base a) := congrArg (fun f : U' ⟶ X ↦ f.base a) hc
    exact hij.disjoint.le_bot ⟨⟨q.base z, he⟩, ⟨p'.base a, rfl⟩⟩
  have hz : IsZero ((ProEtaleWeilSheaf.upperStar k₀ l d).mapDerivedCategory.obj JK.obj) :=
    DerivedCategory.isZero_mapDerivedCategory_obj_mapDerivedCategory_obj
      (nativeOpenExtension_disjoint k₀ l j' d hdisj) K.obj
  obtain ⟨e⟩ := WeilComplex.nonempty_upperStar_derivedLowerStar_iso_of_isProper
    (f := p) (f' := q) (g := i) (g' := d) inferInstance
    (IsPullback.of_hasPullback p i) JK
  exact ((ProEtaleWeilSheaf.lowerStar k₀ l q).rightDerivedFunctor.map_isZero hz).of_iso
    ((WeilComplex.objectProperty k₀ l Z).ι.mapIso e)

end AlgebraicGeometry

namespace AlgebraicGeometry.WeilComplex

/-- Proper/open interchange for a commutative, possibly non-Cartesian square of finite-type
schemes over a finite field, with proper vertical maps and quasi-compact open horizontal maps.
Both the isomorphism and its inverse are morphisms in the native derived category and hence
include the Weil structure. -/
theorem nonempty_extensionByZero_rightDerivedLowerStar_iso
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {U' X' U X : Scheme.{u}}
    [U'.Over (Spec (CommRingCat.of k₀))] [X'.Over (Spec (CommRingCat.of k₀))]
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (j' : U' ⟶ X') (p' : U' ⟶ U) (p : X' ⟶ X) (j : U ⟶ X)
    [j'.IsOver (Spec (CommRingCat.of k₀))] [p'.IsOver (Spec (CommRingCat.of k₀))]
    [p.IsOver (Spec (CommRingCat.of k₀))] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsProper p] [IsProper p'] [IsOpenImmersion j] [QuasiCompact j]
    [IsOpenImmersion j'] [QuasiCompact j'] (hcomm : j' ≫ p = p' ≫ j) :
    Nonempty
      ((WeilComplex.objectProperty k₀ l U').ι ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory ≅
        (WeilComplex.objectProperty k₀ l U').ι ⋙
          (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
          (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor) := by
  let C : TopologicalSpace.Closeds X :=
    ⟨(Set.range j.base)ᶜ, j.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let Z := (Scheme.IdealSheafData.vanishingIdeal C).subscheme
  let i : Z ⟶ X := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  have : IsClosedImmersion i :=
    inferInstanceAs (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal C).subschemeι)
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ X ↘ Spec (CommRingCat.of k₀)))
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) :=
    inferInstanceAs (QuasiCompact (i ≫ X ↘ Spec (CommRingCat.of k₀)))
  have hrange : Set.range i.base = (Set.range j.base)ᶜ :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (by simp [Scheme.IdealSheafData.coe_support_vanishingIdeal, C])
  have hij : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hrange]
    exact isCompl_compl.symm
  let I := (WeilComplex.objectProperty k₀ l U').ι
  let F := (ProEtaleWeilSheaf.extensionByZero k₀ l j').mapDerivedCategory ⋙
    (ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor
  let R := (ProEtaleWeilSheaf.upperStar k₀ l j).mapDerivedCategory
  let J := (ProEtaleWeilSheaf.extensionByZero k₀ l j).mapDerivedCategory
  let P' := (ProEtaleWeilSheaf.lowerStar k₀ l p').rightDerivedFunctor
  let adj := nativeOpenAdjunction k₀ l j
  have := nativeOpenAdjunction_unit_isIso k₀ l j
  let adj' : J ⊣ R := adj.exactDerivedAdjunction
  let r : F ⋙ R ≅ P' := nativeOpenProperRestrictionIso k₀ l j' p' j p hcomm
  let ε : (I ⋙ F) ⋙ (R ⋙ J) ⟶ (I ⋙ F) ⋙ 𝟭 _ :=
    Functor.whiskerLeft (I ⋙ F) adj'.counit
  have hε : IsIso ε := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.exactDerivedAdjunction_counit_isIso_of_isZero
      (ProEtaleWeilSheaf.upperStar k₀ l i)
      (nativeOpenExtension_disjoint k₀ l j i (by
        rw [Set.inter_comm]
        exact hij.disjoint.eq_bot))
      (ProEtaleWeilSheaf.isZero_of_isZero_upperStar_of_isCompl i j hij)
      (nativeProperBoundaryZero k₀ l j' p' j p i hcomm hij K)
  change Nonempty (I ⋙ P' ⋙ J ≅ I ⋙ F)
  exact ⟨Functor.isoWhiskerLeft I
      (Functor.isoWhiskerRight r.symm J ≪≫ Functor.associator F R J) ≪≫
    (Functor.associator I F (R ⋙ J)).symm ≪≫ asIso ε ≪≫
    Functor.rightUnitor (I ⋙ F)⟩

end AlgebraicGeometry.WeilComplex
