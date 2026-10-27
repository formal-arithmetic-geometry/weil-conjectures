/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q9
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Sheaf.Paper.BarrettIndRealization
import Sheaf.Paper.SfCommonStageDirectImage
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact

/-! # Higher proper images of represented ind-sheaves

Source: SGA 4, XVII, §5; Bhatt--Scholze, §6.7--6.8.
(blueprint: lem-zl-ind-proper-higher-representability).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

private theorem lift_fixed_pair
    {C B : Type*} [Category C] [Category B]
    {F : C ⥤ C} {Q : B ⥤ B} {L : C ⥤ B}
    (e : L ⋙ Q ≅ F ⋙ L) (ff : L.FullyFaithful)
    (K : CategoryTheory.Endofunctor.IsoAlgebra Q) (A : C)
    (i : L.obj A ≅ K.carrier) :
    ∃ H : CategoryTheory.Endofunctor.IsoAlgebra F,
      Nonempty ((CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso e).obj H ≅ K) := by
  let t : L.obj (F.obj A) ≅ L.obj A :=
    (e.app A).symm ≪≫ Q.mapIso i ≪≫ K.str ≪≫ i.symm
  let s : F.obj A ≅ A := ff.preimageIso t
  let H := CategoryTheory.Endofunctor.IsoAlgebra.mk A s
  refine ⟨H, ⟨ObjectProperty.isoMk _ (CategoryTheory.Endofunctor.Algebra.isoMk i ?_)⟩⟩
  change Q.map i.hom ≫ K.str.hom = (e.app A ≪≫ L.mapIso s).hom ≫ i.hom
  have hs : L.map s.hom = t.hom := ff.map_preimage _
  simp only [Iso.trans_hom, Functor.mapIso_hom, hs, t, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_app_assoc]

private theorem rightAdjoint_restriction
    {C D C' D' E : Type*} [Category C] [Category D] [Category C'] [Category D']
    [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ E} {R' : E ⥤ C'}
    {T : D' ⥤ E} {U : E ⥤ D'}
    (a : L ⊣ R) (a' : L' ⊣ R') (b : T ⊣ U) (J : C ⥤ C') (K : D ⥤ D')
    (hJ : J.FullyFaithful) (hK : K.FullyFaithful)
    (e : L ⋙ K ⋙ T ≅ J ⋙ L')
    (detect : ∀ {M N : C'} (f : M ⟶ N),
      (∀ B : C, Function.Bijective (fun g : J.obj B ⟶ M ↦ g ≫ f)) → IsIso f)
    (A : D) (M : E) (i : K.obj A ≅ U.obj M) :
    Nonempty (J.obj (R.obj A) ≅ R'.obj M) := by
  let c : L'.obj (J.obj (R.obj A)) ⟶ M :=
    (e.app (R.obj A)).inv ≫ (b.homEquiv _ _).symm
      (K.map (a.counit.app A) ≫ i.hom)
  let f : J.obj (R.obj A) ⟶ R'.obj M := a'.homEquiv _ _ c
  have hf : IsIso f := by
    apply detect f
    intro B
    let t : (J.obj B ⟶ J.obj (R.obj A)) ≃ (J.obj B ⟶ R'.obj M) :=
      hJ.homEquiv.symm |>.trans ((a.homEquiv B A).symm) |>.trans hK.homEquiv |>.trans
        (Iso.homCongr (Iso.refl _) i) |>.trans (b.homEquiv _ _).symm |>.trans
        (Iso.homCongr (e.app B) (Iso.refl _)) |>.trans (a'.homEquiv _ _)
    have ht (g : J.obj B ⟶ J.obj (R.obj A)) : t g = g ≫ f := by
      obtain ⟨h, rfl⟩ := hJ.map_surjective g
      dsimp only [t, Equiv.trans_apply, Functor.FullyFaithful.homEquiv,
        Equiv.symm, Equiv.coe_fn_mk, Iso.homCongr]
      rw [hJ.preimage_map]
      change a'.homEquiv _ _ ((e.app B).inv ≫
        (b.homEquiv _ _).symm ((Iso.refl _).inv ≫
          K.map ((a.homEquiv B A).symm h) ≫ i.hom) ≫ (Iso.refl _).hom) =
        J.map h ≫ a'.homEquiv _ _ c
      rw [a.homEquiv_counit]
      simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id, Category.id_comp,
        Functor.map_comp, Category.assoc]
      rw [b.homEquiv_naturality_left_symm, ← a'.homEquiv_naturality_left]
      congr 1
      dsimp only [c]
      rw [← Category.assoc]
      simpa only [Category.assoc, Functor.comp_map, Functor.comp_obj, Iso.app_inv] using
        congrArg (fun z ↦ z ≫ (b.homEquiv _ _).symm
          (K.map (a.counit.app A) ≫ i.hom)) (e.inv.naturality h).symm
    have heq : (fun g ↦ g ≫ f) = t := funext (fun g ↦ (ht g).symm)
    rw [heq]
    exact t.bijective
  exact ⟨asIso f⟩

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

private theorem small_pairs_essSurj (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : Endofunctor.IsoAlgebra (zlSmallFrobenius D l hl Ω X₀)) :
    ∃ H : sfCommonStageWeilSheaf D l hl X₀ Ω,
      Nonempty ((zlWeilSmallPairs D l hl Ω X₀).obj H ≅ K) := by
  let H : sfCommonStageWeilSheaf D l hl X₀ Ω :=
    ⟨Endofunctor.IsoAlgebra.mk (AsSmall.down.obj K.carrier).obj
      { hom := K.str.hom.down.hom
        inv := K.str.inv.down.hom
        hom_inv_id := congrArg (fun f ↦ f.down.hom) K.str.hom_inv_id
        inv_hom_id := congrArg (fun f ↦ f.down.hom) K.str.inv_hom_id },
      (AsSmall.down.obj K.carrier).property⟩
  have hc : ((zlWeilSmallPairs D l hl Ω X₀).obj H).carrier = K.carrier := by
    trans (⟨⟨H.obj.carrier, H.property⟩⟩ : zlSmallHeart D l Ω hl X₀)
    · exact (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose_spec.1 H
    · apply ULift.ext
      rfl
  have hs : HEq ((zlWeilSmallPairs D l hl Ω X₀).obj H).str.hom.down.hom
      K.str.hom.down.hom :=
    (zlWeilSmallPairs_existsUnique D l hl Ω X₀).exists.choose_spec.2.1 H
  have obj_ext (A B : Endofunctor.IsoAlgebra (zlSmallFrobenius D l hl Ω X₀))
      (h : A.carrier = B.carrier)
      (ht : HEq A.str.hom.down.hom B.str.hom.down.hom) : A = B := by
    rcases A with ⟨⟨a, sa⟩, ha⟩
    rcases B with ⟨⟨b, sb⟩, hb⟩
    change a = b at h
    cases h
    have hstr : sa = sb := by
      apply ULift.ext
      apply ObjectProperty.hom_ext
      exact eq_of_heq ht
    cases hstr
    rfl
  exact ⟨H, ⟨eqToIso (obj_ext _ _ hc hs)⟩⟩

private theorem represented_carrier_lifts (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : zlIndWeilHeart D l hl Ω X₀) (A : zlSmallHeart D l Ω hl X₀)
    (i : (Ind.yoneda (C := zlSmallHeart D l Ω hl X₀)).obj A ≅ K.carrier) :
    ∃ H : sfCommonStageWeilSheaf D l hl X₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω X₀).obj H ≅ K) := by
  obtain ⟨P, ⟨eP⟩⟩ := lift_fixed_pair
    (zlIndMapIso (zlSmallFrobenius D l hl Ω X₀)) Ind.yoneda.fullyFaithful K A i
  obtain ⟨H, ⟨eH⟩⟩ := small_pairs_essSurj D l hl Ω X₀ P
  exact ⟨H, ⟨(Endofunctor.IsoAlgebra.mapOfNatIso
    (zlIndMapIso (zlSmallFrobenius D l hl Ω X₀))).mapIso eH ≪≫ eP⟩⟩

private def free_derived_adj (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [HasDerivedCategory (Ind (zlSmallHeart D l Ω hl X₀))]
    [HasDerivedCategory (zlIndWeilHeart D l hl Ω X₀)] :
    zlIndDerivedFree D l hl Ω X₀ ⊣ zlIndDerivedForget D l hl Ω X₀ := by
  obtain ⟨ha, hlim, hcolim, he⟩ := zlIndFrobenius_exact D l hl Ω X₀
  let := ha
  let := hlim
  let := hcolim
  let := he
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let Q := zlIndMap (zlSmallFrobenius D l hl Ω X₀)
  let : (Endofunctor.IsoAlgebra.Free.functor Q).IsLeftAdjoint :=
    (Endofunctor.IsoAlgebra.Free.adjunction Q).isLeftAdjoint
  dsimp only [zlIndDerivedFree, zlIndDerivedForget]
  change (Endofunctor.IsoAlgebra.Free.functor Q).mapDerivedCategoryPlus ⊣
    (Endofunctor.IsoAlgebra.forget Q).mapDerivedCategoryPlus
  exact ((Endofunctor.IsoAlgebra.Free.adjunction Q).derivedPlus).ofNatIsoRight
    (Endofunctor.IsoAlgebra.forget Q).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus

private def weil_derived_adj {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [HasDerivedCategory (zlIndWeilHeart D l hl Ω X₀)]
    [HasDerivedCategory (zlIndWeilHeart D l hl Ω Y₀)] (f : X₀ ⟶ Y₀) :
    zlIndDerivedPull D l hl Ω f ⊣ (zlIndWeilPush D l hl Ω f).rightDerivedFunctorPlus := by
  obtain ⟨ha, hlim, hcolim⟩ := zlIndWeilPull_exact D l hl Ω f
  let := ha
  let := hlim
  let := hcolim
  let := zlIndWeilPull_isLeftAdjoint D l hl Ω f
  have a : zlIndWeilPull D l hl Ω f ⊣ zlIndWeilPush D l hl Ω f :=
    Adjunction.ofIsLeftAdjoint _
  simpa only [zlIndDerivedPull] using a.derivedPlus

/-- Higher proper direct images of represented Weil sheaves remain represented.
This statement concerns ordinary proper image alone, with no compactification or open leg.
Source: SGA 4, XVII, proper-image finiteness; Bhatt--Scholze, 6.8.14--6.8.15;
O. Barrett, The derived category of the abelian category of constructible sheaves,
arXiv:2005.10859, Theorem 1.1; Kashiwara--Schapira, Categories and Sheaves, 15.3
(blueprint: lem-zl-ind-proper-higher-representability).

Proof: use the Barrett realization of the ordinary constructible categories in
bounded-below derived ind-hearts. Its inverse-image comparison commutes with free
Frobenius induction. Compose the derived free-forgetful adjunction with the derived
inverse-image/direct-image adjunction. On represented test objects, the two free
adjunctions and full faithfulness identify the resulting Hom bijections with the
constructible inverse-image/direct-image adjunction. The generic adjunction
comparison below constructs the comparison arrow from the counit and proves it
invertible using those test objects. Thus the underlying derived higher image is
the realization of the existing constructible derived image. Its cohomology is
represented. Exact forgetting commutes with cohomology, and the standard
single-object comparison identifies it with the classical rightDerived n.
Finally lift the resulting Frobenius isomorphism through the fully faithful
Yoneda embedding and undo the small presentation. This last step does not require
Frobenius-equivariance of a separately chosen geometric cohomology comparison.
The Barrett realization, which is independent of direct image, is the remaining
separate source theorem -/
theorem zlIndWeilProperHigher_representable {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (p₀ : X₀ ⟶ Y₀) [IsProper p₀.left] (n : ℕ)
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    ∃ H : sfCommonStageWeilSheaf D l hl Y₀ Ω,
      Nonempty ((zlWeilIndEmbedding D l hl Ω Y₀).obj H ≅
        ((zlIndWeilPush D l hl Ω p₀).rightDerived n).obj
          ((zlWeilIndEmbedding D l hl Ω X₀).obj G)) := by
  let := HasDerivedCategory.standard (Ind (zlSmallHeart D l Ω hl X₀))
  let := HasDerivedCategory.standard (Ind (zlSmallHeart D l Ω hl Y₀))
  let := HasDerivedCategory.standard (zlIndWeilHeart D l hl Ω X₀)
  let := HasDerivedCategory.standard (zlIndWeilHeart D l hl Ω Y₀)
  obtain ⟨haX, hlX, hcX, heX⟩ := zlIndFrobenius_exact D l hl Ω X₀
  obtain ⟨haY, hlY, hcY, heY⟩ := zlIndFrobenius_exact D l hl Ω Y₀
  let := hlX
  let := hcX
  let := heX
  let := hlY
  let := hcY
  let := heY
  let : Abelian (zlIndWeilHeart D l hl Ω X₀) := zlIndWeilHeartAbelian D l hl Ω X₀
  let : Preadditive (zlIndWeilHeart D l hl Ω X₀) :=
    (zlIndWeilHeartAbelian D l hl Ω X₀).toPreadditive
  let : Abelian (zlIndWeilHeart D l hl Ω Y₀) := zlIndWeilHeartAbelian D l hl Ω Y₀
  let : Preadditive (zlIndWeilHeart D l hl Ω Y₀) :=
    (zlIndWeilHeartAbelian D l hl Ω Y₀).toPreadditive
  obtain ⟨JX, JY, ⟨hJX⟩, ⟨hJY⟩, heart, homology, ⟨e⟩, detect⟩ :=
    zlBarrettIndRealization D l hl Ω p₀
  let K := (zlWeilIndEmbedding D l hl Ω X₀).obj G
  let A := ((zlWeilSmallPairs D l hl Ω X₀).obj G).carrier
  let M := (DerivedCategory.Plus.singleFunctor _ 0).obj K
  let UX := Endofunctor.IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω X₀))
  let UY := Endofunctor.IsoAlgebra.forget (zlIndMap (zlSmallFrobenius D l hl Ω Y₀))
  have i : JX.obj (AsSmall.down.obj A).obj ≅
      (zlIndDerivedForget D l hl Ω X₀).obj M :=
    (heart A).some ≪≫ (by
      simpa only [zlIndDerivedForget, UX, M, K, A, zlWeilIndEmbedding, Functor.comp_obj,
        Endofunctor.IsoAlgebra.forget_obj, Endofunctor.IsoAlgebra.mapOfNatIso_obj_carrier]
        using
        ((UX.mapDerivedCategoryPlusSingleFunctor 0).app K).symm)
  obtain ⟨eR⟩ := rightAdjoint_restriction
    (sfModelDerivedAdjunction D l hl Ω p₀)
    ((free_derived_adj D l hl Ω Y₀).comp (weil_derived_adj D l hl Ω p₀))
    (free_derived_adj D l hl Ω X₀) JY JX hJY hJX e detect
    (AsSmall.down.obj A).obj M i
  obtain ⟨B, ⟨hB⟩⟩ := homology
    ((sfModelDerivedPush D l hl Ω p₀).obj (AsSmall.down.obj A).obj) n
  let h : Ind.yoneda.obj B ≅
      (((zlIndWeilPush D l hl Ω p₀).rightDerived n).obj K).carrier :=
    hB ≪≫ (DerivedCategory.Plus.homologyFunctor _ (n : ℤ)).mapIso eR ≪≫
      (by simpa only [zlIndDerivedForget, UY, M, Functor.comp_obj] using
        ((UY.mapDerivedCategoryPlusHomologyFunctorIso n).app
          ((zlIndWeilPush D l hl Ω p₀).rightDerivedFunctorPlus.obj M)).symm) ≪≫
      UY.mapIso ((zlIndWeilPush D l hl Ω p₀)
        |>.homologyRightDerivedFunctorPlusObjSingleFunctorIso K n)
  exact represented_carrier_lifts D l hl Ω Y₀ _ B h

end WeilConjectures
