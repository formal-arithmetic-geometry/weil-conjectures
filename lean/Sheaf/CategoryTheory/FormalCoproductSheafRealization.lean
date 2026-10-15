/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Yoneda
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Sheaf realization of formal families over a base

Source: Stacks Project, Hypercoverings, Tags 01G2, 0DB1 and 0DB2.
The construction takes the coproduct of the representable sheaves in the slice over `h_T`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits.FormalCoproduct

/-- The coproduct of the representable sheaves of a family over `T`, with its map to `h_T`.
Source: Stacks Project, Hypercoverings, Tags 0DB1 and 0DB2. -/
noncomputable abbrev sheafRealization {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] (T : C) :
    FormalCoproduct.{u} (Over T) ⥤ Over (J.yoneda.obj T) :=
  (eval _ _).obj (Over.post J.yoneda)

/-- The given Yoneda-image coproduct is also a coproduct in the slice.
Source: Stacks Project, Hypercoverings, Tag 0DB2: colimits in a slice are created by forgetting. -/
noncomputable def isColimitSheafCofan {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [J.Subcanonical] {T : C}
    (Q : FormalCoproduct.{u} (Over T)) (a : Cofan Q.obj)
    (h : IsColimit (Cofan.mk (J.yoneda.obj a.pt.left)
      (fun i : Q.I ↦ J.yoneda.map (a.inj i).left))) :
    IsColimit (Cofan.mk ((Over.post J.yoneda).obj a.pt)
      (fun i : Q.I ↦ (Over.post J.yoneda).map (a.inj i))) := by
  apply isColimitOfReflects (Over.forget (J.yoneda.obj T))
  exact (isColimitMapCoconeCofanMkEquiv _ _ _).symm h

private noncomputable def restrictedFamilyYoneda (C : Type u) [SmallCategory C] :
    FormalCoproduct.{u} C ⥤ Cᵒᵖ ⥤ Type u :=
  CategoryTheory.yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj (incl C).op

private noncomputable def restrictedFamilyCofan {C : Type u} [SmallCategory C]
    (Q : FormalCoproduct.{u} C) : Cofan (fun i : Q.I ↦ CategoryTheory.yoneda.obj (Q.obj i)) :=
  Cofan.mk ((restrictedFamilyYoneda C).obj Q) (fun i ↦
    { app := fun U ↦ ↾fun g ↦ Hom.fromIncl i g })

set_option backward.isDefEq.respectTransparency false in
private noncomputable def isColimitRestrictedFamilyCofan {C : Type u} [SmallCategory C]
    (Q : FormalCoproduct.{u} C) : IsColimit (restrictedFamilyCofan Q) := by
  refine Cofan.IsColimit.mk _ (fun s ↦
    { app := fun U ↦ ↾fun f ↦ (s.inj (f.f PUnit.unit)).app U (f.φ PUnit.unit)
      naturality := ?_ }) ?_ ?_
  · intro U V f
    ext g
    exact ConcreteCategory.congr_hom ((s.inj (g.f PUnit.unit)).naturality f) (g.φ PUnit.unit)
  · intro s i
    ext U g
    rfl
  · intro s m hm
    ext U f
    change ((incl C).obj U.unop ⟶ Q) at f
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (hm (f.f PUnit.unit)) U) (f.φ PUnit.unit)
    change m.app U (Hom.fromIncl _ _) = _ at h
    exact (congrArg (fun t ↦ m.app U t) (Hom.fromIncl_asSigma f)).symm.trans h

private noncomputable def familyYonedaIso (C : Type u) [SmallCategory C] :
    FormalCoproduct.yoneda (C := C) ≅ restrictedFamilyYoneda C := by
  let b (Q : FormalCoproduct.{u} C) :
      FormalCoproduct.yoneda.obj Q ≅ (restrictedFamilyYoneda C).obj Q :=
    (coproductIsCoproduct _).coconePointUniqueUpToIso
      (isColimitRestrictedFamilyCofan Q)
  have hb (Q : FormalCoproduct.{u} C) (i : Q.I) :
      Sigma.ι (fun i ↦ CategoryTheory.yoneda.obj (Q.obj i)) i ≫ (b Q).hom =
        (restrictedFamilyCofan Q).inj i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
      (isColimitRestrictedFamilyCofan Q) (Discrete.mk i)
  refine NatIso.ofComponents b ?_
  intro Q R f
  apply Sigma.hom_ext
  intro i
  simp only [FormalCoproduct.yoneda, eval_obj_map, Sigma.ι_desc_assoc,
    Category.assoc, Function.comp_def]
  rw [hb R, ← Category.assoc, hb Q]
  ext U g
  rfl

private theorem familyYoneda_preservesLimits (C : Type u) [SmallCategory C] :
    PreservesLimits (FormalCoproduct.yoneda (C := C)) := by
  have : PreservesLimits (restrictedFamilyYoneda C) := by
    dsimp [restrictedFamilyYoneda]
    infer_instance
  exact preservesLimits_of_natIso (familyYonedaIso C).symm

private def familyToOver {C : Type u} [SmallCategory C] (T : C) :
    FormalCoproduct.{u} (Over T) ⥤ Over ((incl C).obj T) where
  obj Q := Over.mk (Y := ⟨Q.I, fun i ↦ (Q.obj i).left⟩)
    ⟨fun _ ↦ PUnit.unit, fun i ↦ (Q.obj i).hom⟩
  map f := Over.homMk ⟨f.f, fun i ↦ (f.φ i).left⟩ (by
    refine hom_ext ?_ ?_
    · rfl
    · intro i
      simp [Over.w (f.φ i)])

private def overToFamily {C : Type u} [SmallCategory C] (T : C) :
    Over ((incl C).obj T) ⥤ FormalCoproduct.{u} (Over T) where
  obj Q := ⟨Q.left.I, fun i ↦ Over.mk (Q.hom.φ i)⟩
  map {Q R} f := ⟨f.left.f, fun i ↦ Over.homMk (f.left.φ i) (by
    obtain ⟨_, h⟩ := (hom_ext_iff _ _).mp (Over.w f)
    simpa [incl] using h i)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def familyOverEquiv {C : Type u} [SmallCategory C] (T : C) :
    FormalCoproduct.{u} (Over T) ≌ Over ((incl C).obj T) :=
  Equivalence.mk (familyToOver T) (overToFamily T)
    (NatIso.ofComponents
      (fun Q ↦ isoOfComponents (Equiv.refl _) (fun i ↦ Over.isoMk (Iso.refl _)))
      (by
        intro Q R f
        ext i
        · rfl
        · simp [familyToOver, overToFamily, isoOfComponents, Over.homMk_left,
            Over.isoMk_hom_left]))
    (NatIso.ofComponents
      (fun Q ↦ Over.isoMk (Iso.refl _) (by
        refine hom_ext ?_ ?_
        · funext i
          exact Subsingleton.elim (α := PUnit) _ _
        · intro i
          simp [familyToOver, overToFamily, incl]))
      (by
        intro Q R f
        ext i
        · rfl
        · simp [familyToOver, overToFamily, Over.homMk_left, Over.isoMk_hom_left]))

private noncomputable def isColimitSelf {D : Type u} [SmallCategory D]
    (Q : FormalCoproduct.{u} D) :
    IsColimit (Cofan.mk Q (fun i : Q.I ↦ Hom.fromIncl i (𝟙 (Q.obj i)))) :=
  (coproductIsCoproduct Q.toFun).ofIsoColimit
    (Cocone.ext (coproductIsoSelf Q) (fun i ↦ ι_comp_coproductIsoSelf_hom Q i.as))

set_option backward.isDefEq.respectTransparency false in
private noncomputable def evalExtensionIso
    {D : Type u} [SmallCategory D] {E : Type*} [Category* E] [HasCoproducts.{u} E]
    (G : FormalCoproduct.{u} D ⥤ E) (H : D ⥤ E)
    (hG : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G)
    (e : incl D ⋙ G ≅ H) : G ≅ (eval _ _).obj H := by
  let c (Q : FormalCoproduct.{u} D) :=
    Cofan.mk (G.obj Q) (fun i : Q.I ↦ G.map (Hom.fromIncl i (𝟙 _)))
  have hc (Q : FormalCoproduct.{u} D) : IsColimit (c Q) := by
    have := hG Q.I
    exact isColimitCofanMkObjOfIsColimit G _ _ (isColimitSelf Q)
  let d (Q : FormalCoproduct.{u} D) :=
    Cofan.mk (∐ fun i : Q.I ↦ H.obj (Q.obj i))
      (fun i : Q.I ↦ (e.app (Q.obj i)).hom ≫ Sigma.ι (fun i : Q.I ↦ H.obj (Q.obj i)) i)
  have hd (Q : FormalCoproduct.{u} D) : IsColimit (d Q) := by
    let ei : Discrete.functor (fun i : Q.I ↦ G.obj ((incl D).obj (Q.obj i))) ≅
        Discrete.functor (fun i : Q.I ↦ H.obj (Q.obj i)) :=
      Discrete.natIso (fun i ↦ e.app (Q.obj i.as))
    exact (IsColimit.precomposeHomEquiv ei _).symm (coproductIsCoproduct _)
  let b (Q : FormalCoproduct.{u} D) := (hc Q).coconePointUniqueUpToIso (hd Q)
  have hb (Q : FormalCoproduct.{u} D) (i : Q.I) :
      G.map (Hom.fromIncl i (𝟙 _)) ≫ (b Q).hom =
        (e.app (Q.obj i)).hom ≫ Sigma.ι (fun i : Q.I ↦ H.obj (Q.obj i)) i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (hc Q) (hd Q) (Discrete.mk i)
  refine NatIso.ofComponents b ?_
  intro Q R f
  apply Cofan.IsColimit.hom_ext (hc Q)
  intro i
  change G.map (Hom.fromIncl i (𝟙 _)) ≫ G.map f ≫ (b R).hom =
    G.map (Hom.fromIncl i (𝟙 _)) ≫ (b Q).hom ≫ ((eval _ _).obj H).map f
  rw [← G.map_comp_assoc]
  have h : Hom.fromIncl i (𝟙 _) ≫ f =
      (incl D).map (f.φ i) ≫ Hom.fromIncl (f.f i) (𝟙 _) := by
    ext j
    · rfl
    · simp [Hom.fromIncl, incl]
  rw [h, G.map_comp, Category.assoc, hb R]
  trans (e.app (Q.obj i)).hom ≫ H.map (f.φ i) ≫
    Sigma.ι (fun i : R.I ↦ H.obj (R.obj i)) (f.f i)
  · exact e.hom.naturality_assoc (f.φ i) _
  · simp only [eval_obj_map, Function.comp_def, ← Category.assoc]
    rw [hb Q]
    simp [Category.assoc]

private theorem overPost_preservesCoproducts
    {D : Type*} [Category* D] [HasCoproducts.{u} D]
    {E : Type*} [Category* E] [HasCoproducts.{u} E]
    (G : D ⥤ E) (X : D) (I : Type u)
    [PreservesColimitsOfShape (Discrete I) G] :
    PreservesColimitsOfShape (Discrete I) (Over.post G (X := X)) := by
  have : PreservesColimitsOfShape (Discrete I)
      (Over.post G (X := X) ⋙ Over.forget (G.obj X)) := by
    change PreservesColimitsOfShape (Discrete I) (Over.forget X ⋙ G)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (Over.post G) (Over.forget (G.obj X))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Realizing formal families of representables over `T` preserves finite limits.
Source: Stacks Project, Hypercoverings, Tag 01G2(2) and Tag 0DB1.

Proof: the formal-family Yoneda functor is the ordinary Yoneda functor on formal
coproducts restricted to singleton families. The coproduct universal property and
the equivalence between maps from a singleton and pairs `(i, U ⟶ Q_i)` give the
natural comparison isomorphism. Both ordinary Yoneda and restriction preserve
limits, so formal-family Yoneda does too, as in Tag 01G2(2).

A formal family over `T` is equivalently a formal family in `C` with a morphism to
the singleton family `{T}`. Use this equivalence, apply formal-family Yoneda on
the slice, and then apply sheafification on the slice. These functors preserve
finite limits. Identify the resulting base with `h_T` by the singleton-coproduct
isomorphism and the sheafification counit; changing the base along an isomorphism
also preserves limits. The resulting composite preserves coproducts and agrees
with sheaf Yoneda on singleton families. Since every formal family is the
coproduct of its singleton families, the coproduct universal property gives a
natural isomorphism from this composite to `sheafRealization`. Transporting
finite-limit preservation along that isomorphism completes the proof.
(blueprint: lem-weil-pbc-formal-coproduct-sheaf-finite-limits). -/
theorem sheafRealization_preservesFiniteLimits {C : Type u} [SmallCategory C]
    [HasPullbacks C] (J : GrothendieckTopology C) [J.Subcanonical] (T : C) :
    PreservesFiniteLimits (sheafRealization J T) := by
  let H := FormalCoproduct.yoneda (C := C)
  let S := presheafToSheaf J (Type u)
  have : PreservesLimits H := familyYoneda_preservesLimits C
  let q : incl C ⋙ H ≅ CategoryTheory.yoneda :=
    (evalCompInclIsoId C (Cᵒᵖ ⥤ Type u)).app CategoryTheory.yoneda
  let r : CategoryTheory.yoneda ⋙ S ≅ J.yoneda :=
    (Functor.associator J.yoneda (sheafToPresheaf J (Type u)) S) ≪≫
      Functor.isoWhiskerLeft J.yoneda (asIso (sheafificationAdjunction J (Type u)).counit) ≪≫
      J.yoneda.rightUnitor
  let z : incl C ⋙ (H ⋙ S) ≅ J.yoneda :=
    (Functor.associator (incl C) H S).symm ≪≫ Functor.isoWhiskerRight q S ≪≫ r
  let G := (familyOverEquiv T).functor ⋙ Over.post (H ⋙ S) ⋙ Over.map (z.app T).hom
  have : PreservesFiniteLimits (H ⋙ S) := comp_preservesFiniteLimits H S
  have : PreservesFiniteLimits
      (Over.post (H ⋙ S) (X := (incl C).obj T) ⋙ Over.map (z.app T).hom) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have hG (I : Type u) : PreservesColimitsOfShape (Discrete I) G := by
    have : PreservesColimitsOfShape (Discrete I) H := by
      dsimp [H, FormalCoproduct.yoneda]
      infer_instance
    have : PreservesColimitsOfShape (Discrete I) (Over.post (H ⋙ S)
        (X := (incl C).obj T)) := overPost_preservesCoproducts _ _ _
    dsimp [G]
    infer_instance
  let e : incl (Over T) ⋙ G ≅ Over.post J.yoneda :=
    NatIso.ofComponents (fun X ↦ Over.isoMk (z.app X.left)
      (by exact (z.hom.naturality X.hom).symm))
      (by
        intro X Y f
        apply Over.OverMorphism.ext
        exact z.hom.naturality f.left)
  exact preservesFiniteLimits_of_natIso (evalExtensionIso G (Over.post J.yoneda) hG e)

end CategoryTheory.Limits.FormalCoproduct
