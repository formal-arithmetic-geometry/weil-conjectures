/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.CategoryTheory.RingedToposBinaryDescentDefs
import Sheaf.CategoryTheory.RingedToposDirectImageRestriction
import Sheaf.Algebra.Homology.SitePerfectModelRestriction

/-! # Restriction of the binary direct-image fibre

Source: Stacks Project, Cohomology, Tag 08DG.
-/

@[expose] public section
universe u v r w s
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Preadditive
namespace CategoryTheory
set_option autoImplicit false
set_option synthInstance.maxSize 4096

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_projection_isIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {G X Y Z : D} (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso b]
    (f : G ⟶ X ⊞ Y) (h : Z ⟶ G⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (biprod.desc a b) h ∈ distTriang D) :
    IsIso (f ≫ biprod.fst) := by
  let d := biprod.desc a b
  let T := Triangle.mk f d h
  have ht : T ∈ distTriang D := hT
  have hs : (inv b ≫ biprod.inr) ≫ d = 𝟙 _ := by
    simp [d]
  let : IsSplitEpi d := IsSplitEpi.mk' ⟨_, hs⟩
  have hh : T.mor₃ = 0 := T.mor₃_eq_zero_of_epi₂ ht (show Epi d from inferInstance)
  have : Mono f := T.mono₁ ht hh
  have : Mono (f ≫ biprod.fst) := by
    rw [mono_iff_cancel_zero]
    intro W k hk
    apply (cancel_mono f).mp
    apply biprod.hom_ext
    · simpa only [Category.assoc, zero_comp] using hk
    · have hz := congrArg (fun z ↦ k ≫ z) (comp_distTriang_mor_zero₁₂ T ht)
      change k ≫ (f ≫ biprod.desc a b) = k ≫ 0 at hz
      have hd : biprod.desc a b = biprod.fst ≫ a + biprod.snd ≫ b := by
        apply biprod.hom_ext' <;> simp
      rw [hd, Preadditive.comp_add, Preadditive.comp_add] at hz
      simp only [← Category.assoc, hk, zero_comp, zero_add, comp_zero] at hz
      apply (cancel_mono b).mp
      simpa only [Category.assoc, zero_comp] using hz
  let l : X ⟶ X ⊞ Y := biprod.lift (𝟙 X) (-a ≫ inv b)
  have hl : l ≫ d = 0 := by simp [l, d]
  obtain ⟨t, ht⟩ := T.coyoneda_exact₂ hT l hl
  change l = t ≫ f at ht
  have ht' : t ≫ (f ≫ biprod.fst) = 𝟙 X := by
    rw [← Category.assoc, ← ht]
    simp [l]
  let : IsSplitEpi (f ≫ biprod.fst) := IsSplitEpi.mk' ⟨t, ht'⟩
  exact isIso_of_mono_of_isSplitEpi _

set_option backward.isDefEq.respectTransparency false in
private theorem fibre_projection_snd_isIso
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {G X Y Z : D} (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso a]
    (f : G ⟶ X ⊞ Y) (h : Z ⟶ G⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (biprod.desc a b) h ∈ distTriang D) :
    IsIso (f ≫ biprod.snd) := by
  let e := biprod.braiding X Y
  have ht : Triangle.mk (f ≫ e.hom) (biprod.desc b a) h ∈ distTriang D := by
    apply isomorphic_distinguished _ hT _
    refine Triangle.isoMk _ _ (Iso.refl G) e.symm (Iso.refl Z) ?_ ?_ ?_
    · change (f ≫ e.hom) ≫ e.inv = 𝟙 G ≫ f
      rw [Category.assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
    · change biprod.desc b a ≫ 𝟙 Z = e.inv ≫ biprod.desc a b
      apply biprod.hom_ext' <;> simp [e]
    · change h ≫ (shiftFunctor D 1).map (𝟙 G) = 𝟙 Z ≫ h
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  have hi := fibre_projection_isIso b a (f ≫ e.hom) h ht
  simpa [e, Category.assoc] using hi

attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
set_option backward.isDefEq.respectTransparency false in
private theorem map_fibre_projection_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasShift D ℤ] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {G X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso (F.map b)]
    (f : G ⟶ X ⊞ Y) (h : Z ⟶ G⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (biprod.desc a b) h ∈ distTriang C) :
    IsIso (F.map (f ≫ biprod.fst)) := by
  let e := F.mapBiprod X Y
  let T := F.mapTriangle.obj (Triangle.mk f (biprod.desc a b) h)
  have ht := F.map_distinguished _ hT
  have ht' : Triangle.mk (F.map f ≫ e.hom)
      (biprod.desc (F.map a) (F.map b)) T.mor₃ ∈ distTriang D := by
    apply isomorphic_distinguished _ ht _
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    · change (F.map f ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map f
      simp
    · change biprod.desc (F.map a) (F.map b) ≫ 𝟙 _ = e.inv ≫ F.map (biprod.desc a b)
      apply biprod.hom_ext'
      · simp [e, ← F.map_comp]
      · simp [e, ← F.map_comp]
    · change T.mor₃ ≫ (shiftFunctor D 1).map (𝟙 _) = 𝟙 _ ≫ T.mor₃
      simp
  have hi := fibre_projection_isIso (F.map a) (F.map b) (F.map f ≫ e.hom) T.mor₃ ht'
  simpa only [e, Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst,
    ← F.map_comp] using hi
set_option backward.isDefEq.respectTransparency false in
private theorem map_fibre_projection_snd_isIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasShift C ℤ] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [HasShift D ℤ] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated C] [Pretriangulated D]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    {G X Y Z : C} (a : X ⟶ Z) (b : Y ⟶ Z) [IsIso (F.map a)]
    (f : G ⟶ X ⊞ Y) (h : Z ⟶ G⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f (biprod.desc a b) h ∈ distTriang C) :
    IsIso (F.map (f ≫ biprod.snd)) := by
  let e := F.mapBiprod X Y
  let T := F.mapTriangle.obj (Triangle.mk f (biprod.desc a b) h)
  have ht := F.map_distinguished _ hT
  have ht' : Triangle.mk (F.map f ≫ e.hom)
      (biprod.desc (F.map a) (F.map b)) T.mor₃ ∈ distTriang D := by
    apply isomorphic_distinguished _ ht _
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    · change (F.map f ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ F.map f
      simp
    · change biprod.desc (F.map a) (F.map b) ≫ 𝟙 _ = e.inv ≫ F.map (biprod.desc a b)
      apply biprod.hom_ext'
      · simp [e, ← F.map_comp]
      · simp [e, ← F.map_comp]
    · change T.mor₃ ≫ (shiftFunctor D 1).map (𝟙 _) = 𝟙 _ ≫ T.mor₃
      simp
  have hi := fibre_projection_snd_isIso (F.map a) (F.map b) (F.map f ≫ e.hom) T.mor₃ ht'
  simpa only [e, Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd,
    ← F.map_comp] using hi

set_option backward.isDefEq.respectTransparency false in
private noncomputable def restrictionDerivedIso
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (T : DerivedCategory A ⥤ DerivedCategory B)
    (q : DerivedCategory.Q ⋙ T ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    F.mapDerivedCategory ≅ T := by
  let : Localization.Lifting DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) T := ⟨q⟩
  exact Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory T (Iso.refl _)

set_option maxHeartbeats 800000 in
-- The five localized module categories require simultaneous instance elaboration.
/-- The projections from a direct-image fibre are isomorphisms on the two opens.
Source: Stacks Project, Cohomology, Tag 08DG (lemma-glue), restricted-cone calculation.
(blueprint: lem-sp-ringed-topos-fibre-restriction).

Proof: Exact slice restriction induces a triangulated functor on derived categories.
Lift qU and qV through localization to identify these functors with the displayed
restrictions, transporting their shift structures and triangulatedness. The direct-image
restriction lemma gives invertible counits and invertible cross-restrictions of the two
adjunction mates. Consequently on U the second component of the restricted middle
arrow is invertible; on V its first component is invertible (also using c).

In any distinguished triangle G → X ⊕ Y → Z → G[1], if the second component b of
the middle arrow (a,b) is invertible, that arrow is split epic. Its connecting arrow
is zero, so the first arrow f is monic. The relation f(a,b)=0 shows that f followed
by projection to X is monic: an element annihilated by that projection has its second
projection annihilated by b. The graph map (1,-a b⁻¹) is killed by (a,b), hence factors
through f by exactness of coyoneda on the triangle. This supplies a right inverse to
the projection, which is therefore invertible. Exchange the two summands for the
symmetric assertion. Apply this argument to both restricted triangles, comparing
restriction of a biproduct with the biproduct of the restrictions. Composing with the
invertible counits proves both displayed maps invertible. No cover is needed.
-/
theorem ringedTopos_fibre_restriction
    {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
    (R : Sheaf J CommRingCat.{r})
    (U V : C) [Mono (terminal.from U)] [Mono (terminal.from V)]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V))]
    [HasDerivedCategory.{w} (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V))))]
    (rU : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (rV : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (rW : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rUW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (rVW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
          (pullback (terminal.from U) (terminal.from V)))))
    (RU : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RV : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (RW : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over
        (pullback (terminal.from U) (terminal.from V)))) ⥤
      DerivedCategory (ringedSiteModules.{max u v r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (adjU : rU ⊣ RU) (adjV : rV ⊣ RV) (adjW : rW ⊣ RW)
    (compU : rW ≅ rU ⋙ rUW) (compV : rW ≅ rV ⋙ rVW)
    (qU : DerivedCategory.Q ⋙ rU ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U ⋙
        DerivedCategory.Q)
    (qV : DerivedCategory.Q ⋙ rV ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V ⋙
        DerivedCategory.Q)
    (qW : DerivedCategory.Q ⋙ rW ≅
      moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qUW : DerivedCategory.Q ⋙ rUW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.fst (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (qVW : DerivedCategory.Q ⋙ rVW ≅
      moduleOverMapComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
        (pullback.snd (terminal.from U) (terminal.from V)) ⋙ DerivedCategory.Q)
    (compU_on_complexes : ∀ K,
      compU.hom.app (DerivedCategory.Q.obj K) ≫
        rUW.map (qU.hom.app K) ≫
          qUW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) U).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.fst (terminal.from U) (terminal.from V))).hom.app K))
    (compV_on_complexes : ∀ K,
      compV.hom.app (DerivedCategory.Q.obj K) ≫
        rVW.map (qV.hom.app K) ≫
          qVW.hom.app
            ((moduleOverComplex ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) V).obj K) =
      qW.hom.app K ≫ DerivedCategory.Q.map
        ((moduleOverComplexComp ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
          (pullback.snd (terminal.from U) (terminal.from V))).hom.app K))
    (A : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U)))
    (B : DerivedCategory (ringedSiteModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over V)))
    (c : rUW.obj A ≅ rVW.obj B)
    (G : DerivedCategory (ringedSiteModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (f : G ⟶ RU.obj A ⊞ RV.obj B)
    (h : RW.obj (rVW.obj B) ⟶ (shiftFunctor _ (1 : ℤ)).obj G)
    (hT : Pretriangulated.Triangle.mk f
      (biprod.desc
        (restrictionAdjunctionMap (rUW := rUW) adjU adjW compU A ≫ RW.map c.hom)
        (-restrictionAdjunctionMap (rUW := rVW) adjV adjW compV B)) h ∈ distTriang _) :
    IsIso (rU.map f ≫ rU.map biprod.fst ≫ adjU.counit.app A) ∧
      IsIso (rV.map f ≫ rV.map biprod.snd ≫ adjV.counit.app B) := by
  let : HasSheafify J AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{u, v, max u v r} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{u, v, max u v r} J
  let : HasSheafify (J.over U) AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{max u v, v, max u v r} (J.over U)
  let : HasSheafify (J.over V) AddCommGrpCat.{max u v r} :=
    binaryDescent_hasSheafify.{max u v, v, max u v r} (J.over V)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{max u v, v, max u v r} (J.over U)
  let : (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v r} :=
    binaryDescent_wEqualsLocallyBijective.{max u v, v, max u v r} (J.over V)
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let FU := SheafOfModules.overFunctor.{max u v r} R₀ U
  let FV := SheafOfModules.overFunctor.{max u v r} R₀ V
  have : PreservesFiniteLimits FU := (SheafOfModules.overFunctor_exact_ofUniverses R₀ U).1
  have : PreservesFiniteColimits FU := (SheafOfModules.overFunctor_exact_ofUniverses R₀ U).2
  have : PreservesFiniteLimits FV := (SheafOfModules.overFunctor_exact_ofUniverses R₀ V).1
  have : PreservesFiniteColimits FV := (SheafOfModules.overFunctor_exact_ofUniverses R₀ V).2
  let eU := restrictionDerivedIso FU rU qU
  let eV := restrictionDerivedIso FV rV qV
  let : rU.CommShift ℤ := Functor.CommShift.ofIso eU ℤ
  let : rV.CommShift ℤ := Functor.CommShift.ofIso eV ℤ
  have : NatTrans.CommShift eU.hom ℤ := Functor.CommShift.ofIso_compatibility eU ℤ
  have : NatTrans.CommShift eV.hom ℤ := Functor.CommShift.ofIso_compatibility eV ℤ
  have : rU.IsTriangulated := Functor.isTriangulated_of_iso eU
  have : rV.IsTriangulated := Functor.isTriangulated_of_iso eV
  obtain ⟨hU, hV, hUV, hVU⟩ := ringedTopos_directImage_restriction.{u, v, r, w}
    J R U V rU rV rW rUW rVW RU RV RW adjU adjV adjW compU compV
    qU qV qW qUW qVW compU_on_complexes compV_on_complexes
  have := hU A
  have := hV B
  have := hUV B
  have := hVU A
  have : IsIso (rU.map (-restrictionAdjunctionMap (rUW := rVW) adjV adjW compV B)) := by
    rw [rU.map_neg]
    exact ⟨⟨-inv (rU.map (restrictionAdjunctionMap (rUW := rVW) adjV adjW compV B)),
      by simp, by simp⟩⟩
  have : IsIso (rV.map
      (restrictionAdjunctionMap (rUW := rUW) adjU adjW compU A ≫ RW.map c.hom)) := by
    rw [rV.map_comp]
    infer_instance
  have := map_fibre_projection_isIso rU _ _ f h hT
  have := map_fibre_projection_snd_isIso rV _ _ f h hT
  constructor
  · have : IsIso (rU.map (f ≫ biprod.fst) ≫ adjU.counit.app A) := inferInstance
    simpa only [Functor.map_comp, Category.assoc] using this
  · have : IsIso (rV.map (f ≫ biprod.snd) ≫ adjV.counit.app B) := inferInstance
    simpa only [Functor.map_comp, Category.assoc] using this

end CategoryTheory
end
