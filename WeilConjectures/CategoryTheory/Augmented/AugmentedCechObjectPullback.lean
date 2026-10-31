/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

public import WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.PullbackCechLocalDescription
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.CategoryTheory.RingedToposMorphism.RingedToposDerivedAdjunctionOfUniverses
public import WeilConjectures.ProperBaseChange.ExtendedCechReflectorCore
public import WeilConjectures.ProperBaseChange.RingedToposKFlatPullback
public import WeilConjectures.SmoothPurity.CoefficientClosedStructure.CoefficientClosedTensorComparison

/-! # Pullback of augmented extended Cech objects

Source: Stacks Project, algebraization.tex, Tags 099E, 099F and 0A0G;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-augmented-cech-object-pullback).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wY
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem reflectorComparison
    {D : Type u} [Category.{v} D] (P : D → Prop) (F G : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E) (ν : ∀ E, E ⟶ G.obj E)
    (hF : ∀ E, P (F.obj E)) (hG : ∀ E, P (G.obj E))
    (nF : ∀ E E' (f : E ⟶ E'), η E ≫ F.map f = f ≫ η E')
    (nG : ∀ E E' (f : E ⟶ E'), ν E ≫ G.map f = f ≫ ν E')
    (uF : ∀ E T, P T → Function.Bijective (fun f : F.obj E ⟶ T ↦ η E ≫ f))
    (uG : ∀ E T, P T → Function.Bijective (fun f : G.obj E ⟶ T ↦ ν E ≫ f)) :
    ∃ e : F ≅ G, ∀ E, η E ≫ e.hom.app E = ν E := by
  classical
  choose m hm using fun E ↦ (uF E (G.obj E) (hG E)).2 (ν E)
  choose n hn using fun E ↦ (uG E (F.obj E) (hF E)).2 (η E)
  dsimp only at hm hn
  have hmn (E : D) : m E ≫ n E = 𝟙 _ := by
    apply (uF E (F.obj E) (hF E)).1
    simp only [← Category.assoc, hm, hn, Category.comp_id]
  have hnm (E : D) : n E ≫ m E = 𝟙 _ := by
    apply (uG E (G.obj E) (hG E)).1
    simp only [← Category.assoc, hn, hm, Category.comp_id]
  refine ⟨NatIso.ofComponents (fun E ↦ ⟨m E, n E, hmn E, hnm E⟩) ?_, hm⟩
  intro E E' f
  apply (uF E (G.obj E') (hG E')).1
  calc
    η E ≫ (F.map f ≫ m E') = f ≫ ν E' := by rw [← Category.assoc, nF, Category.assoc, hm]
    _ = η E ≫ (m E ≫ G.map f) := by rw [← nG, ← Category.assoc, hm]

private def objectHomEquiv
    {D : Type u} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P M : D) :
    (P ⟶ M) ≃ (S.monoidal.tensorUnit ⟶ H.obj (Opposite.op P, M)) := by
  let := S.monoidal
  exact
    { toFun := fun f ↦ (S.adjunction P).homEquiv _ _ ((λ_ P).hom ≫ f)
      invFun := fun g ↦ (λ_ P).inv ≫ ((S.adjunction P).homEquiv _ _).symm g
      left_inv := fun f ↦ by simp
      right_inv := fun g ↦ by
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        exact Equiv.apply_symm_apply _ _ }

private theorem objectHomEquiv_right
    {D : Type u} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P M N : D) (f : P ⟶ M) (g : M ⟶ N) :
    objectHomEquiv S P N (f ≫ g) =
      objectHomEquiv S P M f ≫ H.map (Prod.mkHom (𝟙 _) g) := by
  let := S.monoidal
  change (S.adjunction P).homEquiv _ _ ((λ_ P).hom ≫ (f ≫ g)) =
    (S.adjunction P).homEquiv _ _ ((λ_ P).hom ≫ f) ≫ _
  simpa only [Category.assoc, Functor.comp_obj, Prod.sectR_obj,
    Functor.comp_map, Prod.sectR_map] using
    (S.adjunction P).homEquiv_naturality_right ((λ_ P).hom ≫ f) g

private theorem objectHomEquiv_left
    {D : Type u} [Category.{v} D] {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (P Q M : D) (f : P ⟶ Q) (g : Q ⟶ M) :
    objectHomEquiv S P M (f ≫ g) =
      objectHomEquiv S Q M g ≫ H.map (Prod.mkHom f.op (𝟙 M)) := by
  let := S.monoidal
  change S.transpose S.monoidal.tensorUnit P M ((λ_ P).hom ≫ (f ≫ g)) =
    S.transpose S.monoidal.tensorUnit Q M ((λ_ Q).hom ≫ g) ≫ _
  have h := S.transpose_tensor (𝟙 S.monoidal.tensorUnit) f ((λ_ Q).hom ≫ g)
  simpa only [Category.id_comp, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom,
    MonoidalCategory.leftUnitor_naturality_assoc] using h

private theorem augmentedObjectComparison
    {D : Type u} [Category.{v} D] (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (O A B : D)
    (a : A ⟶ O) (b : B ⟶ O)
    (e : Prod.sectR (Opposite.op A) D ⋙ H ≅ Prod.sectR (Opposite.op B) D ⋙ H)
    (he : ∀ M, H.map (Prod.mkHom a.op (𝟙 M)) ≫ e.hom.app M =
      H.map (Prod.mkHom b.op (𝟙 M))) :
    ∃ d : A ≅ B, d.hom ≫ b = a := by
  classical
  let E (M : D) :
      (S.monoidal.tensorUnit ⟶ H.obj (Opposite.op A, M)) ≃
        (S.monoidal.tensorUnit ⟶ H.obj (Opposite.op B, M)) :=
    { toFun := fun f ↦ f ≫ e.hom.app M
      invFun := fun g ↦ g ≫ e.inv.app M
      left_inv := fun f ↦ by
        simp only [Category.assoc, Iso.hom_inv_id_app]
        change f ≫ 𝟙 (H.obj (Opposite.op A, M)) = f
        exact Category.comp_id f
      right_inv := fun g ↦ by
        simp only [Category.assoc, Iso.inv_hom_id_app]
        change g ≫ 𝟙 (H.obj (Opposite.op B, M)) = g
        exact Category.comp_id g }
  let T (M : D) : (A ⟶ M) ≃ (B ⟶ M) :=
    (objectHomEquiv S A M).trans ((E M).trans (objectHomEquiv S B M).symm)
  have hT (M : D) (f : A ⟶ M) :
      objectHomEquiv S B M (T M f) = objectHomEquiv S A M f ≫ e.hom.app M := by
    change (objectHomEquiv S B M) ((objectHomEquiv S B M).symm
      ((E M) (objectHomEquiv S A M f))) = _
    exact (objectHomEquiv S B M).apply_symm_apply _
  have hn (M N : D) (f : A ⟶ M) (g : M ⟶ N) :
      T N (f ≫ g) = T M f ≫ g := by
    apply (objectHomEquiv S B N).injective
    rw [hT, objectHomEquiv_right, objectHomEquiv_right, hT]
    simpa only [Category.assoc, Functor.comp_map, Prod.sectR_map] using congrArg
      (fun k ↦ objectHomEquiv S A M f ≫ k) (e.hom.naturality g)
  have hab : T O a = b := by
    apply (objectHomEquiv S B O).injective
    have ha := objectHomEquiv_left S A O O a (𝟙 O)
    have hb := objectHomEquiv_left S B O O b (𝟙 O)
    simp only [Category.comp_id] at ha hb
    rw [hT, ha, Category.assoc, he, ← hb]
  let r : B ⟶ A := T A (𝟙 A)
  let l : A ⟶ B := (T B).symm (𝟙 B)
  have hl : T B l = 𝟙 B := (T B).apply_symm_apply _
  have hrl : r ≫ l = 𝟙 B := by
    rw [show r ≫ l = T B l by simpa only [Category.id_comp] using
      (hn A B (𝟙 A) l).symm]
    exact hl
  have hlr : l ≫ r = 𝟙 A := by
    apply (T A).injective
    rw [hn, hl, Category.id_comp]
  have hra : r ≫ a = b := by
    have h := hn A O (𝟙 A) a
    simpa only [Category.id_comp, hab] using h.symm
  refine ⟨⟨l, r, hlr, hrl⟩, ?_⟩
  rw [← hra, ← Category.assoc, hlr, Category.id_comp]

/-- Derived inverse image transports the augmented Cech object and the coefficient ring.
This statement concerns objects and augmentation arrows; it has no tensor action variable.

Source: Stacks Project, algebraization.tex, Tags 099E, 099F and 0A0G;
sites-cohomology.tex, Tags 07A4 and 0G7E.
(blueprint: lem-weil-pbc-augmented-cech-object-pullback).

Proof: construct ordinary module pullback as algebraic inverse image followed by
extension of scalars. Uniqueness of left adjoints identifies its derived comparison
with the supplied L. This comparison is invertible on flat-term K-flat complexes.
The coefficient module in degree zero is such a complex; its ordinary unit
comparison gives j, fixed before the supplied Cech models are chosen.
Resolve KY by a flat-term K-flat complex P. The pullback local-description theorem
applies to the actual complex F(P), augmented by F(p;εY) followed by the unit
comparison. Naturality of the derived comparison gives its augmented square with j.
The completion functors represented by this pulled-back model and by KX are
reflectors onto the same complete objects. Their universal mapping properties give
a natural isomorphism preserving the reflection units. Cancel the invertible
coefficient internal-Hom unit to obtain compatibility with the augmentations.
The closed tensor-Hom adjunction and the left unitor convert this isomorphism into
a natural bijection Hom(QF(P), M) ≃ Hom(QKX, M). Evaluation at identity morphisms
gives inverse maps; the compatibility just established shows that these maps
preserve the augmentations. Compose with the resolution comparison to obtain d.
Every choice in the reflector comparison is the inverse image under a specified
bijection. Independent derived-category universes are retained throughout. -/
theorem ringed_augmentedCech_object_pullback
    {C X : Type u} [SmallCategory C] [SmallCategory X]
    {J : GrothendieckTopology C} {K : GrothendieckTopology X}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))]
    [HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))]
    [∀ U : C, HasDerivedCategory.{wY} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (RY.over U)))]
    [∀ U : X, HasDerivedCategory.{wX} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))]
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (IY : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (ιY : IY ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    [Mono ιY] [IY.IsFiniteType]
    (IX : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (ιX : IX ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    [Mono ιX] [IX.IsFiniteType]
    (hImage : ∀ (N : ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
      (j : N ⟶ SheafOfModules.unit ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)),
      Mono j →
      (∃ k : f.inverse.obj ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
          sheafCompose J (forget AddCommGrpCat)).obj IY) ⟶
          (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).obj N,
        (k ≫ (SheafOfModules.toSheaf ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) ⋙
            sheafCompose K (forget AddCommGrpCat)).map j : _ ⟶ (sheafCompose K (forget RingCat)).obj
              ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) =
          (f.inverse.map ((SheafOfModules.toSheaf
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⋙
            sheafCompose J (forget AddCommGrpCat)).map ιY) : _ ⟶ f.inverse.obj
              ((sheafCompose J (forget RingCat)).obj
                ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))) ≫ f.ringMap) ↔
      ∃ a : IX ⟶ N, a ≫ j = ιX)
    (Rf : ringedSiteDerived.{u, wX} RX ⥤ ringedSiteDerived.{u, wY} RY)
    (ρ : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{wY} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)) ⟶
      DerivedCategory.Q.{wX} (C := ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ⋙ Rf)
    (hRf : Rf.IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) (ComplexShape.up ℤ)))
    (hCompute : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)) ℤ,
      I.IsKInjective → IsIso (ρ.app I))
    (L : ringedSiteDerived.{u, wY} RY ⥤ ringedSiteDerived.{u, wX} RX)
    (a : L ⊣ Rf)
 :
    ∃ j : L.obj (DerivedCategory.Q.{wY}.obj (ringedSiteRingComplex RY)) ≅
        DerivedCategory.Q.{wX}.obj (ringedSiteRingComplex RX),
      ∀ (KX : ringedSiteComplex RX) (εX : KX ⟶ ringedSiteRingComplex RX),
        HasLocalExtendedCechDescription.{u, wX} RX IX ιX KX εX →
      ∀ (KY : ringedSiteComplex RY) (εY : KY ⟶ ringedSiteRingComplex RY),
        HasLocalExtendedCechDescription.{u, wY} RY IY ιY KY εY →
      ∃ d : L.obj (DerivedCategory.Q.{wY}.obj KY) ≅ DerivedCategory.Q.{wX}.obj KX,
        d.hom ≫ DerivedCategory.Q.{wX}.map εX =
          L.map (DerivedCategory.Q.{wY}.map εY) ≫ j.hom := by
  classical
  let A := ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)
  let B := ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
  let := f.leftExact
  obtain ⟨RI, ⟨I⟩⟩ := algebraic_image J K f.inverse f.direct f.adj RY
  obtain ⟨c, hc⟩ := structural_map K J RX RY f RI I
  let F := I.modules ⋙ SheafOfModules.tensorFunctor c
  obtain ⟨adjF⟩ : Nonempty (F ⊣ f.modules) := supplied_adjunction f RI I c hc
  let _ : PreservesColimits F := adjF.leftAdjoint_preservesColimits
  let _ : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let _ : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have hobj (M : A) : F.obj M = SheafOfModules.changeOfRings c (I.modules.obj M) := rfl
  have hmap {M N : A} (g : M ⟶ N) : F.map g = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map g) ≫
        eqToHom (hobj N).symm := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := SheafOfModules.canonicalRingedTensorComparison_existsUnique
    RY RX RI f.inverse I c F hobj f.direct f.adj hmap
  obtain ⟨u, _, _⟩ := SheafOfModules.canonicalRingedTensorComparison_unit
    RY RX RI f.inverse I c F hobj hmap k
  obtain ⟨L₀, ⟨adj₀⟩, G, ⟨adjG⟩, hG, ε, _, hεiso⟩ :=
    RingedToposMorphism.exists_derivedLeftAdjoint RY RX f Rf ρ hRf hCompute
  let := hG
  let eL := a.leftAdjointUniq adj₀
  let eG := adjG.leftAdjointUniq adjF
  let π := HomotopyCategory.quotient A (.up ℤ)
  let εc : DerivedCategory.Q.{wY} ⋙ L₀ ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{wX} :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso A).inv L₀ ≫
      Functor.whiskerLeft π ε ≫
      Functor.whiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
      Functor.whiskerLeft (G.mapHomologicalComplex (.up ℤ))
        (DerivedCategory.quotientCompQhIso B).hom
  let t : DerivedCategory.Q.{wY} ⋙ L ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{wX} :=
    Functor.whiskerLeft DerivedCategory.Q eL.hom ≫ εc ≫
      Functor.whiskerRight (NatIso.mapHomologicalComplex eG (.up ℤ)).hom DerivedCategory.Q
  have ht (P : CochainComplex A ℤ) (hP : P.IsAcyclicTensorKFlat)
      (hf : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n)) : IsIso (t.app P) := by
    have := hεiso P hP hf
    dsimp only [t, εc, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    infer_instance
  let OY := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY)
  have hflat : ∀ n : ℤ, SheafOfModules.IsFlat ((ringedSiteRingComplex RY).X n) := by
    let := SheafOfModules.monoidalCategory RY
    intro n
    change CategoryTheory.exactFunctor A A
      (MonoidalCategory.tensorRight ((ringedSiteRingComplex RY).X n))
    have hunit : ObjectProperty.flat OY := ObjectProperty.prop_unit _
    have hterm : ObjectProperty.flat ((ringedSiteRingComplex RY).X n) := by
      by_cases hn : n = 0
      · subst n
        exact (ObjectProperty.flat.prop_iff_of_iso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 OY)).2 hunit
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 OY n hn)
    exact hterm.2
  have hOY : (ringedSiteRingComplex RY).IsAcyclicTensorKFlat := by
    apply CochainComplex.isKFlat_of_boundedAbove_flat _ _ hflat
    refine ⟨0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 OY n (by omega)
  have htO := ht _ hOY hflat
  let u₀ : (F.mapHomologicalComplex (.up ℤ)).obj (ringedSiteRingComplex RY) ≅
      ringedSiteRingComplex RX :=
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app OY ≪≫
      (HomologicalComplex.single B (.up ℤ) 0).mapIso u
  let j : L.obj (DerivedCategory.Q.{wY}.obj (ringedSiteRingComplex RY)) ≅
      DerivedCategory.Q.{wX}.obj (ringedSiteRingComplex RX) :=
    asIso (t.app (ringedSiteRingComplex RY)) ≪≫ DerivedCategory.Q.mapIso u₀
  refine ⟨j, ?_⟩
  intro KX εX hX KY εY hY
  obtain ⟨P, p, hP, hfP, hp, _⟩ := CochainComplex.exists_isKFlatResolution KY
  have htP := ht P hP hfP
  have hq : IsIso (DerivedCategory.Q.{wY}.map p) := by
    let := hp
    infer_instance
  let := hq
  let A₀ := (F.mapHomologicalComplex (.up ℤ)).obj P
  let δ := (F.mapHomologicalComplex (.up ℤ)).map (p ≫ εY) ≫ u₀.hom
  have hA : HasLocalExtendedCechDescription.{u, wX} RX IX ιX A₀ δ :=
    pullback_cech_local_description RY RX f IY ιY IX ιX hImage F adjF u KY εY hY
      P p hp ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP) hfP
  let θ : L.obj (DerivedCategory.Q.{wY}.obj KY) ≅ DerivedCategory.Q.{wX}.obj A₀ :=
    (L.mapIso (asIso (DerivedCategory.Q.map p))).symm ≪≫ asIso (t.app P)
  have hθ : θ.hom ≫ DerivedCategory.Q.map δ =
      L.map (DerivedCategory.Q.map εY) ≫ j.hom := by
    have hn := t.naturality (p ≫ εY)
    change L.map (DerivedCategory.Q.map (p ≫ εY)) ≫ t.app _ =
      t.app P ≫ DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (p ≫ εY))
      at hn
    dsimp only [θ, δ, j, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      asIso_hom, Functor.mapIso_hom]
    rw [Functor.map_comp, Category.assoc, ← reassoc_of% hn]
    rw [DerivedCategory.Q.map_comp, L.map_comp]
    simp only [← Category.assoc, ← L.map_comp, asIso_inv, IsIso.inv_hom_id,
      Category.id_comp]
  have hcompare : ∃ b : DerivedCategory.Q.{wX}.obj A₀ ≅ DerivedCategory.Q.{wX}.obj KX,
      b.hom ≫ DerivedCategory.Q.map εX = DerivedCategory.Q.map δ := by
    obtain ⟨S, _, _, _⟩ := ringedDerived_closed_symmetric_monoidal.{u, u, u, wX} K RX
    obtain ⟨hcA, hnA, huA, _⟩ :=
      ringedExtendedCech_reflector_properties K RX IX ιX A₀ δ hA
    obtain ⟨hcX, hnX, huX, _⟩ :=
      ringedExtendedCech_reflector_properties K RX IX ιX KX εX hX
    obtain ⟨e, he⟩ := reflectorComparison
      (IsLocallyDerivedRingedIdealComplete RX IX ιX)
      (ringedCechCompletionFunctor RX A₀) (ringedCechCompletionFunctor RX KX)
      (ringedCechCompletionUnit RX A₀ δ) (ringedCechCompletionUnit RX KX εX)
      hcA hcX hnA hnX huA huX
    apply augmentedObjectComparison (derivedInternalHom K RX) S
      (DerivedCategory.Q.obj (ringedSiteRingComplex RX))
      (DerivedCategory.Q.obj A₀) (DerivedCategory.Q.obj KX)
      (DerivedCategory.Q.map δ) (DerivedCategory.Q.map εX) e
    intro M
    have hi : IsIso (ringedDerivedHomUnit RX M) := by
      change IsIso ((derivedHomUnitIso RX).hom.app M)
      infer_instance
    let := hi
    apply (cancel_epi (ringedDerivedHomUnit RX M)).mp
    simpa only [ringedCechCompletionUnit, Category.assoc] using he M
  obtain ⟨b, hb⟩ := hcompare
  refine ⟨θ ≪≫ b, ?_⟩
  simpa only [Iso.trans_hom, Category.assoc, hb] using hθ

end CategoryTheory
