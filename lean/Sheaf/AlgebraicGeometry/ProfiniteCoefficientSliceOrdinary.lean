/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups D9 and F7
-/
module

public import Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel
public import Sheaf.AlgebraicGeometry.CommutativeConstantSliceRestriction
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # Ordinary coefficient extension on the profinite slice

Source: Hemo--Richarz--Scholbach, (3.1)--(3.2), Remark 3.2;
Stacks Project, Modules on Sites, Tags 03CY, 03DH and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace SliceCoefficientProof

universe a b r m
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}

private def scalarRoundTrip {R S : Sheaf J RingCat.{r}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{m} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{m} S) :=
  SheafOfModules.pushforwardComp (F := 𝟭 C) (G := 𝟭 C) c.inv c.hom ≪≫
    SheafOfModules.pushforwardCongr c.inv_hom_id ≪≫ SheafOfModules.pushforwardId S

private def scalarEquivalence {R S : Sheaf J RingCat.{r}} (c : R ≅ S) :
    SheafOfModules.{m} S ≌ SheafOfModules.{m} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (scalarRoundTrip c).symm
  counitIso := scalarRoundTrip c.symm
  functor_unitIso_comp M := by ext V x; rfl

private def restriction {R : Sheaf J RingCat.{r}} (U : C)
    {R' : Sheaf (J.over U) RingCat.{r}} (c : R' ≅ R.over U) :
    SheafOfModules.{m} R ⥤ SheafOfModules.{m} R' :=
  SheafOfModules.overFunctor R U ⋙ SheafOfModules.restrictScalars c.hom

private def restrictionAdj [HasBinaryProducts C] {R : Sheaf J RingCat.{r}} (U : C)
    {R' : Sheaf (J.over U) RingCat.{r}} (c : R' ≅ R.over U) :
    restriction U c ⊣ SheafOfModules.restrictScalars.{m} c.inv ⋙
      SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) U) :=
  (SheafOfModules.overPushforwardOverAdj U).comp (scalarEquivalence c).toAdjunction

private def rightSquare [HasBinaryProducts C] {R S : Sheaf J RingCat.{r}}
    (U : C) {R' S' : Sheaf (J.over U) RingCat.{r}}
    (c : R' ≅ R.over U) (d : S' ≅ S.over U) (α : R ⟶ S) (β : R' ⟶ S')
    (h : c.hom ≫ (J.overPullback RingCat.{r} U).map α = β ≫ d.hom) :
    (SheafOfModules.restrictScalars.{m} d.inv ⋙
      SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := S) U)) ⋙
        SheafOfModules.restrictScalars α ≅
      SheafOfModules.restrictScalars β ⋙ SheafOfModules.restrictScalars c.inv ⋙
        SheafOfModules.pushforward (SheafOfModules.pushforwardOver (R := R) U) := by
  let G := (Over.star U).sheafPushforwardContinuous RingCat.{r} J (J.over U)
  let p := SheafOfModules.pushforwardOver (R := R) U
  let q := SheafOfModules.pushforwardOver (R := S) U
  have h' : (J.overPullback RingCat.{r} U).map α ≫ d.inv = c.inv ≫ β := by
    calc
      _ = c.inv ≫ (c.hom ≫ (J.overPullback RingCat.{r} U).map α) ≫ d.inv := by
        simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = c.inv ≫ (β ≫ d.hom) ≫ d.inv := by rw [h]
      _ = _ := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hn : α ≫ q = p ≫ G.map ((J.overPullback RingCat.{r} U).map α) := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact (α.hom.naturality Limits.prod.snd.op).symm
  have hs : α ≫ (q ≫ G.map d.inv) = (p ≫ G.map c.inv) ≫ G.map β := by
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp, h', G.map_comp]
    simp only [Category.assoc]
  let i := SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U)) q d.inv
  let j := SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U)) p c.inv
  exact Functor.isoWhiskerRight i _ ≪≫
    SheafOfModules.pushforwardComp (F := 𝟭 C) (G := Over.star U) α (q ≫ G.map d.inv) ≪≫
    SheafOfModules.pushforwardCongr hs ≪≫
    (SheafOfModules.pushforwardComp (F := Over.star U) (G := 𝟭 (Over U))
      (p ≫ G.map c.inv) β).symm ≪≫ Functor.isoWhiskerLeft _ j.symm

private def extensionRestriction [HasBinaryProducts C] {R S : Sheaf J RingCat.{r}}
    (U : C) {R' S' : Sheaf (J.over U) RingCat.{r}}
    (c : R' ≅ R.over U) (d : S' ≅ S.over U) (α : R ⟶ S) (β : R' ⟶ S')
    (h : c.hom ≫ (J.overPullback RingCat.{r} U).map α = β ≫ d.hom)
    (E : SheafOfModules.{m} R ⥤ SheafOfModules.{m} S)
    (E' : SheafOfModules.{m} R' ⥤ SheafOfModules.{m} S')
    (adj : E ⊣ SheafOfModules.restrictScalars α)
    (adj' : E' ⊣ SheafOfModules.restrictScalars β) :
    E ⋙ restriction U d ≅ restriction U c ⋙ E' :=
  ((adj.comp (restrictionAdj U d)).ofNatIsoRight (rightSquare U c d α β h)).leftAdjointUniq
    ((restrictionAdj U c).comp adj')

private theorem counitUnit {A : Type*} [Category A] (K : GrothendieckTopology C)
    [HasWeakSheafify K A] {T : C} (hT : IsTerminal T) (F : Sheaf K A) :
    toSheafify K ((Functor.const Cᵒᵖ).obj (F.obj.obj (op T))) ≫
      ((constantSheafAdj K A hT).counit.app F).hom =
        (constantPresheafAdj A hT).counit.app F.obj := by
  change (sheafificationAdjunction K A).homEquiv _ _
    ((constantSheafAdj K A hT).counit.app F) = _
  rw [constantSheafAdj, Adjunction.comp_counit_app]
  exact ((sheafificationAdjunction K A).homEquiv _ _).apply_symm_apply
    ((constantPresheafAdj A hT).counit.app F.obj)

private theorem constantCounitOver {A : Type*} [Category A]
    (K : GrothendieckTopology C) [HasWeakSheafify K A]
    {T : C} (hT : IsTerminal T) (U : C) [HasWeakSheafify (K.over U) A]
    {F : Sheaf K A} {G : Sheaf (K.over U) A} (d : F.over U ≅ G)
    (c : (constantSheaf (K.over U) A).obj (F.obj.obj (op T)) ≅
      ((constantSheaf K A).obj (F.obj.obj (op T))).over U)
    (hc : toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (F.obj.obj (op T))) ≫
      c.hom.hom = Functor.whiskerLeft (Over.forget U).op
        (toSheafify K ((Functor.const Cᵒᵖ).obj (F.obj.obj (op T))))) :
    c.hom ≫ (K.overPullback A U).map ((constantSheafAdj K A hT).counit.app F) ≫ d.hom =
      (constantSheaf (K.over U) A).map
        (F.obj.map (hT.from U).op ≫ d.hom.hom.app (op (Over.mk (𝟙 U)))) ≫
          (constantSheafAdj (K.over U) A Over.mkIdTerminal).counit.app G := by
  apply ((sheafificationAdjunction (K.over U) A).homEquiv _ _).injective
  apply NatTrans.ext
  funext V
  let t := F.obj.map (hT.from U).op ≫ d.hom.hom.app (op (Over.mk (𝟙 U)))
  have hF := congr_app (counitUnit K hT F) ((Over.forget U).op.obj V)
  have hG := congr_app (counitUnit (K.over U) Over.mkIdTerminal G) V
  have hcV := congr_app hc V
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hF hG hcV
  have hnat := congr_app (toSheafify_naturality (K.over U)
    ((Functor.const (Over U)ᵒᵖ).map t)) V
  change t ≫ (toSheafify (K.over U)
      ((Functor.const (Over U)ᵒᵖ).obj (G.obj.obj (op (Over.mk (𝟙 U)))))).app V =
    (toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (F.obj.obj (op T)))).app V ≫
      ((constantSheaf (K.over U) A).map t).hom.app V at hnat
  change (toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (F.obj.obj (op T)))).app V ≫
      c.hom.hom.app V ≫
      ((constantSheafAdj K A hT).counit.app F).hom.app ((Over.forget U).op.obj V) ≫
        d.hom.hom.app V =
    (toSheafify (K.over U) ((Functor.const (Over U)ᵒᵖ).obj (F.obj.obj (op T)))).app V ≫
      ((constantSheaf (K.over U) A).map t).hom.app V ≫
        ((constantSheafAdj (K.over U) A Over.mkIdTerminal).counit.app G).hom.app V
  simp only [← Category.assoc]
  rw [hcV, hF, ← hnat, Category.assoc, hG]
  change F.obj.map (hT.from V.unop.left).op ≫ d.hom.hom.app V =
    (F.obj.map (hT.from U).op ≫ d.hom.hom.app (op (Over.mk (𝟙 U)))) ≫
      G.obj.map (Over.mkIdTerminal.from V.unop).op
  rw [Category.assoc, ← d.hom.hom.naturality, ← Category.assoc]
  change F.obj.map (hT.from V.unop.left).op ≫ d.hom.hom.app V =
    (F.obj.map (hT.from U).op ≫ F.obj.map
      ((Over.forget U).map (Over.mkIdTerminal.from V.unop)).op) ≫ d.hom.hom.app V
  rw [← F.obj.map_comp]
  congr 1
  congr 1
  rw [← op_comp]
  congr 1
  exact hT.hom_ext _ _

private def conjugateComparison
    {C₀ C₁ D₀ D₁ B₀ B₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁] [Category B₀] [Category B₁]
    (e : C₀ ≌ D₀) (eS : C₁ ≌ D₁) (f : C₀ ⥤ C₁) (R : D₀ ⥤ D₁)
    (E : B₀ ⥤ D₀) (E' : B₁ ⥤ D₁) (R₀ : B₀ ⥤ B₁)
    (h : e.functor ⋙ R ≅ f ⋙ eS.functor) (i : E ⋙ R ≅ R₀ ⋙ E') :
    E ⋙ e.inverse ⋙ f ≅ R₀ ⋙ E' ⋙ eS.inverse := by
  let k : e.inverse ⋙ f ≅ R ⋙ eS.inverse :=
    Iso.isoCompInverse (H := eS)
      ((Functor.associator e.inverse f eS.functor) ≪≫
        Iso.inverseCompIso (G := e) h.symm)
  exact Functor.isoWhiskerLeft E k ≪≫
    (Functor.associator E R eS.inverse).symm ≪≫
    Functor.isoWhiskerRight i eS.inverse ≪≫ Functor.associator _ _ _

end SliceCoefficientProof

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.Obj

private def sliceRingIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :
    (condensedSectionRing Λ.X).over S ≅
      Evaluation.ringSheaf ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ.X S) := by
  let J := coherentTopology Profinite.{u}
  let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (Over.forget S) Ab.{u + 1} (J.over S) J
  let z := ((Functor.mapCommMonCompIso (F := sheafToPresheaf J Ab.{u + 1})
      (G := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj (Over.forget S).op)).symm ≪≫
    Functor.mapCommMonNatIso e ≪≫
    Functor.mapCommMonCompIso (F := J.overPullback Ab.{u + 1} S)
      (G := sheafToPresheaf (J.over S) Ab.{u + 1})).app (CommMon.mk Λ.X)
  let w := (Monoidal.commMonFunctorCategoryEquivalence (Over S)ᵒᵖ Ab.{u + 1}).functor.mapIso z
  exact ObjectProperty.isoMk _ (Functor.isoWhiskerRight w
    InternalAbelianSheafModule.commMonToRing)

private theorem sliceRingIso_hom (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) (V : (Over S)ᵒᵖ) :
    ((sliceRingIso Λ S).hom.hom.app V).hom.toAddMonoidHom = AddMonoidHom.id _ := by
  change (((Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
    (Over.forget S) Ab.{u + 1} ((coherentTopology Profinite.{u}).over S)
      (coherentTopology Profinite.{u})).hom.app Λ.X).app V).hom = AddMonoidHom.id _
  rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app]
  rfl

private theorem sliceRingIso_inv (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) (V : (Over S)ᵒᵖ) (r : Λ.X.obj.obj ((Over.forget S).op.obj V)) :
    (sliceRingIso Λ S).inv.hom.app V r = r := by
  have h := congrArg (fun f ↦ f.hom.app V r) (sliceRingIso Λ S).hom_inv_id
  change (sliceRingIso Λ S).inv.hom.app V ((sliceRingIso Λ S).hom.hom.app V r) = r at h
  have hr := DFunLike.congr_fun (sliceRingIso_hom Λ S V) r
  change (sliceRingIso Λ S).hom.hom.app V r = r at hr
  rw [hr] at h
  exact h

private def sliceModules (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :=
  SliceCoefficientProof.restriction
    (R := (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (condensedSectionRing Λ.X)) S
    ((sheafCompose ((coherentTopology Profinite.{u}).over S)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (sliceRingIso Λ S).symm)

private def sliceSectionComparison (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :
    InternalAbelianSheafModule.sectionModuleFunctor (coherentTopology Profinite.{u}) Λ.X ⋙
        sliceModules Λ S ≅
      ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ.X ⋙
        InternalAbelianSheafModule.sectionModuleFunctor
          ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    refine PresheafOfModules.isoMk (fun V ↦ ModuleCat.isoMk (Iso.refl _) ?_) ?_
    · intro r
      ext x
      have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (Over.forget S) Ab.{u + 1} ((coherentTopology Profinite.{u}).over S)
          (coherentTopology Profinite.{u}) Λ.X M.X V
      change ((Functor.LaxMonoidal.μ
          (sheafToPresheaf ((coherentTopology Profinite.{u}).over S) Ab.{u + 1})
          (profiniteCoefficient Λ.X S)
          (((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).obj M.X)).app V ≫
        (Functor.LaxMonoidal.μ
          ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S) Λ.X M.X).hom.app V ≫
        (Mod.act M.X).hom.app ((Over.forget S).op.obj V)).hom (r ⊗ₜ[ℤ] x) =
        ((Functor.LaxMonoidal.μ (sheafToPresheaf (coherentTopology Profinite.{u})
          Ab.{u + 1}) Λ.X M.X).app ((Over.forget S).op.obj V) ≫
          (Mod.act M.X).hom.app ((Over.forget S).op.obj V)).hom
            ((sliceRingIso Λ S).inv.hom.app V r ⊗ₜ[ℤ] x)
      rw [← Category.assoc, h, sliceRingIso_inv]
      rfl
    · intro V W f
      ext x
      rfl
  · intro M N f
    ext V x
    rfl


private theorem sliceScalarSquare (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (S : Profinite.{u}) :
    (constantSheafOverIso (coherentTopology Profinite.{u}) CommRingCat.{u + 1} S
      (condensedScalarRing Λ.X)).hom ≫
        ((coherentTopology Profinite.{u}).overPullback CommRingCat.{u + 1} S).map
          (condensedScalarMap Λ.X) =
      ((constantSheaf ((coherentTopology Profinite.{u}).over S) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (profiniteScalarMap Λ.X S)) ≫
        Evaluation.scalarMap ((coherentTopology Profinite.{u}).over S)
          (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal) ≫
            (sliceRingIso Λ S).inv := by
  let J := coherentTopology Profinite.{u}
  have h := SliceCoefficientProof.constantCounitOver J terminalIsTerminal S
    (sliceRingIso Λ S)
    (constantSheafOverIso J CommRingCat.{u + 1} S (condensedScalarRing Λ.X))
    (toSheafify_constantSheafOverHom_hom J CommRingCat.{u + 1} S
      (condensedScalarRing Λ.X))
  have hnorm : (condensedSectionRing Λ.X).obj.map (terminalIsTerminal.from S).op ≫
      (sliceRingIso Λ S).hom.hom.app (op (Over.mk (𝟙 S))) =
        CommRingCat.ofHom (profiniteScalarMap Λ.X S) := by
    rw [show terminalIsTerminal.from S = terminal.from S from terminal.hom_ext _ _]
    rfl
  rw [hnorm] at h
  apply (Iso.eq_comp_inv (sliceRingIso Λ S)).2
  simpa only [Category.assoc, J, condensedScalarMap, Evaluation.scalarMap] using h

attribute [local irreducible] sliceRingIso

/-- Ordinary coefficient extension commutes with restriction before deriving.
The coefficient map is specified explicitly; the conclusion involves only the
ordinary functors of the two models, and no derived functors or complexes.

Source: HRS equations (3.1)--(3.2), Remark 3.2; Stacks Modules on Sites, 03CY,
03DH and 03EK. This is steps 1--2 of the parent slice base-change argument.
(blueprint: lem-zl-profinite-coefficient-slice-ordinary).

Proof: let J be the coherent topology and K its slice at S. The monoidal
restriction comparison identifies the restricted section-ring sheaf with the
section-ring sheaf of the restricted internal ring. On terminal sections this
is profiniteSectionRingIso. The constant-sheaf comparison takes each constant
point scalar to the same constant section. Naturality of the constant-sheaf
adjunction counit, evaluated on the map S to the point, identifies the restricted
point scalar map with phi. For a module M form sectionwise balanced tensors.
After these coefficient identifications both sides have the same generators
b tensor m and the same additive and balancing relations. The maps fixing
these generators are inverse and commute with section restrictions. Restriction
to the slice commutes with sheafification: the restricted sheafification unit
is locally bijective, because slice covering sieves are exactly the underlying
covering sieves. Thus the tensor-presheaf isomorphism sheafifies to the required
module isomorphism. Its naturality follows on pure tensors and then by the
sheafification universal property. The section-module equivalences identify
this restriction with the displayed actual mapMod. The object and map equations
of each model identify its ordinary functor with this same sheafified extension,
so the comparison applies to every choice of models. The construction also
applies to the empty slice and to zero coefficient rings. -/
theorem profinite_coefficient_slice_ordinary
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (S : Profinite.{u})
    (φ : realizationRing ((coherentTopology Profinite.{u}).over S)
        (condensedScalarRing Λ.X) ⟶
      Evaluation.ringSheaf ((coherentTopology Profinite.{u}).over S)
        (profiniteCoefficient Λ.X S))
    (hφ : φ =
      (constantSheaf ((coherentTopology Profinite.{u}).over S) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (profiniteScalarMap Λ.X S)) ≫
        Evaluation.scalarMap ((coherentTopology Profinite.{u}).over S)
          (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal)
    (M : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (condensedScalarMap Λ.X))
    [HasDerivedCategory.{u + 2}
      (realizationModules ((coherentTopology Profinite.{u}).over S)
        (condensedScalarRing Λ.X))]
    (MS : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2} φ) :
    let e := InternalAbelianSheafModule.sectionModuleEquivalence
      (coherentTopology Profinite.{u}) Λ.X
    let eS := InternalAbelianSheafModule.sectionModuleEquivalence
      ((coherentTopology Profinite.{u}).over S) (profiniteCoefficient Λ.X S)
    let f := ((coherentTopology Profinite.{u}).overPullback Ab.{u + 1} S).mapMod Λ.X
    Nonempty (M.E ⋙ e.inverse ⋙ f ≅
      commutativeConstantSliceRestriction (coherentTopology Profinite.{u})
        (condensedScalarRing Λ.X) S ⋙ MS.E ⋙ eS.inverse) := by
  let J := coherentTopology Profinite.{u}
  let e := InternalAbelianSheafModule.sectionModuleEquivalence J Λ.X
  let eS := InternalAbelianSheafModule.sectionModuleEquivalence (J.over S)
    (profiniteCoefficient Λ.X S)
  let f := (J.overPullback Ab.{u + 1} S).mapMod Λ.X
  let c := (sheafCompose (J.over S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (constantSheafOverIso J CommRingCat.{u + 1} S (condensedScalarRing Λ.X))
  let d := (sheafCompose (J.over S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
    (sliceRingIso Λ S).symm
  let α := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (condensedScalarMap Λ.X)
  let β := (sheafCompose (J.over S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map φ
  have hs : c.hom ≫ (J.overPullback RingCat.{u + 1} S).map α = β ≫ d.hom := by
    have h := sliceScalarSquare Λ S
    rw [← hφ] at h
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    exact congrArg (fun t ↦ (t.hom.app V).hom) h
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction
    (condensedScalarMap Λ.X)
  obtain ⟨adj, _⟩ := ha M.E M.obj_eq M.map_eq
  obtain ⟨_, _, hb⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction φ
  obtain ⟨adjS, _⟩ := hb MS.E MS.obj_eq MS.map_eq
  -- Explicit ring sheaves avoid inferring a sheaf from its restriction.
  let i := SliceCoefficientProof.extensionRestriction (J := J)
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing J (condensedScalarRing Λ.X)))
    (S := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (condensedSectionRing Λ.X))
    (R' := (sheafCompose (J.over S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (realizationRing (J.over S) (condensedScalarRing Λ.X)))
    (S' := (sheafCompose (J.over S) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (Evaluation.ringSheaf (J.over S) (profiniteCoefficient Λ.X S)))
    S c d α β hs M.E MS.E adj adjS
  have i' : M.E ⋙ sliceModules Λ S ≅
      commutativeConstantSliceRestriction J (condensedScalarRing Λ.X) S ⋙ MS.E := by
    exact i
  exact ⟨SliceCoefficientProof.conjugateComparison e eS f (sliceModules Λ S)
    M.E MS.E (commutativeConstantSliceRestriction J (condensedScalarRing Λ.X) S)
    (sliceSectionComparison Λ S) i'⟩

end AlgebraicGeometry.ProEtale.CondensedRing
