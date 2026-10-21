/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.EtaleTensorHomEvaluationNaturality
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeCoordinatesNaturality

/-! # Local Frobenius equations on finite locally free modules -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open Modules SheafOfModules Pseudofunctor.LocallyDiscreteOpToCat
attribute [local instance 3000] CategoryStruct.toQuiver
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensorPullback tensorPullbackObj
  tensorSectionsPullbackComparison pullbackObjUnitIso pullbackFreeIso
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
private theorem exists_affine_frame (S : Scheme.{u}) (E : S.Modules)
    [E.IsFiniteLocallyFree] (U : S.Etale) (x : U.left) :
    ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ n : ℕ, Nonempty ((Modules.pullback (A.ι ≫ U.hom)).obj E ≅
        (Modules.pullback (A.ι ≫ U.hom)).obj
          (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) := by
  classical
  let M := (Modules.pullback U.hom).obj E
  obtain ⟨B, I, hI, hxB, ⟨e⟩⟩ := Modules.exists_mem_over_iso_free M x
  obtain ⟨A, hA, hxA, hAB⟩ := exists_isAffineOpen_mem_and_subset hxB
  let j : A.toScheme ⟶ B.toScheme := U.left.homOfLE hAB
  let eB : M.restrict B.ι ≅ SheafOfModules.free I := overIsoFreeEquiv M B I e
  let eA : M.restrict A.ι ≅ SheafOfModules.free I :=
    restrictCompIso M B.ι j A.ι (by simp [j]) ≪≫
      (Modules.restrictFunctor j).mapIso eB ≪≫ restrictFreeIso j I
  let eFin : I ≃ ULift.{u} (Fin (Fintype.card I)) :=
    (Fintype.equivFin I).trans Equiv.ulift.symm
  refine ⟨A, hA, hxA, Fintype.card I, ⟨?_⟩⟩
  exact ((pullbackComp A.ι U.hom).app E).symm ≪≫
    ((restrictFunctorIsoPullback A.ι).app M).symm ≪≫ eA ≪≫
    SheafOfModules.freeFunctor.mapIso eFin.toIso ≪≫
    (pullbackFreeIso (A.ι ≫ U.hom) _).symm
private theorem free_hom_coordinates_naturality
    {S V W : Scheme.{u}} (f : V ⟶ S) (h : W ⟶ S) (g : W ⟶ V)
    (hg : g ≫ f = h) (n : ℕ)
    (φ : (Modules.pullback f).obj (Modules.unit S) ⟶
      (Modules.pullback f).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) (i : Fin n) :
    freeSectionsEquiv (ULift.{u} (Fin n))
      ((pullbackFreeIso h _).hom.app ⊤
        (homSection h (pullHom (F := modulesPseudofunctor) φ g h h hg hg)))
          (ULift.up i) =
      g.appTop (freeSectionsEquiv (ULift.{u} (Fin n))
        ((pullbackFreeIso f _).hom.app ⊤ (homSection f φ)) (ULift.up i)) := by
  subst h
  rw [pullHom_eq_pullbackComp, homSection_comp]
  have hh := pullback_free_coordinates_naturality f (g ≫ f) g rfl
    (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) n
    (𝟙 _) (homSection f φ) i
  simpa [pullbackSectionFactorization, pullbackCompOfEq, pullbackCongr,
    pullbackΓ_apply, pullbackSection] using hh
private noncomputable def frameCoordinates
    {S T : Scheme.{u}} (f : T ⟶ S) (E : S.Modules) (n : ℕ)
    (q : (Modules.pullback f).obj E ≅ (Modules.pullback f).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) :
    Γ((tensorPullback f).obj E, ⊤) ≃ₗ[Γ(T, ⊤)]
      (ULift.{u} (Fin n) → Γ(T, ⊤)) := by
  classical
  exact SheafOfModules.sectionsLinearEquivOfIsoFree
    ((tensorSectionsPullbackComparison f).app E ≪≫ q ≪≫ pullbackFreeIso f _) (op ⊤)
private theorem evaluation_surjective {S : Scheme.{u}} (E : S.Modules) (V : S.Etale) :
    Function.Surjective (etaleTensorHomEvaluation E V) := by
  intro s
  let t := ((tensorSectionsPullbackComparison V.hom).hom.app E).app ⊤ s
  let φ := (pullbackObjUnitIso V.hom).hom ≫ homOfGlobalSection _ t
  refine ⟨φ, ?_⟩
  dsimp only [etaleTensorHomEvaluation, φ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ((tensorSectionsPullbackComparison V.hom).inv.app E).app ⊤
    ((homOfGlobalSection _ t).app ⊤ (1 : Γ(V.left, ⊤))) = s
  rw [homOfGlobalSection_app_one]
  erw [((Modules.pullback V.hom).obj E).presheaf.map_id]
  change (((tensorSectionsPullbackComparison V.hom).hom.app E) ≫
    ((tensorSectionsPullbackComparison V.hom).inv.app E)).app ⊤ s = s
  rw [Iso.hom_inv_id_app]
  rfl
private theorem homSection_postcompose {S T : Scheme.{u}} (f : T ⟶ S)
    (E N : S.Modules)
    (φ : (Modules.pullback f).obj (Modules.unit S) ⟶ (Modules.pullback f).obj E)
    (q : (Modules.pullback f).obj E ⟶ (Modules.pullback f).obj N) :
    homSection f (φ ≫ q) = q.app ⊤ (homSection f φ) := by
  rfl
private theorem frameCoordinates_evaluation {S : Scheme.{u}} (E : S.Modules)
    (V : S.Etale) (n : ℕ)
    (q : (Modules.pullback V.hom).obj E ≅ (Modules.pullback V.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (φ : (etaleHom (unitObj S) E).obj (op V)) :
    frameCoordinates V.hom E n q (etaleTensorHomEvaluation E V φ) =
      freeSectionsEquiv (ULift.{u} (Fin n))
        ((pullbackFreeIso V.hom _).hom.app ⊤ (homSection V.hom (φ ≫ q.hom))) := by
  classical
  have he : ((tensorSectionsPullbackComparison V.hom).hom.app E).app ⊤
      (etaleTensorHomEvaluation E V φ) = homSection V.hom φ := by
    change (((pullbackObjUnitIso V.hom).inv ≫ φ ≫
      (tensorSectionsPullbackComparison V.hom).inv.app E) ≫
      (tensorSectionsPullbackComparison V.hom).hom.app E).app ⊤ (1 : Γ(V.left, ⊤)) = _
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [homSection, pullbackSection_one_eq]
    rfl
  change freeSectionsEquiv _ ((pullbackFreeIso V.hom _).hom.app ⊤
    (q.hom.app ⊤ (((tensorSectionsPullbackComparison V.hom).hom.app E).app ⊤
      (etaleTensorHomEvaluation E V φ)))) = _
  have hp := homSection_postcompose V.hom E
    (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) φ q.hom
  exact (congrArg (fun z : Γ((Modules.pullback V.hom).obj E, ⊤) ↦
    freeSectionsEquiv (ULift.{u} (Fin n))
      ((pullbackFreeIso V.hom _).hom.app ⊤ (q.hom.app ⊤ z))) he).trans
    (congrArg (fun z : Γ((Modules.pullback V.hom).obj
        (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))), ⊤) ↦
      freeSectionsEquiv (ULift.{u} (Fin n))
        ((pullbackFreeIso V.hom _).hom.app ⊤ z)) hp.symm)

attribute [local irreducible] frameCoordinates etaleTensorHomEvaluation
private theorem pull_composite
    {F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1}}
    {S V W : Scheme.{u}} (O E N : F.obj (.mk (op S)))
    (f : V ⟶ S) (h : W ⟶ S) (g : W ⟶ V) (hg : g ≫ f = h)
    (φ : (F.map f.op.toLoc).toFunctor.obj O ⟶ (F.map f.op.toLoc).toFunctor.obj E)
    (qV : (F.map f.op.toLoc).toFunctor.obj E ⟶ (F.map f.op.toLoc).toFunctor.obj N)
    (qW : (F.map h.op.toLoc).toFunctor.obj E ⟶ (F.map h.op.toLoc).toFunctor.obj N)
    (hq : pullHom qV g h h hg hg = qW) :
    pullHom (φ ≫ qV) g h h hg hg = pullHom φ g h h hg hg ≫ qW := by
  rw [pullHom_comp φ qV g h h h hg hg hg, hq]
private theorem etaleHom_map_pullHom {S : Scheme.{u}} (M N : modulesPseudofunctor.obj (.mk (op S)))
    (V W : S.Etale) (g : W ⟶ V) (φ : (etaleHom M N).obj (op V)) :
    (etaleHom M N).map g.op φ =
      pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := N)
        (f₁ := V.hom) (f₂ := V.hom) φ g.left W.hom W.hom
        (MorphismProperty.Over.w g) (MorphismProperty.Over.w g) := by
  exact Pseudofunctor.presheafHom_map_eq_pullHom
    ((toProEt S ⋙ ProEt.forget S).map g) φ

private theorem homSection_frame_pull {S : Scheme.{u}} (E N : S.Modules)
    (V W : S.Etale) (g : W ⟶ V)
    (qV : (Modules.pullback V.hom).obj E ⟶ (Modules.pullback V.hom).obj N)
    (qW : (Modules.pullback W.hom).obj E ⟶ (Modules.pullback W.hom).obj N)
    (hq : pullHom (F := modulesPseudofunctor) qV g.left W.hom W.hom
      (MorphismProperty.Over.w g) (MorphismProperty.Over.w g) = qW)
    (φ : (etaleHom (unitObj S) E).obj (op V)) :
    homSection W.hom (((etaleHom (unitObj S) E).map g.op φ) ≫ qW) =
      homSection W.hom (pullHom (F := modulesPseudofunctor) (M₁ := Modules.unit S)
        (M₂ := N) (f₁ := V.hom) (f₂ := V.hom)
        (φ ≫ qV) g.left W.hom W.hom (MorphismProperty.Over.w g) (MorphismProperty.Over.w g)) := by
  have hc := pull_composite (F := modulesPseudofunctor) (Modules.unit S) E N
    V.hom W.hom g.left (MorphismProperty.Over.w g) φ qV qW hq
  have hm := etaleHom_map_pullHom (unitObj S) E V W g φ
  rw [hc]
  exact congrArg (fun z : (etaleHom (unitObj S) E).obj (op W) ↦
    homSection W.hom (A := N) (z ≫ qW)) hm

private noncomputable def frameEvaluationNat {S : Scheme.{u}} (E : S.Modules) :
    etaleHom (unitObj S) E ⟶
      etaleTensorSectionsPresheaf E ⋙ CategoryTheory.forget AddCommGrpCat where
  app V := TypeCat.ofHom (etaleTensorHomEvaluation E V.unop)
  naturality _ _ g := etaleTensorHomEvaluation_naturality E g
private theorem natural_of_evaluation {C : Type (u + 1)} [Category.{u} C]
    {F : C ⥤ Type u} {G : C ⥤ AddCommGrpCat.{u}}
    (e : F ⟶ G ⋙ CategoryTheory.forget AddCommGrpCat)
    {V W : C} (g : V ⟶ W) (he : Function.Surjective (e.app V))
    {A B : Type u} (kV : G.obj V → A) (kW : G.obj W → B) (t : A → B)
    (h : ∀ φ, kW (e.app W (F.map g φ)) = t (kV (e.app V φ)))
    (s : G.obj V) : kW (G.map g s) = t (kV s) := by
  obtain ⟨φ, rfl⟩ := he s
  have hn := ConcreteCategory.congr_hom (C := Type u) (e.naturality g) φ
  exact (congrArg kW hn.symm).trans (h φ)
private theorem frameCoordinates_naturality {S : Scheme.{u}} (E : S.Modules)
    (V W : S.Etale) (g : W ⟶ V) (n : ℕ)
    (qV : (Modules.pullback V.hom).obj E ≅ (Modules.pullback V.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (qW : (Modules.pullback W.hom).obj E ≅ (Modules.pullback W.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (hq : pullHom (F := modulesPseudofunctor) (M₁ := E)
      (M₂ := SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))
      (f₁ := V.hom) (f₂ := V.hom) qV.hom g.left W.hom W.hom
      (MorphismProperty.Over.w g) (MorphismProperty.Over.w g) = qW.hom)
    (s : Γ((tensorPullback V.hom).obj E, ⊤)) (i : Fin n) :
    frameCoordinates W.hom E n qW (etaleTensorSectionsPresheaf E |>.map g.op <| s)
        (ULift.up i) = g.left.appTop (frameCoordinates V.hom E n qV s (ULift.up i)) := by
  refine natural_of_evaluation (frameEvaluationNat E) g.op (evaluation_surjective E V)
    (fun z ↦ frameCoordinates V.hom E n qV z (ULift.up i))
    (fun z ↦ frameCoordinates W.hom E n qW z (ULift.up i))
    (fun z ↦ g.left.appTop z) (fun φ ↦ ?_) s
  have hs := homSection_frame_pull E
    (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))
    V W g qV.hom qW.hom hq φ
  have h := free_hom_coordinates_naturality V.hom W.hom g.left
    (MorphismProperty.Over.w g) n (φ ≫ qV.hom) i
  have evW := congrFun (frameCoordinates_evaluation E W n qW
    ((etaleHom (unitObj S) E).map g.op φ)) (ULift.up i)
  have evV := congrFun (frameCoordinates_evaluation E V n qV φ) (ULift.up i)
  have h2 := congrArg (fun z : Γ((Modules.pullback W.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))), ⊤) ↦
    freeSectionsEquiv (ULift.{u} (Fin n))
      ((pullbackFreeIso W.hom _).hom.app ⊤ z) (ULift.up i)) hs
  exact evW.trans (h2.trans (h.trans
    (congrArg (fun z : Γ(V.left, ⊤) ↦ g.left.appTop z) evV.symm)))
private theorem coordinates_transport {C : Type (u + 1)} [Category.{u} C]
    {P Q : C ⥤ AddCommGrpCat.{u}} (h : P = Q) {V W : C} (g : V ⟶ W)
    {A B : Type u} (kV : P.obj V → A) (kW : P.obj W → B)
    (cV : Q.obj V → A) (cW : Q.obj W → B) (t : A → B)
    (hV : ∀ z, cV ((eqToIso h).hom.app V z) = kV z)
    (hW : ∀ z, cW ((eqToIso h).hom.app W z) = kW z)
    (hk : ∀ z, kW (P.map g z) = t (kV z)) (s : Q.obj V) :
    cW (Q.map g s) = t (cV s) := by
  subst Q
  change ∀ z, cV z = kV z at hV
  change ∀ z, cW z = kW z at hW
  rw [hW, hV]
  exact hk s

private theorem frameCoordinates_sheaf_naturality {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent]
    (V W : S.Etale) (g : W ⟶ V) (n : ℕ)
    (qV : (Modules.pullback V.hom).obj E ≅ (Modules.pullback V.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (qW : (Modules.pullback W.hom).obj E ≅ (Modules.pullback W.hom).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (hq : pullHom (F := modulesPseudofunctor) (M₁ := E)
      (M₂ := SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))
      (f₁ := V.hom) (f₂ := V.hom) qV.hom g.left W.hom W.hom
      (MorphismProperty.Over.w g) (MorphismProperty.Over.w g) = qW.hom)
    (s : Γ((tensorPullback V.hom).obj E, ⊤)) (i : Fin n) :
    frameCoordinates W.hom E n qW ((etaleTensorSectionsSheaf E).obj.map g.op s)
        (ULift.up i) = g.left.appTop (frameCoordinates V.hom E n qV s (ULift.up i)) := by
  refine coordinates_transport
    (P := etaleTensorSectionsPresheaf E) (Q := (etaleTensorSectionsSheaf E).obj)
    rfl g.op
    (fun z ↦ frameCoordinates V.hom E n qV z (ULift.up i))
    (fun z ↦ frameCoordinates W.hom E n qW z (ULift.up i))
    (fun z ↦ frameCoordinates V.hom E n qV z (ULift.up i))
    (fun z ↦ frameCoordinates W.hom E n qW z (ULift.up i))
    (fun z ↦ g.left.appTop z) (fun _ ↦ rfl) (fun _ ↦ rfl) ?_ s
  intro z
  exact frameCoordinates_naturality E V W g n qV qW hq z i

private noncomputable def pullFrame {S T : Scheme.{u}} (a : T ⟶ S) (E : S.Modules)
    (n : ℕ) (q : (Modules.pullback a).obj E ≅ (Modules.pullback a).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (V : T.Etale) :
    (Modules.pullback (V.hom ≫ a)).obj E ≅ (Modules.pullback (V.hom ≫ a)).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) :=
  by
    have : IsIso (pullHom (F := modulesPseudofunctor) q.hom V.hom
        (V.hom ≫ a) (V.hom ≫ a) rfl rfl) :=
      isIso_pullHom (F := modulesPseudofunctor) (M₁ := E)
        (M₂ := SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))
        q.hom V.hom (V.hom ≫ a) (V.hom ≫ a) rfl rfl
    exact asIso (pullHom (F := modulesPseudofunctor) q.hom V.hom
      (V.hom ≫ a) (V.hom ≫ a) rfl rfl)
private theorem pullFrame_naturality {S T : Scheme.{u}} (a : T ⟶ S) (E : S.Modules)
    (n : ℕ) (q : (Modules.pullback a).obj E ≅ (Modules.pullback a).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))))
    (V W : T.Etale) (g : W ⟶ V) :
    pullHom (F := modulesPseudofunctor) (pullFrame a E n q V).hom g.left
      (W.hom ≫ a) (W.hom ≫ a)
      (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ a) (MorphismProperty.Over.w g))
      (by simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ a) (MorphismProperty.Over.w g)) =
      (pullFrame a E n q W).hom := by
  dsimp only [pullFrame, asIso_hom]
  rw [pullHom_pullHom]
  congr 1
  exact MorphismProperty.Over.w g

private theorem localized_additive_coordinates {S T : Scheme.{u}} (a : T ⟶ S)
    [Etale a] (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (n : ℕ) :
    let M : T.Etale ⥤ S.Etale :=
      MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale a)
    ∀ (act : ∀ V : T.Etale, Γ(V.left, ⊤) → F.obj.obj (op (M.obj V)) →
        F.obj.obj (op (M.obj V)))
      (c : ∀ V : T.Etale, F.obj.obj (op (M.obj V)) ≃+ (Fin n → Γ(V.left, ⊤))),
    (∀ (V W : T.Etale) (g : W ⟶ V) (s) (i),
      c W (F.obj.map (M.map g).op s) i = g.left.appTop (c V s i)) →
    (∀ V b s, c V (act V b s) = b • c V s) →
    let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1} a inferInstance
    let G := (sheafCompose S.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F
    ∃ e : ∀ V : T.Etale, (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
      (∀ (V W : T.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)) (i),
        e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
      (∀ (V : T.Etale) (b : Γ(V.left, ⊤)) (s : (L.obj G).obj.obj (op V)),
        e V (ULift.up (act V b s.down)) = b • e V s) := by
  classical
  intro M act c hc ha
  let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1} a inferInstance
  let G := (sheafCompose S.smallEtaleTopology
    AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F
  let e (V : T.Etale) : (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)) :=
    AddEquiv.ulift.trans (c V)
  have he (V : T.Etale) (s : (L.obj G).obj.obj (op V)) : e V s = c V s.down := rfl
  have hm (V W : T.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)) :
      (((L.obj G).obj.map g.op) s).down = F.obj.map (M.map g).op s.down := rfl
  refine ⟨e, ?_, ?_⟩
  · intro V W g s i
    rw [he, hm, he]
    exact hc V W g s.down i
  · intro V b s
    rw [he, he]
    exact ha V b s.down

private def unliftAddCoordinates (R : Type u) [Add R] (n : ℕ) :
    (ULift.{u} (Fin n) → R) ≃+ (Fin n → R) where
  toFun z i := z (ULift.up i)
  invFun z i := z i.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def linearCoordinatesAddEquiv {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (l : M ≃ₗ[R] (ULift.{u} (Fin n) → R)) : M ≃+ (Fin n → R) :=
  l.toAddEquiv.trans (unliftAddCoordinates R n)
private theorem linearCoordinatesAddEquiv_smul {R M : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] (n : ℕ)
    (l : M ≃ₗ[R] (ULift.{u} (Fin n) → R)) (b : R) (s : M) :
    linearCoordinatesAddEquiv n l (b • s) = b • linearCoordinatesAddEquiv n l s := by
  funext i
  exact congrFun (l.map_smul b s) (ULift.up i)

private noncomputable def pulledFrameCoordinates {S T : Scheme.{u}} (a : T ⟶ S) [Etale a]
    (E : S.Modules) [E.IsQuasicoherent] (n : ℕ)
    (q : (Modules.pullback a).obj E ≅ (Modules.pullback a).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) (V : T.Etale) :
    let M : T.Etale ⥤ S.Etale :=
      MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale a)
    (etaleTensorSectionsSheaf E).obj.obj (op (M.obj V)) ≃+ (Fin n → Γ(V.left, ⊤)) := by
  let M : T.Etale ⥤ S.Etale :=
    MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale a)
  exact linearCoordinatesAddEquiv (R := Γ((𝟭 Scheme).obj (M.obj V).left, ⊤))
    (M := Γ((tensorPullback (M.obj V).hom).obj E, ⊤)) n
    (frameCoordinates (M.obj V).hom E n (pullFrame a E n q V))

private theorem pulledFrameCoordinates_naturality {S T : Scheme.{u}} (a : T ⟶ S) [Etale a]
    (E : S.Modules) [E.IsQuasicoherent] (n : ℕ)
    (q : (Modules.pullback a).obj E ≅ (Modules.pullback a).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) :
    let M : T.Etale ⥤ S.Etale :=
      MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale a)
    ∀ (V W : T.Etale) (g : W ⟶ V)
      (s : (etaleTensorSectionsSheaf E).obj.obj (op (M.obj V))) (i : Fin n),
    pulledFrameCoordinates a E n q W ((etaleTensorSectionsSheaf E).obj.map (M.map g).op s) i =
      g.left.appTop (pulledFrameCoordinates a E n q V s i) := by
  intro M V W g s i
  have hn := frameCoordinates_sheaf_naturality (S := S) E (M.obj V) (M.obj W) (M.map g) n
    (pullFrame a E n q V) (pullFrame a E n q W)
    (pullFrame_naturality a E n q V W g) s i
  have hl : (M.map g).left = g.left := MorphismProperty.Over.map_map_left _ _ _
  exact hn.trans (congrArg (fun h : W.left ⟶ V.left ↦
    h.appTop (frameCoordinates (M.obj V).hom E n (pullFrame a E n q V)
      s (ULift.up i))) hl)


private theorem pulledFrameCoordinates_smul {S T : Scheme.{u}} (a : T ⟶ S) [Etale a]
    (E : S.Modules) [E.IsQuasicoherent] (n : ℕ)
    (q : (Modules.pullback a).obj E ≅ (Modules.pullback a).obj
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n)))) :
    let M : T.Etale ⥤ S.Etale :=
      MorphismProperty.Over.map (Y := S) ⊤ (inferInstance : Etale a)
    ∀ (V : T.Etale) (b : Γ(V.left, ⊤))
      (s : (etaleTensorSectionsSheaf E).obj.obj (op (M.obj V))),
    pulledFrameCoordinates a E n q V
      ((@id Γ((M.obj V).left, ⊤) b) •
        (@id Γ((tensorPullback (M.obj V).hom).obj E, ⊤) s)) =
      b • pulledFrameCoordinates a E n q V s := by
  intro M V b s
  exact linearCoordinatesAddEquiv_smul
    (R := Γ((𝟭 Scheme).obj (M.obj V).left, ⊤))
    (M := Γ((tensorPullback (M.obj V).hom).obj E, ⊤)) n
    (frameCoordinates (M.obj V).hom E n (pullFrame a E n q V)) b s


/-- Finite locally free modules admit natural scalar-compatible coordinates after an
étale test scheme is restricted to an affine neighbourhood of any given point.

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
label lemma-frobenius-linear-on-vb, the choice of a basis on an affine trivializing open.
(blueprint: lem-weil-pbc-frobenius-vector-bundle-local-frames)

Proof: Pull E back to U. Local freeness supplies a finite free trivialization near x;
intersect with an affine neighbourhood to obtain A, and reindex the finite basis by Fin n.
Pull this basis to every étale V over A. The free-module section equivalence identifies
sections with tuples of functions on V. Compose with the inverse ULift equivalence.
These are additive and scalar compatible because pullback of modules and the free-module
coordinate maps are linear. Their naturality follows by applying tensor-pullback
composition to each basis vector. The unit-normalized tensor comparison and the
etaleTensorHomEvaluation_naturality lemma identify this comparison with the restriction
map used by etaleTensorSectionsSheaf. In rank zero all coordinate types are singletons;
on an empty U there is no point x to consider. -/
theorem frobenius_vectorBundle_local_frames
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree] :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ n : ℕ,
      let f : A.toScheme ⟶ S := A.ι ≫ U.hom
      let M : A.toScheme.Etale ⥤ S.Etale :=
        MorphismProperty.Over.map (Y := S) ⊤
          (inferInstance : Etale f)
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        f inferInstance
      let G := (sheafCompose S.smallEtaleTopology
        AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (Modules.etaleTensorSectionsSheaf E)
      let act (V : A.toScheme.Etale) (b : Γ(V.left, ⊤))
          (s : (Modules.etaleTensorSectionsSheaf E).obj.obj (op (M.obj V))) :=
        (@id Γ((M.obj V).left, ⊤) b) •
          (@id Γ((Modules.tensorPullback (M.obj V).hom).obj E, ⊤) s)
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (a : Γ(V.left, ⊤))
          (s : (L.obj G).obj.obj (op V)),
          e V (ULift.up (act V a s.down)) =
                a • e V s) := by
  classical
  intro U x
  have hf := exists_affine_frame S E U x
  rcases hf with ⟨A, hA, hxA, n, ⟨q⟩⟩
  refine ⟨A, hA, hxA, n, ?_⟩
  intro a M L G act
  let F := Modules.etaleTensorSectionsSheaf E
  let c (V : A.toScheme.Etale) : F.obj.obj (op (M.obj V)) ≃+ (Fin n → Γ(V.left, ⊤)) :=
    pulledFrameCoordinates a E n q V
  have hc := pulledFrameCoordinates_naturality a E n q
  have ha := pulledFrameCoordinates_smul a E n q
  exact localized_additive_coordinates (S := S) a F n act c hc ha

end AlgebraicGeometry.Scheme
