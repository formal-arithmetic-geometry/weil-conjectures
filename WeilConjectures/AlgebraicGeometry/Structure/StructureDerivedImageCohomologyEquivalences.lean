/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalSingleAdjunctionTranspose
import WeilConjectures.AlgebraicGeometry.AffineHigherDirectImageCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.GlobalLerayUnitSquare
import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeLocalCalculation

/-! The affine Leray comparison before passing from modules to abelian sheaves.

Source: Stacks Project, Tags 01XK, 01FB and 03FD.
(blueprint: new-structure-derived-image-module-naturality)

Proof: Apply the affine Leray edge isomorphisms to the degree-one cohomology of
the two proper direct images. The cocycle square for the derived adjunction unit,
the canonical single pullback transpose, and naturality of direct-image composition
identify the resulting map with `moduleCohomologyFMap` for the structure h-map.
The identity-base truncated edge is invertible by its local-class formula and
sheafification of local cohomology. The total/classical comparison is the canonical
single comparison. This argument is uniform in the finite family and supplies the
two additive equivalences and their displayed square. -/

@[expose] public section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme

attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  AlgebraicGeometry.Scheme.Modules.instAbelian
set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] Scheme.Modules.pushforward RingedSpace.moduleDirectImage
  Scheme.Hom.toRingCatSheafHom globalLerayImage RingedSpace.globalSectionsFunctor
attribute [local instance 2000] SheafOfModules.instCategory SheafOfModules.instPreadditive
  SheafOfModules.instAbelian
attribute [local instance] Scheme.Modules.enoughInjectives
set_option synthInstance.maxSize 2048

private theorem sheafification_iso
    {V : Type*} [Category V] (J : GrothendieckTopology V)
    [HasWeakSheafify J AddCommGrpCat.{v}]
    (P Q : Vᵒᵖ ⥤ AddCommGrpCat.{v}) (M N : Sheaf J AddCommGrpCat.{v})
    (a : (presheafToSheaf J AddCommGrpCat.{v}).obj P ≅ M)
    (b : (presheafToSheaf J AddCommGrpCat.{v}).obj Q ≅ N)
    (l : P ≅ Q) (f : M ⟶ N)
    (h : (sheafificationAdjunction J AddCommGrpCat.{v}).unit.app P ≫
        (sheafToPresheaf J AddCommGrpCat.{v}).map a.hom ≫
        (sheafToPresheaf J AddCommGrpCat.{v}).map f =
      l.hom ≫ (sheafificationAdjunction J AddCommGrpCat.{v}).unit.app Q ≫
        (sheafToPresheaf J AddCommGrpCat.{v}).map b.hom) : IsIso f := by
  have hf : a.hom ≫ f = (presheafToSheaf J AddCommGrpCat.{v}).map l.hom ≫ b.hom := by
    apply ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ _).injective
    have hn := (sheafificationAdjunction J AddCommGrpCat.{v}).unit.naturality l.hom
    change l.hom ≫ (sheafificationAdjunction J AddCommGrpCat.{v}).unit.app Q =
      (sheafificationAdjunction J AddCommGrpCat.{v}).unit.app P ≫
        (sheafToPresheaf J AddCommGrpCat.{v}).map
          ((presheafToSheaf J AddCommGrpCat.{v}).map l.hom) at hn
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    calc
      _ = l.hom ≫ (sheafificationAdjunction J AddCommGrpCat.{v}).unit.app Q ≫
          (sheafToPresheaf J AddCommGrpCat.{v}).map b.hom := h
      _ = _ := by rw [← Category.assoc, hn, Category.assoc]
  have : IsIso (a.hom ≫ f) := hf ▸ inferInstance
  exact IsIso.of_isIso_comp_left a.hom f

private theorem topEdgeLocalClass_eq
    [∀ X : Scheme.{v},
      HasDerivedCategory.{w} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    (T : Scheme.{v}) (q : ℤ) (K : schemeDerivedCategory T) :
    RingedSpace.topEdgeLocalClass T.toRingedSpace q K =
      (sheafificationAdjunction (Opens.grothendieckTopology T) AddCommGrpCat.{v}).unit.app
          ((RingedSpace.localHypercohomologyPresheaf T.toRingedSpace q).obj K) ≫
        (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{v}).map
          (RingedSpace.localHypercohomologySheafificationAt q K).hom := by
  rfl

private theorem identity_presheaf_square (T : Scheme.{v}) (M : T.Modules)
    (P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{v})
    (θ : P ⟶ (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{v}).obj
      ((SheafOfModules.toSheaf (moduleRings T.toRingedSpace)).obj M)) :
    Functor.whiskerLeft (Opens.map ((𝟙 T : T ⟶ T).base)).op θ ≫
      (sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{v}).map
        ((SheafOfModules.toSheaf (moduleRings T.toRingedSpace)).map
          ((Modules.pushforwardId T).hom.app M)) =
      (Functor.leftUnitor P).hom ≫ θ := by
  change Functor.whiskerLeft (𝟭 _) θ ≫ (Functor.leftUnitor _).hom =
    (Functor.leftUnitor P).hom ≫ θ
  rfl

set_option maxHeartbeats 1600000 in
-- Sheafification comparisons cross several presentations of the module category.
private theorem identity_edge_isIso
    [∀ X : Scheme.{v},
      HasDerivedCategory.{w} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    (T : Scheme.{v}) (q : ℤ) (K : schemeDerivedCategory T) :
    IsIso (topEdgeTruncatedCounit (𝟙 T) q K) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let R := moduleRings T.toRingedSpace
  let U := SheafOfModules.toSheaf R
  let E := (schemeDerivedDirectImage (𝟙 T)).obj K
  let P := (RingedSpace.localHypercohomologyPresheaf T.toRingedSpace q).obj E
  let Q := (RingedSpace.localHypercohomologyPresheaf T.toRingedSpace q).obj K
  let l : P ≅ Q :=
    RingedSpace.topEdgeLocalLeray (Scheme.Hom.toLRSHom (𝟙 T)).toShHom q K ≪≫
      squareInverseOpenComparison (𝟙 T) q K ≪≫ Functor.leftUnitor Q
  let f := U.map (topEdgeTruncatedCounit (𝟙 T) q K) ≫
    U.map ((Scheme.Modules.pushforwardId T).hom.app
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) q).obj K))
  have hf : IsIso f := by
    apply sheafification_iso (Opens.grothendieckTopology T) P Q _ _
      (RingedSpace.localHypercohomologySheafificationAt q E)
      (RingedSpace.localHypercohomologySheafificationAt q K) l f
    let θE := RingedSpace.topEdgeLocalClass T.toRingedSpace q E
    let θK := RingedSpace.topEdgeLocalClass T.toRingedSpace q K
    let localLeray := RingedSpace.topEdgeLocalLeray (Scheme.Hom.toLRSHom (𝟙 T)).toShHom q K
    let σ := squareInverseOpenComparison (𝟙 T) q K
    let V := sheafToPresheaf (Opens.grothendieckTopology T) AddCommGrpCat.{v}
    have hc : θE ≫ V.map (U.map (topEdgeTruncatedCounit (𝟙 T) q K)) =
        localLeray.hom ≫ σ.hom ≫
          Functor.whiskerLeft (Opens.map ((𝟙 T : T ⟶ T).base)).op θK := by
      apply NatTrans.ext
      funext W
      have h := topEdgeTruncatedCounit_localClass (𝟙 T) q K W
      rw [squareInverseOpenComparison_class] at h
      with_unfolding_all simpa only [θE, θK, localLeray, σ, V, U, R, E,
        sheafToPresheaf, ObjectProperty.ι_map, ObjectProperty.ι_obj,
        NatTrans.comp_app, Category.assoc] using h
    rw [← Category.assoc, ← topEdgeLocalClass_eq T q E, ← topEdgeLocalClass_eq T q K]
    change θE ≫ V.map f = l.hom ≫ θK
    dsimp only [f, l, Iso.trans_hom]
    rw [Functor.map_comp, ← Category.assoc, hc]
    simp only [Category.assoc]
    apply congrArg (fun k ↦ localLeray.hom ≫ σ.hom ≫ k)
    exact identity_presheaf_square T
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) q).obj K) Q θK
  have hf' : IsIso (U.map (topEdgeTruncatedCounit (𝟙 T) q K) ≫
      U.map ((Scheme.Modules.pushforwardId T).hom.app
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) q).obj K))) := hf
  have hm : IsIso (U.map ((Scheme.Modules.pushforwardId T).hom.app
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) q).obj K))) := inferInstance
  have hfirst : IsIso (U.map (topEdgeTruncatedCounit (𝟙 T) q K)) :=
    IsIso.of_isIso_comp_right
      (U.map (topEdgeTruncatedCounit (𝟙 T) q K))
      (U.map ((Scheme.Modules.pushforwardId T).hom.app
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{v} (moduleRings T.toRingedSpace)) q).obj K)))
  exact isIso_of_reflects_iso _ U

private theorem add_bijective_of_isIso {X Y : AddCommGrpCat.{v}} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f := ConcreteCategory.bijective_of_isIso _

private noncomputable def affineLerayEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q] :
    (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (SheafOfModules.unit X.ringCatSheaf) ≃+
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
          SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)).obj
        ((schemeDerivedDirectImage q).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)))) := by
  classical
  let eps := Classical.choose (exists_lerayEdge_isIso_of_vanishing q)
  have hqc : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{v, v, v}
  have hv (p r : ℕ) (hr : 0 < r) :
      IsZero ((RingedSpace.moduleCohomology T.toRingedSpace r).obj
        (((RingedSpace.moduleDirectImage q.toLRSHom.toShHom).rightDerived p).obj
          (SheafOfModules.unit X.ringCatSheaf))) :=
    isZero_affine_higherDirectImage_moduleCohomology q _ hqc p r hr
  let : IsIso ((eps 1).app (SheafOfModules.unit X.ringCatSheaf)) :=
    (Classical.choose_spec (exists_lerayEdge_isIso_of_vanishing q)).2 _ hv 1
  let c := globalLerayComparison q (SheafOfModules.unit X.ringCatSheaf) 1
  let cm := (forget₂ _ AddCommGrpCat).map
    ((SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)).map c.inv)
  exact (AddEquiv.ofBijective ((eps 1).app _).hom
    (add_bijective_of_isIso _)).trans
      (AddEquiv.ofBijective cm.hom (ConcreteCategory.bijective_of_isIso _))

private theorem affineLerayEquiv_apply
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q]
    (x : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
      (SheafOfModules.unit X.ringCatSheaf)) :
    affineLerayEquiv q x =
      (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
        (globalLerayComparison q (SheafOfModules.unit X.ringCatSheaf) 1).inv
          (((Classical.choose (exists_lerayEdge_isIso_of_vanishing q)) 1).app
            (SheafOfModules.unit X.ringCatSheaf) x) := by
  with_unfolding_all rfl

attribute [local irreducible] affineLerayEquiv

private theorem evaluation_map_apply {T : Scheme.{v}} {M N : T.Modules}
    (f : M ⟶ N)
    (x : (SheafOfModules.evaluation (moduleRings T.toRingedSpace) (op ⊤)).obj M) :
    (SheafOfModules.evaluation (moduleRings T.toRingedSpace) (op ⊤)).map f x =
      Modules.Hom.app f ⊤ x := by
  with_unfolding_all rfl

private theorem relative_unit_transpose
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X Y : Scheme.{v}} (q : X ⟶ T) (j : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (a : (Modules.pullback j).obj F ⟶ G) :
    relativeMVUnit j q ((DerivedCategory.singleFunctor _ 0).obj F) ≫
      (schemeDerivedDirectImage (j ≫ q)).map
        (Modules.canonicalSinglePullbackMap j F ≫
          (DerivedCategory.singleFunctor _ 0).map a) =
    (schemeDerivedDirectImage q).map
      ((DerivedCategory.singleFunctor _ 0).map
        ((Modules.pullbackPushforwardAdjunction j).homEquiv _ _ a) ≫
          Modules.canonicalSingleDirectImageMap j G) ≫
      (relativeMVImageComp j q).hom.app ((DerivedCategory.singleFunctor _ 0).obj G) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let c := Modules.canonicalSinglePullbackMap j F ≫
    (DerivedCategory.singleFunctor _ 0).map a
  have h := Modules.canonicalSingleAdjunctionTranspose j F G a
  change (relativeMVAdj j).homEquiv _ _ c = _ at h
  rw [Adjunction.homEquiv_unit] at h
  unfold relativeMVUnit
  rw [Category.assoc, ← (relativeMVImageComp j q).hom.naturality c]
  simp only [Functor.comp_map]
  rw [← Category.assoc, ← Functor.map_comp, h]

set_option maxHeartbeats 1600000 in
-- The large comparison square needs extra heartbeats for category transports.
/-- The affine Leray module equivalence is natural for maps of proper total spaces.
Source: Stacks Project, Tags 01XK (affine higher-image vanishing), 01FB (h-maps),
and 03FD (module cohomology); local classes and sheafification as in Tag 0BKJ.
(blueprint: new-structure-derived-image-module-naturality).

Proof: The cocycle Leray edge is bijective by affine higher-image vanishing; compose
with the inverse total/classical comparison. The identity-base truncated edge is an
isomorphism since its local-class square sheafifies to a square of isomorphisms.
Naturality of relativeMVImageComp and the canonical single adjunction transpose
identify the displayed map b with the derived-square unit alpha followed by an
isomorphism psi. Apply globalLeray_unitSquare with the identity base, then compose
the target comparison with the identity edge and inverse psi. The same source Leray
equivalence works for all indices, including an empty family. -/
theorem structure_derived_image_module_naturality
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    {T X : Scheme.{v}} [IsAffine T] (q : X ⟶ T) [IsProper q]
    {n : ℕ} (Xi : Fin n → Scheme.{v}) (qi : ∀ i, Xi i ⟶ T)
    [∀ i, IsProper (qi i)] (j : ∀ i, Xi i ⟶ X) (hj : ∀ i, j i ≫ q = qi i) :
    let A := (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings X.toRingedSpace)) 0).obj
        (SheafOfModules.unit X.ringCatSheaf)
    let Ai := fun i ↦ (DerivedCategory.singleFunctor
      (SheafOfModules.{v} (moduleRings (Xi i).toRingedSpace)) 0).obj
        (SheafOfModules.unit (Xi i).ringCatSheaf)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1 ⋙
      SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)
    let b := fun i ↦ relativeMVUnit (j i) q A ≫
      (schemeDerivedDirectImage (j i ≫ q)).map
        (Modules.canonicalSinglePullbackMap (j i) (SheafOfModules.unit X.ringCatSheaf) ≫
          (DerivedCategory.singleFunctor _ 0).map (Modules.pullbackObjUnitIso (j i)).hom) ≫
      eqToHom (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj (Ai i)) (hj i))
    ∃ e : H.obj ((schemeDerivedDirectImage q).obj A) ≃+
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (SheafOfModules.unit X.ringCatSheaf),
      ∀ i, ∃ ei : H.obj ((schemeDerivedDirectImage (qi i)).obj (Ai i)) ≃+
          (RingedSpace.moduleCohomology (Xi i).toRingedSpace 1).obj
            (SheafOfModules.unit (Xi i).ringCatSheaf),
        ∀ z, ei (H.map (b i) z) =
          Modules.moduleCohomologyFMap (j i)
            (SheafOfModules.unitToPushforwardObjUnit (j i).toRingCatSheafHom) 1 (e z) := by
  classical
  intro A Ai H b₀
  let H₁ := DerivedCategory.homologyFunctor
    (SheafOfModules.{v} (moduleRings T.toRingedSpace)) 1
  let Γ := SheafOfModules.evaluation (moduleRings T.toRingedSpace) (.op ⊤)
  refine ⟨(affineLerayEquiv q).symm, ?_⟩
  intro i
  let K := (schemeDerivedDirectImage (qi i)).obj (Ai i)
  have hs : j i ≫ q = qi i ≫ 𝟙 T := by simpa using hj i
  let r := derivedSquareRightComparison q (qi i) (𝟙 T) (j i) hs
  let ψ : (schemeDerivedDirectImage (𝟙 T)).obj K ≅ K :=
    (r.app (Ai i)).symm ≪≫ (relativeMVImageComp (j i) q).app (Ai i) ≪≫
      eqToIso (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj (Ai i)) (hj i))
  let c := Modules.canonicalSinglePullbackMap (j i)
    (SheafOfModules.unit X.ringCatSheaf) ≫
      (DerivedCategory.singleFunctor _ 0).map (Modules.pullbackObjUnitIso (j i)).hom
  let φ := SheafOfModules.unitToPushforwardObjUnit (j i).toRingCatSheafHom
  let α := derivedSquareUnitMap q (qi i) (𝟙 T) (j i) hs
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit (Xi i).ringCatSheaf) φ
  let b := relativeMVUnit (j i) q A ≫ (schemeDerivedDirectImage (j i ≫ q)).map c ≫
    eqToHom (congrArg (fun t ↦ (schemeDerivedDirectImage t).obj (Ai i)) (hj i))
  have hb : b = α ≫ ψ.hom := by
    have ht := relative_unit_transpose q (j i) (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit (Xi i).ringCatSheaf) (Modules.pullbackObjUnitIso (j i)).hom
    have ha : (Modules.pullbackPushforwardAdjunction (j i)).homEquiv _ _
        (Modules.pullbackObjUnitIso (j i)).hom = φ :=
      SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
    rw [ha] at ht
    dsimp only [b]
    rw [← Category.assoc]
    change (relativeMVUnit (j i) q A ≫ (schemeDerivedDirectImage (j i ≫ q)).map c) ≫ _ = _
    rw [ht]
    dsimp only [α, derivedSquareUnitMap, ψ, r, Iso.trans_hom, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv]
    dsimp only [Ai]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, eqToIso.hom]
  have heiso : IsIso (topEdgeTruncatedCounit (𝟙 T) 1 K) := identity_edge_isIso T 1 K
  let edge := topEdgeTruncatedCounit (𝟙 T) 1 K ≫
    (Modules.pushforwardId T).hom.app (H₁.obj K)
  let edgeIso : H₁.obj ((schemeDerivedDirectImage (𝟙 T)).obj K) ≅ H₁.obj K := asIso edge
  let θiso := H.mapIso ψ.symm ≪≫ Γ.mapIso edgeIso
  let θ := ((forget₂ _ AddCommGrpCat).mapIso θiso).addCommGroupIsoToAddEquiv
  refine ⟨θ.trans (affineLerayEquiv (qi i)).symm, ?_⟩
  intro z
  apply (affineLerayEquiv (qi i)).injective
  change affineLerayEquiv (qi i) ((affineLerayEquiv (qi i)).symm
      (θ (H.map b z))) = affineLerayEquiv (qi i)
    (Modules.moduleCohomologyFMap (j i) φ 1 ((affineLerayEquiv q).symm z))
  rw [AddEquiv.apply_symm_apply]
  have hg := globalLeray_unitSquare q (qi i) (𝟙 T) (j i) hs
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit (Xi i).ringCatSheaf)
    φ 1 (topEdgeTruncatedCounit (𝟙 T) 1
      (globalLerayImage (qi i) (SheafOfModules.unit (Xi i).ringCatSheaf)))
    (topEdgeTruncatedCounit_localClass (𝟙 T) 1 _) ((affineLerayEquiv q).symm z)
  rw [← affineLerayEquiv_apply (qi i), ← affineLerayEquiv_apply q] at hg
  have hg' : affineLerayEquiv (qi i)
      (Modules.moduleCohomologyFMap (j i) φ 1 ((affineLerayEquiv q).symm z)) =
      Γ.map edge (H.map α (affineLerayEquiv q ((affineLerayEquiv q).symm z))) := by
    with_unfolding_all refine hg.trans ?_
    with_unfolding_all simp only [Scheme.Hom.id_base, eqToHom_refl,
      edge, H, H₁, Γ, globalLerayUnitMap, globalLerayImage,
      RingedSpace.globalSectionsFunctor, Modules.Hom.comp_app,
      Functor.comp_map, Functor.map_comp,
      ConcreteCategory.comp_apply, evaluation_map_apply,
      Modules.pushforwardId_hom_app_app]
    let y := Modules.Hom.app (topEdgeTruncatedCounit (𝟙 T) 1 K) ⊤
      (Modules.Hom.app (H₁.map α) ⊤ (affineLerayEquiv q ((affineLerayEquiv q).symm z)))
    with_unfolding_all change (H₁.obj K).val.presheaf.map (𝟙 (op ⊤)) y = y
    with_unfolding_all exact
      ConcreteCategory.congr_hom ((H₁.obj K).val.presheaf.map_id (op ⊤)) y
  rw [AddEquiv.apply_symm_apply] at hg'
  rw [hg', hb, H.map_comp]
  change Γ.map edge (H.map ψ.inv (H.map ψ.hom (H.map α z))) = _
  have hh := ConcreteCategory.congr_hom (H.mapIso ψ).hom_inv_id (H.map α z)
  exact congrArg (fun x ↦ Γ.map edge x) hh

end AlgebraicGeometry.Scheme
