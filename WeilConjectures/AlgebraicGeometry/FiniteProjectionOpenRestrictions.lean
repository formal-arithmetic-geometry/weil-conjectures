/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteProjectionExchangeData
import WeilConjectures.AlgebraicGeometry.FiniteProjectionTensorSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-! # Open restrictions for the finite projection formula -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

-- Work with the published open adjunction, using derived pullback on its right.
private abbrev openAdj {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :=
  derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction (ModuleCat A) j

omit [Finite A] in
private theorem unit_openUnitInv {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (K : Dcat A X) : (openAdj A j).unit.app K ≫ openUnitInv A j K = 𝟙 K := by
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit_isIso_of_L_fully_faithful
  have hd : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  simp only [openAdj, derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    openUnitInv, Category.assoc, Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id, Functor.id_obj]

omit [Finite A] in
private theorem openUnitInv_unit {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (K : Dcat A X) : openUnitInv A j K ≫ (openAdj A j).unit.app K = 𝟙 _ := by
  have hu : IsIso (openImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit_isIso_of_L_fully_faithful
  have hd : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit :=
    Adjunction.isIso_mapDerivedCategoryAdjunction_unit _
  simp only [openAdj, derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    openUnitInv, Category.assoc, IsIso.inv_hom_id_assoc, Iso.hom_inv_id_app]

omit [Finite A] in
private theorem beta_eq {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) :
    beta A s = leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat A) s := by
  ext K
  simp only [beta, leftDerivedOpenImmersionLowerShriekBaseChangeIso,
    leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso, Iso.symm_hom,
    Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.symm_inv, Category.assoc]

omit [Finite A] in
private theorem beta_unit {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) :
    (openAdj A j').unit.app ((pull A a).obj K) ≫
        (pull A j').map ((beta A s).inv.app K) =
      (pull A a).map ((openAdj A j).unit.app K) ≫
        (theta A s.toCommSq).inv.app ((ext A j).obj K) := by
  have ht := unit_mateEquiv (openAdj A j) (openAdj A j')
    (TwoSquare.mk _ _ _ _
      (leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso (ModuleCat A) s).inv) K
  rw [mateEquiv_leftDerivedUpperStarOpenImmersionLowerShriekBaseChangeIso_inv] at ht
  simpa only [beta_eq, TwoSquare.mk, pull, ext, theta, Functor.id_obj,
    Functor.comp_obj] using ht.symm

-- Bifunctoriality, kept in the fixed-scalar coordinates of the statement.
omit [Finite A] in
@[reassoc] private theorem tensorMap_comp {X : Scheme.{u}} {K K' K'' M M' M'' : Dcat A X}
    (a : K ⟶ K') (a' : K' ⟶ K'') (b : M ⟶ M') (b' : M' ⟶ M'') :
    tensorMap A (a ≫ a') (b ≫ b') = tensorMap A a b ≫ tensorMap A a' b' := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_comp
    (Prod.mkHom a b) (Prod.mkHom a' b')

omit [Finite A] in
private theorem tensorMap_id {X : Scheme.{u}} (K M : Dcat A X) :
    tensorMap A (𝟙 K) (𝟙 M) = 𝟙 (tensor A X K M) := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_id (K, M)

omit [Finite A] in
private theorem tensorMap_left {X : Scheme.{u}} {K K' : Dcat A X} (a : K ⟶ K')
    (M : Dcat A X) : tensorMap A a (𝟙 M) =
      ((derivedTensor (ModuleCat A) X).map a).app M := by
  unfold tensorMap
  rw [((derivedTensor (ModuleCat A) X).obj K').map_id, Category.comp_id]

omit [Finite A] in
private theorem tensorMap_right {X : Scheme.{u}} (K : Dcat A X)
    {M M' : Dcat A X} (b : M ⟶ M') : tensorMap A (𝟙 K) b =
      ((derivedTensor (ModuleCat A) X).obj K).map b := by
  unfold tensorMap
  rw [(derivedTensor (ModuleCat A) X).map_id, NatTrans.id_app]
  exact Category.id_comp _

omit [Finite A] in
private theorem tensorMap_comp_left {X : Scheme.{u}} {K K' K'' : Dcat A X}
    (a : K ⟶ K') (a' : K' ⟶ K'') (M : Dcat A X) :
    tensorMap A (a ≫ a') (𝟙 M) = tensorMap A a (𝟙 M) ≫ tensorMap A a' (𝟙 M) := by
  simpa only [Category.comp_id] using tensorMap_comp A a a' (𝟙 M) (𝟙 M)

private theorem tensorComparison_app {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (M P : Dcat A B) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat A) j).hom.app M).app P =
      tensorMap A ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).inv.app M)
        (𝟙 ((pull A j).obj P)) ≫
      (mu A j M P).inv ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).hom.app (tensor A B M P) := by
  rw [tensorMap_left]
  rfl

private theorem gamma_unit {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (K : Dcat A X) (P : Dcat A B) :
    (openAdj A j).unit.app (tensor A X K ((pull A j).obj P)) ≫
        (pull A j).map (gamma A j K P).inv =
      tensorMap A ((openAdj A j).unit.app K) (𝟙 ((pull A j).obj P)) ≫
        (mu A j ((ext A j).obj K) P).inv := by
  have ht := Adjunction.unit_app_comp_map_projectionMap_app_app
      (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j) (pull A j)
      (derivedTensor (ModuleCat A) X) (derivedTensor (ModuleCat A) B)
      (mapDerivedCategoryUpperStarDerivedTensorIso (ModuleCat A) j).hom K P
  have ht' : (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit.app
      (tensor A X K ((pull A j).obj P)) ≫
        (upperStar (ModuleCat A) j).mapDerivedCategory.map (gamma A j K P).inv =
      tensorMap A
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).unit.app K)
        (𝟙 ((pull A j).obj P)) ≫
      tensorMap A ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).inv.app
        ((ext A j).obj K)) (𝟙 ((pull A j).obj P)) ≫
      (mu A j ((ext A j).obj K) P).inv ≫
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).hom.app
        (tensor A B ((ext A j).obj K) P) := by
    simpa only [Adjunction.projectionMapTranspose, NatTrans.comp_app,
      Functor.whiskeringLeft₂_map_app_app_app_app,
      Functor.whiskeringLeft₂_obj_obj_map_app_app,
      tensorComparison_app, tensorMap_left, Functor.id_obj,
      Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, gamma,
      derivedTensorOpenImmersionLowerShriekIso, Iso.symm_inv, Iso.app_hom,
      derivedOpenImmersionLowerShriekProjectionIso_hom,
      derivedOpenImmersionLowerShriekProjectionMap, Functor.comp_obj] using ht
  rw [← cancel_mono ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat A) j).hom.app
    (tensor A B ((ext A j).obj K) P))]
  simp only [openAdj, derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.assoc]
  rw [NatIso.naturality_1, ht']
  simp only [tensorMap_left, Functor.map_comp, NatTrans.comp_app, Category.assoc]

private theorem restriction_of_unit
    {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) {V : D} {W : C} (e : V ≅ F.obj W)
    (u : G.obj (F.obj W) ⟶ W)
    (hu : adj.unit.app W ≫ u = 𝟙 W) (hu' : u ≫ adj.unit.app W = 𝟙 _)
    (t : W ⟶ G.obj V) (r : G.obj V ⟶ W)
    (ht : adj.unit.app W ≫ G.map e.inv = t) (hr : t ≫ r = 𝟙 W) :
    G.map e.hom ≫ u = r := by
  have : IsIso (adj.unit.app W) := ⟨u, hu, hu'⟩
  apply (cancel_epi (adj.unit.app W ≫ G.map e.inv)).1
  simp only [Category.assoc, ← G.map_comp_assoc, e.inv_hom_id, G.map_id, Category.id_comp]
  rw [← Category.assoc, ht, hr]
  exact hu

omit [Finite A] in
private theorem beta_restriction {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) :
    (pull A j').map ((beta A s).hom.app K) ≫ openUnitInv A j' ((pull A a).obj K) =
      (theta A s.toCommSq).hom.app ((ext A j).obj K) ≫
        (pull A a).map (openUnitInv A j K) := by
  apply restriction_of_unit (openAdj A j') ((beta A s).app K) _
    (unit_openUnitInv A j' _) (openUnitInv_unit A j' _)
    ((pull A a).map ((openAdj A j).unit.app K) ≫
      (theta A s.toCommSq).inv.app ((ext A j).obj K)) _ (beta_unit A s K)
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    unit_openUnitInv]
  exact (pull A a).map_id K

private theorem gamma_restriction {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    (K : Dcat A X) (P : Dcat A B) :
    (pull A j).map (gamma A j K P).hom ≫
        openUnitInv A j (tensor A X K ((pull A j).obj P)) =
      (mu A j ((ext A j).obj K) P).hom ≫
        tensorMap A (openUnitInv A j K) (𝟙 ((pull A j).obj P)) := by
  apply restriction_of_unit (openAdj A j) (gamma A j K P) _
    (unit_openUnitInv A j _) (openUnitInv_unit A j _)
    (tensorMap A ((openAdj A j).unit.app K) (𝟙 ((pull A j).obj P)) ≫
      (mu A j ((ext A j).obj K) P).inv) _ (gamma_unit A j K P)
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← tensorMap_comp,
    unit_openUnitInv, Category.comp_id, tensorMap_id]

omit [Finite A] in
private theorem openUnitInv_naturality {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j]
    {K M : Dcat A X} (f : K ⟶ M) :
    (pull A j).map ((ext A j).map f) ≫ openUnitInv A j M = openUnitInv A j K ≫ f := by
  have : IsIso ((openAdj A j).unit.app K) :=
    ⟨openUnitInv A j K, unit_openUnitInv A j K, openUnitInv_unit A j K⟩
  rw [← cancel_epi ((openAdj A j).unit.app K)]
  have hn := (openAdj A j).unit.naturality f
  change f ≫ (openAdj A j).unit.app M =
    (openAdj A j).unit.app K ≫ (pull A j).map ((ext A j).map f) at hn
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, unit_openUnitInv, Category.comp_id]
  rw [← Category.assoc, unit_openUnitInv]
  exact (Category.id_comp f).symm

private theorem mu_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' M M' : Dcat A Y} (a : K ⟶ K') (b : M ⟶ M') :
    (pull A f).map (tensorMap A a b) ≫ (mu A f K' M').hom =
      (mu A f K M).hom ≫ tensorMap A ((pull A f).map a) ((pull A f).map b) := by
  have hn := NatTrans.naturality
    ((Functor.uncurry.mapIso (leftDerivedUpperStarTensorNatIso (ModuleCat A) f)).hom)
    (Prod.mkHom a b)
  dsimp only [leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
    Functor.uncurry_obj_map, Functor.uncurry_map_app, Functor.mapIso_hom,
    Functor.postcompose₂_obj_obj_map_app, Functor.postcompose₂_obj_obj_obj_map,
    Functor.whiskeringLeft₂_obj_obj_map_app_app,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_map] at hn
  simpa only [tensorMap, Functor.map_comp, Category.assoc, pull, ext, tensor, mu,
    leftDerivedUpperStarTensorIso, Iso.app_hom, Functor.uncurry_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_map_app] using hn

-- Both restrictions are computed independently; neither route defines openSource.
private theorem openFirst_restriction
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    (pull A j').map (openFirst A s K P) ≫ openUnitInv A j' _ = openSource A s K P := by
  simp only [openFirst, Functor.map_comp, Category.assoc]
  slice_lhs 4 5 => rw [openUnitInv_naturality]
  slice_lhs 3 4 => rw [openUnitInv_naturality]
  slice_lhs 2 3 => rw [beta_restriction]
  simp only [Category.assoc]
  have hn := (theta A s.toCommSq).hom.naturality (gamma A j K P).hom
  change (pull A j').map ((pull A h).map (gamma A j K P).hom) ≫
      (theta A s.toCommSq).hom.app _ =
    (theta A s.toCommSq).hom.app _ ≫
      (pull A a).map ((pull A j).map (gamma A j K P).hom) at hn
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, gamma_restriction, Functor.map_comp_assoc]
  rw [reassoc_of% (mu_naturality A a (openUnitInv A j K) (𝟙 ((pull A j).obj P)))]
  simp only [pull, ← tensorMap_comp, Category.comp_id, openSource]
  erw [(pull A a).map_id ((pull A j).obj P), Category.id_comp]

private theorem openSecond_restriction
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    (pull A j').map (openSecond A s K P) ≫ openUnitInv A j' _ = openSource A s K P := by
  simp only [openSecond, Functor.map_comp, Category.assoc]
  rw [gamma_restriction,
    reassoc_of% (mu_naturality A j' ((beta A s).hom.app K) (𝟙 ((pull A h).obj P)))]
  simp only [pull, ← tensorMap_comp, Category.comp_id]
  rw [beta_restriction]
  have hf :
      tensorMap A
        ((theta A s.toCommSq).hom.app ((ext A j).obj K) ≫
          (pull A a).map (openUnitInv A j K)) (𝟙 _) =
      tensorMap A ((theta A s.toCommSq).hom.app ((ext A j).obj K))
          ((theta A s.toCommSq).hom.app P) ≫
        tensorMap A ((pull A a).map (openUnitInv A j K))
          ((theta A s.toCommSq).inv.app P) := by
    rw [← tensorMap_comp, Iso.hom_inv_id_app]
  erw [(pull A j').map_id ((pull A h).obj P)]
  dsimp only [Functor.comp_obj, pull] at hf
  erw [hf]
  rw [reassoc_of% (tensor_square A s.toCommSq)]
  rfl

omit [Finite A] in
private theorem tensorMap_isIso {X : Scheme.{u}} {K K' M M' : Dcat A X}
    (a : K ⟶ K') (b : M ⟶ M') [IsIso a] [IsIso b] : IsIso (tensorMap A a b) := by
  unfold tensorMap
  infer_instance

attribute [local instance] tensorMap_isIso

private theorem open_routes_equal
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    openFirst A s K P = openSecond A s K P := by
  have hrestr := (openFirst_restriction A s K P).trans (openSecond_restriction A s K P).symm
  have : IsIso (openFirst A s K P) := by
    dsimp only [openFirst]
    infer_instance
  let e := asIso (openFirst A s K P)
  have hu : IsIso (openUnitInv A j'
      (tensor A X' ((pull A a).obj K) ((pull A j').obj ((pull A h).obj P)))) :=
    ⟨(openAdj A j').unit.app _, openUnitInv_unit A j' _, unit_openUnitInv A j' _⟩
  have hu' : IsIso (openUnitInv A j'
      (tensor A X' ((pull A a).obj K) ((pull A h ⋙ pull A j').obj P))) := hu
  have hr := (cancel_mono (openUnitInv A j' _)).1 hrestr
  apply (cancel_epi e.inv).1
  apply ((openAdj A j').homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [hr]

/-- The two open projection routes agree, and both restrictions are the canonical source.
Source: prop-sf-pf-coherence.proof.md, open-factor and base-change paragraphs.
(blueprint: lem-sf-finite-projection-open-routes).

Proof: use the canonical derived open adjunction. Its inverse unit is openUnitInv.
The mate equation for beta and the projection-unit equation for gamma compute their
restrictions. Naturality moves the units and tensor comparison through the two routes;
the tensor square identifies the second route with the same openSource. Finally,
apply the open adjunction's hom-equivalence and cancel its invertible unit to recover
equality of the original routes from equality of their restrictions. -/
theorem open_factor_routes
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    openFirst A s K P = openSecond A s K P ∧
    (pull A j').map (openFirst A s K P) ≫ openUnitInv A j' _ = openSource A s K P ∧
    (pull A j').map (openSecond A s K P) ≫ openUnitInv A j' _ = openSource A s K P := by
  exact ⟨open_routes_equal A s K P,
    openFirst_restriction A s K P, openSecond_restriction A s K P⟩

end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
