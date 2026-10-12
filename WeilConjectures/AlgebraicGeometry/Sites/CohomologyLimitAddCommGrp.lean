/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Continuity of étale cohomology of abelian sheaves
-/

@[expose] public section

universe w w' u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D]

/-- The canonical isomorphism `Adjunction.leftAdjointUniq` of two left adjoints of `G` does not
change when both adjunctions are transported along a morphism `κ : G ⟶ G'` to adjunctions with
right adjoint `G'` which is compatible with the units. -/
lemma leftAdjointUniq_eq_of_unit {F F' : C ⥤ D} {G G' : D ⥤ C} (adj₁ : F ⊣ G) (adj₂ : F' ⊣ G)
    (adj₁' : F ⊣ G') (adj₂' : F' ⊣ G') (κ : G ⟶ G')
    (h₁ : ∀ x, adj₁'.unit.app x = adj₁.unit.app x ≫ κ.app (F.obj x))
    (h₂ : ∀ x, adj₂'.unit.app x = adj₂.unit.app x ≫ κ.app (F'.obj x)) :
    leftAdjointUniq adj₁ adj₂ = leftAdjointUniq adj₁' adj₂' := by
  ext x
  apply (adj₁'.homEquiv _ _).injective
  rw [homEquiv_leftAdjointUniq_hom_app, homEquiv_unit, h₁, Category.assoc, ← κ.naturality,
    ← Category.assoc, ← homEquiv_unit, homEquiv_leftAdjointUniq_hom_app, h₂]

end CategoryTheory.Adjunction

namespace CategoryTheory

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) (D : Type*) [Category* D]
  [HasWeakSheafify J D]

/-- The units of the adjunctions `constantSheaf ⊣ Γ(T, -)` for two terminal objects `T`, `T'`
differ by the restriction along `T' ⟶ T`. -/
lemma constantSheafAdj_unit_app_comp_map {T T' : C} (hT : IsTerminal T) (hT' : IsTerminal T')
    (a : D) :
    (constantSheafAdj J D hT).unit.app a ≫ ((constantSheaf J D).obj a).obj.map (hT.from T').op =
      (constantSheafAdj J D hT').unit.app a := by
  simp only [constantSheafAdj, Adjunction.comp_unit_app, constantPresheafAdj_unit_app,
    evaluation_obj_map, Category.assoc]
  erw [← ((sheafificationAdjunction J D).unit.app ((Functor.const Cᵒᵖ).obj a)).naturality]
  simp

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The identification `g^* Λ_Y ≅ Λ_Z` of `AlgebraicGeometry.Etale.constantSheafCompUpperStarIso`
is the one of `AlgebraicGeometry.Scheme.upperStarConstantSheafIso`: both come from the uniqueness
of left adjoints, for two different choices of terminal objects of the small étale sites. -/
lemma constantSheafCompUpperStarIso_eq_upperStarConstantSheafIso {Y Z : Scheme.{u}}
    (g : Z ⟶ Y) :
    constantSheafCompUpperStarIso Λ g =
      Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g := by
  rw [constantSheafCompUpperStarIso, Scheme.upperStarConstantSheafIso]
  refine (Adjunction.leftAdjointUniq_eq_of_unit _ _ _ _
    ((sheafSections Z.smallEtaleTopology _).map (terminalIsTerminal.from
      ((MorphismProperty.Over.pullback @Etale ⊤ g).obj (Scheme.Etale.mk (𝟙 Y)))).op)
    (fun a ↦ ?_) (fun a ↦ ?_)).symm
  · simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
      Adjunction.comp_unit_app, NatIso.ofComponents_hom_app, Iso.refl_hom,
      Category.assoc]
    rw [← constantSheafAdj_unit_app_comp_map _ _ terminalIsTerminal
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y), Category.assoc]
    congr 1
    erw [Category.comp_id]
    erw [((upperStarLowerStarAdjunction (ModuleCat Λ) g).unit.app _).hom.naturality]
    congr 1
    simp only [lowerStarCompSheafSectionsTerminalIso, NatIso.ofComponents_hom_app]
    erw [Functor.mapIso_hom, ← Functor.map_comp]
    exact congrArg (((g)^*[ModuleCat Λ]).obj ((constantSheaf Y.smallEtaleTopology
      (ModuleCat Λ)).obj a)).obj.map (Quiver.Hom.unop_inj (IsTerminal.hom_ext
        (terminalIsTerminal.ofIso (PreservesTerminal.iso (Scheme.Hom.Etale g)).symm) _ _))
  · exact (constantSheafAdj_unit_app_comp_map _ _ _ _ a).symm

section Forget

variable {X Y Z : Scheme.{u}}

set_option hygiene false in
/-- The functor taking the underlying abelian sheaf of an étale sheaf of `Λ`-modules. -/
local notation "Φ" X:max => sheafCompose (Scheme.smallEtaleTopology X)
  (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Taking underlying abelian sheaves commutes with the composition isomorphisms of the
pushforwards. -/
lemma lowerStarComp_hom_app_sheafCompose_forget₂ (h₁ : X ⟶ Y) (h₂ : Y ⟶ Z)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂).hom.app ((Φ X).obj F) =
      (Φ Z).map ((lowerStarComp (ModuleCat.{u + 1} Λ) h₁ h₂).hom.app F) :=
  rfl

/-- The comparison `f^* (forget₂ G) ⟶ forget₂ (f^* G)` of
`AlgebraicGeometry.Etale.upperStarForget₂Comparison` is compatible with the composition
isomorphisms of the pullbacks. -/
lemma upperStarComp_hom_app_comp_upperStarForget₂Comparison (h₁ : X ⟶ Y) (h₂ : Y ⟶ Z)
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarComp AddCommGrpCat.{u + 1} h₁ h₂).hom.app ((Φ Z).obj G) ≫
        ((h₁)^*[AddCommGrpCat.{u + 1}]).map (upperStarForget₂Comparison Λ h₂ G) ≫
          upperStarForget₂Comparison Λ h₁ (((h₂)^*[ModuleCat.{u + 1} Λ]).obj G) =
      upperStarForget₂Comparison Λ (h₁ ≫ h₂) G ≫
        (Φ X).map ((upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂).hom.app G) := by
  apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (h₁ ≫ h₂)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [
    reassoc_of% unit_comp_lowerStar_map_upperStarForget₂Comparison,
    reassoc_of% (upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} h₁ h₂ ((Φ Z).obj G)),
    ← (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂).hom.naturality_assoc,
    ← (lowerStarComp AddCommGrpCat.{u + 1} h₁ h₂).hom.naturality,
    lowerStarComp_hom_app_sheafCompose_forget₂]
  simp only [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp_assoc (h₂)_*[AddCommGrpCat.{u + 1}],
    ← Functor.comp_map (h₁)^*[AddCommGrpCat.{u + 1}] (h₁)_*[AddCommGrpCat.{u + 1}],
    ← (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h₁).unit.naturality, Functor.id_map,
    Functor.map_comp_assoc, reassoc_of% unit_comp_lowerStar_map_upperStarForget₂Comparison,
    ← Functor.map_comp_assoc (h₂)_*[AddCommGrpCat.{u + 1}],
    unit_comp_lowerStar_map_upperStarForget₂Comparison, lowerStar_map_sheafCompose_forget₂_map,
    lowerStar_map_sheafCompose_forget₂_map]
  erw [← Functor.map_comp]
  refine Eq.trans ?_ ((Φ Z).map_comp
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (h₁ ≫ h₂)).unit.app G)
    ((h₁ ≫ h₂)_*[ModuleCat.{u + 1} Λ].map
      ((upperStarComp (ModuleCat.{u + 1} Λ) h₁ h₂).hom.app G)))
  rw [upperStarComp_hom_app_unit_app (ModuleCat.{u + 1} Λ) h₁ h₂ G, Adjunction.comp_unit_app,
    Category.assoc]
  exact ((Φ Z).map_comp _ _).symm

/-- Naturality of the comparison `f^* (forget₂ G) ⟶ forget₂ (f^* G)` of
`AlgebraicGeometry.Etale.upperStarForget₂Comparison` in `G`. -/
@[reassoc]
lemma upperStarForget₂Comparison_naturality (f : X ⟶ Y)
    {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : G ⟶ G') :
    ((f)^*[AddCommGrpCat.{u + 1}]).map ((Φ Y).map φ) ≫ upperStarForget₂Comparison Λ f G' =
      upperStarForget₂Comparison Λ f G ≫ (Φ X).map (((f)^*[ModuleCat.{u + 1} Λ]).map φ) := by
  rw [← upperStarForget₂_natTrans_app, ← upperStarForget₂_natTrans_app]
  exact (upperStarForget₂ Λ f).natTrans.naturality φ

end Forget

end AlgebraicGeometry.Etale

namespace CategoryTheory.Abelian.Ext

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]

/-- An isomorphism `e : Y ≅ Y'` induces an isomorphism `Ext X Y n ≃+ Ext X Y' n` of
`Ext`-groups by postcomposition with `e`. -/
@[simps! apply]
noncomputable def postcompAddEquiv (X : C) {Y Y' : C} (e : Y ≅ Y') (n : ℕ) :
    Ext X Y n ≃+ Ext X Y' n where
  __ := (Ext.mk₀ e.hom).postcomp X (add_zero n)
  invFun := (Ext.mk₀ e.inv).postcomp X (add_zero n)
  left_inv _ := by simp [Ext.mk₀_comp_mk₀]
  right_inv _ := by simp [Ext.mk₀_comp_mk₀]

variable {D : Type*} [Category* D] [Abelian D] [HasExt.{w'} D] [EnoughInjectives C]
  {F G : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Pushing `Ext`-classes forward along isomorphic exact functors gives the same class up to
the isomorphism. -/
lemma mapExactFunctor_eq_of_iso (τ : F ≅ G) {A B : C} {n : ℕ} (x : Ext A B n) :
    x.mapExactFunctor F = (mk₀ (τ.hom.app A)).comp
      ((x.mapExactFunctor G).comp (mk₀ (τ.inv.app B)) (add_zero n)) (zero_add n) := by
  rw [← comp_assoc_of_third_deg_zero, ← mapExactFunctor_comp_mk₀_app F G τ.hom,
    comp_assoc_of_third_deg_zero, mk₀_comp_mk₀, Iso.hom_inv_id_app, comp_mk₀_id]

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.Etale

section Transport

set_option hygiene false in
/-- The functor taking the underlying abelian sheaf of an étale sheaf of `ULift ℤ`-modules. -/
local notation "Ψ" X:max => sheafCompose (Scheme.smallEtaleTopology X)
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})

variable {S : Scheme.{u}}
  (e : (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ≅
    (Ψ S).obj (SemiSimplicialObject.constSheaf S.smallEtaleTopology (ULift.{u + 1} ℤ)))
  {G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))}
  {F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (ε : (Ψ S).obj G ≅ F)

/-- For `p : Y ⟶ S`, the identification of the constant sheaf `ℤ` on `Y` with the underlying
abelian sheaf of the constant sheaf of `ULift ℤ`-modules, transported along `p` from an
identification `e` on `S`. -/
noncomputable def constantSheafForget₂Iso {Y : Scheme.{u}} (p : Y ⟶ S) :
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      (Ψ Y).obj (SemiSimplicialObject.constSheaf Y.smallEtaleTopology (ULift.{u + 1} ℤ)) :=
  ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} p).app _).symm ≪≫
    ((p)^*[AddCommGrpCat.{u + 1}]).mapIso e ≪≫
    asIso (upperStarForget₂Comparison (ULift.{u + 1} ℤ) p _) ≪≫
    (Ψ Y).mapIso ((constantSheafCompUpperStarIso (ULift.{u + 1} ℤ) p).app _)

/-- For `p : Y ⟶ S`, the identification `forget₂ (p^* G) ≅ p^* F` induced by an
identification `ε : forget₂ G ≅ F`. -/
noncomputable def forget₂UpperStarObjIso {Y : Scheme.{u}} (p : Y ⟶ S) :
    (Ψ Y).obj (((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).obj G) ≅
      ((p)^*[AddCommGrpCat.{u + 1}]).obj F :=
  (asIso (upperStarForget₂Comparison (ULift.{u + 1} ℤ) p G)).symm ≪≫
    ((p)^*[AddCommGrpCat.{u + 1}]).mapIso ε

/-- For `p : Y ⟶ S`, the étale cohomology of the pullback `p^* G` of a sheaf of
`ULift ℤ`-modules is the cohomology of the abelian sheaf `p^* F`, for `F ≅ forget₂ G`. -/
noncomputable def cohomologyForget₂AddEquiv {Y : Scheme.{u}} (p : Y ⟶ S) (q : ℕ) :
    Ext (SemiSimplicialObject.constSheaf Y.smallEtaleTopology (ULift.{u + 1} ℤ))
        (((p)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).obj G) q ≃+
      Sheaf.H (((p)^*[AddCommGrpCat.{u + 1}]).obj F) q :=
  ((AddEquiv.ofBijective _
      (Functor.mapExt_bijective_of_preservesInjectiveObjects (Ψ Y) _ _ q)).trans
    (Ext.postcompAddEquiv _ (forget₂UpperStarObjIso ε p) q)).trans
    (Ext.precompAddEquiv (constantSheafForget₂Iso e p) _ q)

lemma cohomologyForget₂AddEquiv_apply {Y : Scheme.{u}} (p : Y ⟶ S) (q : ℕ) (x) :
    cohomologyForget₂AddEquiv e ε p q x = (Ext.mk₀ (constantSheafForget₂Iso e p).hom).comp
      ((x.mapExactFunctor (Ψ Y)).comp (Ext.mk₀ (forget₂UpperStarObjIso ε p).hom) (add_zero q))
      (zero_add q) :=
  rfl

/-- The identifications `AlgebraicGeometry.Etale.constantSheafForget₂Iso` are compatible with
pullbacks. -/
lemma constantSheafForget₂Iso_hom_comp {Y Z : Scheme.{u}} (pZ : Z ⟶ S) (f : Y ⟶ Z) :
    (constantSheafForget₂Iso e (f ≫ pZ)).hom ≫ (Ψ Y).map
        ((constantSheafCompUpperStarIso (ULift.{u + 1} ℤ) f).inv.app _) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).inv.app _ ≫
        ((f)^*[AddCommGrpCat.{u + 1}]).map (constantSheafForget₂Iso e pZ).hom ≫
        upperStarForget₂Comparison (ULift.{u + 1} ℤ) f _ := by
  simp only [constantSheafForget₂Iso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    asIso_hom, Iso.app_hom, constantSheafCompUpperStarIso_eq_upperStarConstantSheafIso,
    Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (f ≫ pZ)).hom.app _),
    Iso.hom_inv_id_app_assoc, ← Scheme.upperStarConstantSheafIso_comp AddCommGrpCat.{u + 1} f pZ,
    Category.assoc, Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (upperStarComp AddCommGrpCat.{u + 1} f pZ).hom.naturality e.hom
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  congr 1
  rw [upperStarForget₂Comparison_naturality,
    reassoc_of% upperStarComp_hom_app_comp_upperStarForget₂Comparison]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← Scheme.upperStarConstantSheafIso_comp (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f pZ]
  simp

/-- The identifications `AlgebraicGeometry.Etale.forget₂UpperStarObjIso` are compatible with
pullbacks. -/
lemma forget₂UpperStarObjIso_hom_comp {Y Z : Scheme.{u}} (pZ : Z ⟶ S) (f : Y ⟶ Z) :
    (Ψ Y).map ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f pZ).inv.app G) ≫
        (forget₂UpperStarObjIso ε (f ≫ pZ)).hom =
      inv (upperStarForget₂Comparison (ULift.{u + 1} ℤ) f _) ≫
        ((f)^*[AddCommGrpCat.{u + 1}]).map (forget₂UpperStarObjIso ε pZ).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} f pZ).inv.app F := by
  simp only [forget₂UpperStarObjIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    asIso_inv, Functor.map_comp, Category.assoc]
  have hn := (upperStarComp AddCommGrpCat.{u + 1} f pZ).inv.naturality ε.hom
  simp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc]
  congr 1
  simp only [Category.assoc]
  rw [← cancel_epi ((upperStarComp AddCommGrpCat.{u + 1} f pZ).hom.app _ ≫
    ((f)^*[AddCommGrpCat.{u + 1}]).map (upperStarForget₂Comparison (ULift.{u + 1} ℤ) pZ G) ≫
    upperStarForget₂Comparison (ULift.{u + 1} ℤ) f _)]
  simp only [Category.assoc]
  rw [
    reassoc_of% upperStarComp_hom_app_comp_upperStarForget₂Comparison, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id,
    IsIso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    IsIso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- The identifications `AlgebraicGeometry.Etale.cohomologyForget₂AddEquiv` intertwine the
restriction maps `AlgebraicGeometry.Etale.cohomologyRestrictOver` of the cohomology of sheaves of
`ULift ℤ`-modules with the pullback maps `AlgebraicGeometry.Etale.cohomologyMap` of the
cohomology of abelian sheaves. -/
lemma cohomologyForget₂AddEquiv_cohomologyRestrictOver {Y Z : Scheme.{u}} (pY : Y ⟶ S)
    (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (q : ℕ)
    (x : Ext (SemiSimplicialObject.constSheaf Z.smallEtaleTopology (ULift.{u + 1} ℤ))
      (((pZ)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)]).obj G) q) :
    cohomologyForget₂AddEquiv e ε pY q
        (cohomologyRestrictOver (ULift.{u + 1} ℤ) pY pZ f hf G q x) =
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm).inv.app F) q
        (cohomologyMap f _ q (cohomologyForget₂AddEquiv e ε pZ q x)) := by
  subst hf
  rw [cohomologyForget₂AddEquiv_apply, cohomologyForget₂AddEquiv_apply, cohomologyMap_apply,
    Sheaf.H.map_apply]
  simp only [cohomologyRestrictOver, cohomologyRestrict, AddMonoidHom.comp_apply,
    AddMonoidHom.mk'_apply, Functor.mapExtAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  done

end Transport

end AlgebraicGeometry.Etale
