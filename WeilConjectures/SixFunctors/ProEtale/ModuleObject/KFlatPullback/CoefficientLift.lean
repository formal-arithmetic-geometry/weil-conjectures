/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.CoefficientRingSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapComparison
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-!
# Lifting global sections of the coefficient ring along weakly étale maps

Let `S ≅ Spec R` with `R` w-contractible and `g : S ⟶ Y`. The global sections of the coefficient
sheaf `Λ_S` are `Λ(π₀ S)`. We show that they all come from global sections of `Λ_V` for the weakly
étale `Y`-scheme `V = Y[π₀ S] = Spec LC(π₀ S, ℤ) ×_{Spec ℤ} Y`, through which `g` factors
(`AlgebraicGeometry.ProEtale.exists_weaklyEtale_surjective_globalSectionsToUpperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

/-- Sections version of `ProEtale.unit_comp_lowerStar_map_unit_comp_upperStarComp`. -/
lemma unit_hom_app_comp_unit_hom_app_comp_upperStarComp {B X Y : Scheme.{u}} (f : X ⟶ Y)
    (kX : X ⟶ B) (kY : Y ⟶ B) (hf : f ≫ kY = kX) (F : Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
    (W : B.ProEt) :
    ((upperStarLowerStarAdjunction Ab.{u + 1} kY).unit.app F).hom.app (op W) ≫
      ((upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app ((kY)^*[Ab.{u + 1}].obj F)).hom.app
          (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ kY).obj W)) ≫
        ((upperStarComp Ab.{u + 1} f kY).inv.app F ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app F).hom.app
            (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj
              ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ kY).obj W))) =
    ((upperStarLowerStarAdjunction Ab.{u + 1} kX).unit.app F).hom.app (op W) ≫
      ((kX)^*[Ab.{u + 1}].obj F).obj.map
        ((MorphismProperty.Over.pullbackComp f kY).inv.app W ≫
          (MorphismProperty.Over.pullbackCongr hf).hom.app W).op := by
  have H := congrArg (fun φ ↦ φ.hom.app (op W))
    (unit_comp_lowerStar_map_unit_comp_upperStarComp Ab.{u + 1} f kX kY hf F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at H
  rw [eqToHom_lowerStar_app_hom_app Ab.{u + 1} hf.symm,
    coefficient_lowerStarComp_inv_app_hom_app] at H
  rw [op_comp, Functor.map_comp]
  exact H

section Lift

variable {S Y : Scheme.{u}} (g : S ⟶ Y)

/-- The profinite set `π₀ S` of connected components of `S`. -/
noncomputable abbrev componentsOf (S : Scheme.{u}) : Profinite.{u} :=
  (connectedComponentsAlong (toSpecZ S)).obj (ProEt.mk (𝟙 S))

/-- The unit `S ⟶ S[π₀ S]`. -/
noncomputable abbrev componentsUnit (S : Scheme.{u}) :
    ProEt.mk (𝟙 S) ⟶ (profiniteToProEtAlong (toSpecZ S)).obj (componentsOf S) :=
  (connectedComponentsAlongAdjunction (toSpecZ S)).unit.app (ProEt.mk (𝟙 S))

/-- The projection `S ⟶ Spec LC(π₀ S, ℤ)`. -/
noncomputable abbrev componentsProj (S : Scheme.{u}) :
    S ⟶ profiniteToScheme.obj (componentsOf S) :=
  homProfiniteToProEtAlongEquiv (toSpecZ S) _ _ (componentsUnit S)

/-- The weakly étale `Y`-scheme `Y[π₀ S]`. -/
noncomputable abbrev componentsLift (S : Scheme.{u}) (Y : Scheme.{u}) : Y.ProEt :=
  (profiniteToProEtAlong (toSpecZ Y)).obj (componentsOf S)

/-- The map `S ⟶ Y[π₀ S]` with components `S ⟶ Spec LC(π₀ S, ℤ)` and `g`. -/
noncomputable def componentsLiftHom : S ⟶ (componentsLift S Y).left :=
  pullback.lift (componentsProj S) g (specULiftZIsTerminal.hom_ext _ _)

/-- The first component of `S ⟶ Y[π₀ S]` is the projection `S ⟶ Spec LC(π₀ S, ℤ)`. -/
lemma componentsLiftHom_fst :
    componentsLiftHom g ≫ pullback.fst _ _ = componentsProj S :=
  pullback.lift_fst _ _ _

/-- The map `S ⟶ Y[π₀ S]` is a morphism over `Y`. -/
lemma componentsLiftHom_snd :
    componentsLiftHom g ≫ (componentsLift S Y).hom = g :=
  pullback.lift_snd _ _ _

/-- The section `V ⟶ V[π₀ S]` given by the projection `V ⟶ Spec LC(π₀ S, ℤ)`, for
`V = Y[π₀ S]`. -/
noncomputable def componentsSection (S Y : Scheme.{u}) :
    ProEt.mk (𝟙 (componentsLift S Y).left) ⟶
      (profiniteToProEtAlong (toSpecZ (componentsLift S Y).left)).obj (componentsOf S) :=
  (homProfiniteToProEtAlongEquiv _ _ _).symm (pullback.fst _ _)

-- the intermediate `simp` normal form is too large to state explicitly
set_option linter.flexible false in
/-- The base change of the section `V ⟶ V[π₀ S]` along `S ⟶ V` is the unit `S ⟶ S[π₀ S]`. -/
lemma componentsSection_comp :
    (overPullbackObjMkIdIso (componentsLiftHom g)).inv ≫
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (componentsLiftHom g)).map
        (componentsSection S Y) ≫
      (MorphismProperty.Over.pullbackComp (componentsLiftHom g)
        (toSpecZ (componentsLift S Y).left)).inv.app (profiniteToProEt.obj (componentsOf S)) ≫
      (MorphismProperty.Over.pullbackCongr (comp_toSpecZ (componentsLiftHom g))).hom.app
        (profiniteToProEt.obj (componentsOf S)) = componentsUnit S := by
  apply (homProfiniteToProEtAlongEquiv (toSpecZ S) _ _).injective
  simp only [homProfiniteToProEtAlongEquiv, Equiv.coe_fn_mk]
  refine (?_ : _ = componentsLiftHom g ≫ pullback.fst _ _).trans (componentsLiftHom_fst g)
  simp [MorphismProperty.Over.pullbackCongr_hom_app_left_fst, overPullbackObjMkIdIso,
    componentsSection, homProfiniteToProEtAlongEquiv]
  erw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, ← pullback.condition]
  simp
  rfl

/-- `AlgebraicGeometry.ProEtale.componentsSection_comp` after applying a presheaf. -/
lemma map_componentsSection_comp (G : S.ProEtᵒᵖ ⥤ Ab.{u + 1}) :
    G.map ((MorphismProperty.Over.pullbackComp (componentsLiftHom g)
        (toSpecZ (componentsLift S Y).left)).inv.app (profiniteToProEt.obj (componentsOf S)) ≫
      (MorphismProperty.Over.pullbackCongr (comp_toSpecZ (componentsLiftHom g))).hom.app
        (profiniteToProEt.obj (componentsOf S))).op ≫
      G.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (componentsLiftHom g)).map
        (componentsSection S Y)).op ≫
      G.map (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso (componentsLiftHom g))).op =
    G.map (componentsUnit S).op := by
  rw [← G.map_comp, ← G.map_comp, ← op_comp, ← op_comp, Category.assoc]
  exact congrArg (fun f ↦ G.map f.op) (componentsSection_comp g)

end Lift

/-- Restricting global sections along `h : S ⟶ V` and applying `α : h^* G ⟶ G'`, computed on
sections over the terminal objects `V` and `S`. -/
lemma ΓNatIsoSheafSections_inv_app_comp_globalSectionsToUpperStar_app_comp {S V : Scheme.{u}}
    (h : S ⟶ V) {G : Sheaf (ProEt.topology V) Ab.{u + 1}} {G' : Sheaf (ProEt.topology S) Ab.{u + 1}}
    (α : (h)^*[Ab.{u + 1}].obj G ⟶ G') :
    (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId V)).inv.app G ≫
        (globalSectionsToUpperStar Ab.{u + 1} h).app G ≫ (Sheaf.Γ _ Ab.{u + 1}).map α =
      ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app G).hom.app (op (ProEt.mk (𝟙 V))) ≫
        α.hom.app (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj (ProEt.mk (𝟙 V)))) ≫
        G'.obj.map (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso h)).op ≫
        (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId S)).inv.app G' := by
  have nV := (Sheaf.ΓNatIsoSheafSections _ Ab.{u + 1} (ProEt.isTerminalMkId V)).inv.naturality
    ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app G)
  have nS := (Sheaf.ΓNatIsoSheafSections _ Ab.{u + 1} (ProEt.isTerminalMkId S)).inv.naturality α
  have nc := α.hom.naturality (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso h)).op
  rw [globalSectionsToUpperStar_app, globalSectionsLowerStarIso_hom_app']
  simp only [Category.assoc, ← nS]
  rw [← reassoc_of% nV, Iso.inv_hom_id_app_assoc, ← reassoc_of% nc]
  rfl

/-- The unit of `p_V^* ⊣ p_{V*}` (along `k_V : V ⟶ Spec ℤ`), followed by the unit of
`h^* ⊣ h_*` and the comparison `h^* k_V^* ≅ k_S^*`, is the unit of `p_S^* ⊣ p_{S*}` followed by
the comparison `S ×_V V[P] ≅ S[P]`. -/
lemma unit_comp_unit_comp_upperStarComp_inv_app {S V : Scheme.{u}} (h : S ⟶ V)
    (kS : S ⟶ specZ.{u}) (kV : V ⟶ specZ.{u}) (hf : h ≫ kV = kS) (P : Profinite.{u}) :
    ((upperStarFromPointAlongAdjunction kV).unit.app Λ).hom.app (op P) ≫
      ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app
          ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))).hom.app
        (op ((profiniteToProEtAlong kV).obj P)) ≫
      ((upperStarComp Ab.{u + 1} h kV).inv.app (pointUpperStar.obj Λ) ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app (pointUpperStar.obj Λ)).hom.app
        (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).obj
          ((profiniteToProEtAlong kV).obj P))) =
    ((upperStarFromPointAlongAdjunction kS).unit.app Λ).hom.app (op P) ≫
      ((kS)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map
        ((MorphismProperty.Over.pullbackComp h kV).inv.app (profiniteToProEt.obj P) ≫
          (MorphismProperty.Over.pullbackCongr hf).hom.app (profiniteToProEt.obj P)).op := by
  have H := unit_hom_app_comp_unit_hom_app_comp_upperStarComp h kS kV hf (pointUpperStar.obj Λ)
    (profiniteToProEt.obj P)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at H
  simp only [upperStarFromPointAlongAdjunction, Adjunction.comp_unit_app,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, pointLowerStar_map_hom_app_eq,
    Category.assoc]
  exact congrArg (_ ≫ ·) H

/-- The canonical section `x_V ∈ Λ_V(V[P])` of `x ∈ Λ(P)`, restricted along a section
`σ : V ⟶ V[P]`, restricts along `h : S ⟶ V` to the canonical section `x_S`, restricted along a
section `τ : S ⟶ S[P]` compatible with `σ`. Here `Λ_V = k_V^* p^* Λ` and `Λ_S = k_S^* p^* Λ`. -/
lemma unit_comp_map_comp_globalSectionsToUpperStar_app_comp {S V : Scheme.{u}} (h : S ⟶ V)
    (kS : S ⟶ specZ.{u}) (kV : V ⟶ specZ.{u}) (hf : h ≫ kV = kS) (P : Profinite.{u})
    (σ : ProEt.mk (𝟙 V) ⟶ (profiniteToProEtAlong kV).obj P)
    (τ : ProEt.mk (𝟙 S) ⟶ (profiniteToProEtAlong kS).obj P)
    (hτ : ∀ G : S.ProEtᵒᵖ ⥤ Ab.{u + 1},
      G.map ((MorphismProperty.Over.pullbackComp h kV).inv.app (profiniteToProEt.obj P) ≫
        (MorphismProperty.Over.pullbackCongr hf).hom.app (profiniteToProEt.obj P)).op ≫
      G.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map σ).op ≫
      G.map (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso h)).op = G.map τ.op) :
    ((upperStarFromPointAlongAdjunction kV).unit.app Λ).hom.app (op P) ≫
      ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map σ.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId V)).inv.app
        ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) ≫
      (globalSectionsToUpperStar Ab.{u + 1} h).app
        ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) ≫
      (Sheaf.Γ _ Ab.{u + 1}).map ((upperStarComp Ab.{u + 1} h kV).inv.app (pointUpperStar.obj Λ) ≫
          (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app (pointUpperStar.obj Λ)) =
    ((upperStarFromPointAlongAdjunction kS).unit.app Λ).hom.app (op P) ≫
      ((kS)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map τ.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId S)).inv.app
        ((kS)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) := by
  have n1 : ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map σ.op ≫
      ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app
        ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))).hom.app _ =
      ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app
        ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))).hom.app _ ≫
      ((h)^*[Ab.{u + 1}].obj ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))).obj.map
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map σ).op :=
    ((upperStarLowerStarAdjunction Ab.{u + 1} h).unit.app
      ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))).hom.naturality σ.op
  have n2 := ((upperStarComp Ab.{u + 1} h kV).inv.app (pointUpperStar.obj Λ) ≫
    (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app (pointUpperStar.obj Λ)).hom.naturality
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map σ).op
  rw [ΓNatIsoSheafSections_inv_app_comp_globalSectionsToUpperStar_app_comp, reassoc_of% n1,
    reassoc_of% n2, reassoc_of% (unit_comp_unit_comp_upperStarComp_inv_app Λ h kS kV hf P),
    reassoc_of% (hτ _)]

/-- Let `h : S ⟶ V` be compatible with `k_S : S ⟶ Spec ℤ` and `k_V : V ⟶ Spec ℤ`. If the
sections of `Λ_S = k_S^* p^* Λ` over `S` are all canonical sections `x_S ∈ Λ_S(S[P])` restricted
along a section `τ : S ⟶ S[P]` which factors through `h` and a section `σ : V ⟶ V[P]`, then
restricting global sections of `Λ_V = k_V^* p^* Λ` along `h` is surjective. -/
lemma surjective_globalSectionsToUpperStar_app_of_surjective {S V : Scheme.{u}} (h : S ⟶ V)
    (kS : S ⟶ specZ.{u}) (kV : V ⟶ specZ.{u}) (hf : h ≫ kV = kS) (P : Profinite.{u})
    (σ : ProEt.mk (𝟙 V) ⟶ (profiniteToProEtAlong kV).obj P)
    (τ : ProEt.mk (𝟙 S) ⟶ (profiniteToProEtAlong kS).obj P)
    (hτ : ∀ G : S.ProEtᵒᵖ ⥤ Ab.{u + 1},
      G.map ((MorphismProperty.Over.pullbackComp h kV).inv.app (profiniteToProEt.obj P) ≫
        (MorphismProperty.Over.pullbackCongr hf).hom.app (profiniteToProEt.obj P)).op ≫
      G.map ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ h).map σ).op ≫
      G.map (Iso.inv (C := S.ProEt) (overPullbackObjMkIdIso h)).op = G.map τ.op)
    (hS : Function.Surjective (((upperStarFromPointAlongAdjunction kS).unit.app Λ).hom.app (op P) ≫
      ((pointUpperStar ⋙ (kS)^*[Ab.{u + 1}]).obj Λ).obj.map τ.op)) :
    Function.Surjective ((globalSectionsToUpperStar Ab.{u + 1} h).app
      ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))) := by
  intro y
  have hinj := (ConcreteCategory.bijective_of_isIso ((Sheaf.Γ _ Ab.{u + 1}).map
    ((upperStarComp Ab.{u + 1} h kV).inv.app (pointUpperStar.obj Λ) ≫
      (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app (pointUpperStar.obj Λ)))).1
  obtain ⟨x, hx⟩ := hS ((Sheaf.ΓNatIsoSheafSections (ProEt.topology S) Ab.{u + 1}
    (ProEt.isTerminalMkId S)).hom.app ((kS)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))
    ((Sheaf.Γ _ Ab.{u + 1}).map ((upperStarComp Ab.{u + 1} h kV).inv.app (pointUpperStar.obj Λ) ≫
      (eqToHom (congrArg (upperStar Ab.{u + 1}) hf)).app (pointUpperStar.obj Λ)) y))
  refine ⟨(((upperStarFromPointAlongAdjunction kV).unit.app Λ).hom.app (op P) ≫
      ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)).obj.map σ.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ (ProEt.isTerminalMkId V)).inv.app
        ((kV)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))) x, hinj ?_⟩
  have H := congrArg (fun φ ↦ φ x)
    (unit_comp_map_comp_globalSectionsToUpperStar_app_comp Λ h kS kV hf P σ τ hτ)
  simp only [ConcreteCategory.comp_apply] at H hx ⊢
  refine H.trans ((congrArg (ConcreteCategory.hom ((Sheaf.ΓNatIsoSheafSections (ProEt.topology S)
    Ab.{u + 1} (ProEt.isTerminalMkId S)).inv.app ((kS)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ))))
    hx).trans ?_)
  rw [← ConcreteCategory.comp_apply, Iso.hom_inv_id_app, ConcreteCategory.id_apply]

/-- **Global sections of the coefficient ring lift along a weakly étale map.** Let `S ≅ Spec R`
with `R` w-contractible and `g : S ⟶ Y`. Then `g` factors through the weakly étale `Y`-scheme
`V = Y[π₀ S]` via `h = (π, g) : S ⟶ V`, such that restricting global sections of `Λ_V` along `h` is
surjective: the global sections of `Λ_S` are `Λ(π₀ S)`, and these are restrictions of sections of
`Λ_V` along the section `V ⟶ V[π₀ S]`. -/
theorem exists_weaklyEtale_surjective_globalSectionsToUpperStar (S : Scheme.{u})
    (R : CommRingCat.{u}) [IsWContractibleRing R] (e : S ≅ Spec R) {Y : Scheme.{u}} (g : S ⟶ Y) :
    ∃ (V : Scheme.{u}) (v : V ⟶ Y) (_ : WeaklyEtale v) (h : S ⟶ V), h ≫ v = g ∧
      Function.Surjective
        ((globalSectionsToUpperStar Ab.{u + 1} h).app (condensedRingObj Λ V)) :=
  ⟨(componentsLift S Y).left, (componentsLift S Y).hom, (componentsLift S Y).prop,
    componentsLiftHom g, componentsLiftHom_snd g,
    surjective_globalSectionsToUpperStar_app_of_surjective Λ (componentsLiftHom g) (toSpecZ S)
      (toSpecZ (componentsLift S Y).left) (comp_toSpecZ (componentsLiftHom g)) (componentsOf S)
      (componentsSection S Y) (componentsUnit S) (map_componentsSection_comp g)
      (bijective_unit_app_comp_map_unit (toSpecZ S) Λ (ProEt.mk (𝟙 S))
        (bijective_toSheafify_connectedComponentsAlong_of_forall_exists_retraction (toSpecZ S) Λ
          (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) e)).2⟩

end AlgebraicGeometry.ProEtale
