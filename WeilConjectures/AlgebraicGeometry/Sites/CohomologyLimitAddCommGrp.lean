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
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Continuity of étale cohomology of abelian sheaves

Let `(Xᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over a scheme `S`, with
affine transition maps and limit `X`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Xᵢ, F|_{Xᵢ})` along the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap` ([Stacks, Tag 09YQ], blueprint
`lemma-weil-pbc-etale-cohomology-continuity`).

For sheaves of `Λ`-modules this is proved in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyLimit` in terms of the restriction maps
`AlgebraicGeometry.Etale.cohomologyRestrictOver`. Here the case of sheaves of
`ULift ℤ`-modules is transported to abelian sheaves: taking underlying abelian sheaves is an
equivalence which commutes with pullbacks and preserves injectives, so it identifies the cohomology
groups (`AlgebraicGeometry.Etale.cohomologyForget₂AddEquiv`) compatibly with the
restriction maps (`AlgebraicGeometry.Etale.cohomologyForget₂AddEquiv_cohomologyRestrictOver`).

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_isColimit_of_isLimit`: continuity of the étale
  cohomology of abelian sheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

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
  have key : (x.mapExactFunctor (Ψ Z)).mapExactFunctor ((f)^*[AddCommGrpCat.{u + 1}]) =
      (Ext.mk₀ (upperStarForget₂Comparison (ULift.{u + 1} ℤ) f _)).comp
        (((x.mapExactFunctor ((f)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)])).mapExactFunctor
          (Ψ Y)).comp
          (Ext.mk₀ (inv (upperStarForget₂Comparison (ULift.{u + 1} ℤ) f _))) (add_zero q))
        (zero_add q) := by
    rw [Ext.mapExactFunctor_mapExactFunctor, Ext.mapExactFunctor_mapExactFunctor,
      Ext.mapExactFunctor_eq_of_iso
        (asIso (upperStarForget₂ (ULift.{u + 1} ℤ) f).natTrans).symm]
    simp [upperStarForget₂_natTrans_app]
  have hres : cohomologyRestrictOver (ULift.{u + 1} ℤ) (f ≫ pZ) pZ f rfl G q x =
      (Ext.mk₀ ((constantSheafCompUpperStarIso (ULift.{u + 1} ℤ) f).inv.app _)).comp
        ((x.mapExactFunctor ((f)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)])).comp
          (Ext.mk₀ ((upperStarComp (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f pZ _ rfl).inv.app G))
          (add_zero q)) (zero_add q) := by
    rw [← Ext.comp_assoc_of_third_deg_zero]
    rfl
  rw [hres, cohomologyForget₂AddEquiv_apply, cohomologyForget₂AddEquiv_apply, cohomologyMap_apply,
    Sheaf.H.map_apply]
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, key,
    Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Ext.mk₀_comp_mk₀]
  rw [constantSheafForget₂Iso_hom_comp, forget₂UpperStarObjIso_hom_comp, Category.assoc]
  rfl

end Transport

section Continuity

set_option hygiene false in
/-- The functor taking the underlying abelian sheaf of an étale sheaf of `ULift ℤ`-modules. -/
local notation "Ψ" X:max => sheafCompose (Scheme.smallEtaleTopology X)
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})

/-- Blueprint `lemma-weil-pbc-etale-cohomology-continuity`: Etale cohomology continuity, in the
form of an elementwise colimit statement for the pullback maps.

Let `(Dᵢ)` be a cofiltered system of quasi-compact quasi-separated schemes over `S` with affine
transition maps, with limit `X = c.pt`, and let `F` be an abelian étale sheaf on `S`. Then
`Hᵠ(X, F|_X) = colimᵢ Hᵠ(Dᵢ, F|_{Dᵢ})` along the pullback maps
`AlgebraicGeometry.Etale.cohomologyMap`: every class on `X` comes from some `Dᵢ` (up to the
canonical identification `F|_X ≅ (F|_{Dᵢ})|_X` of `AlgebraicGeometry.Etale.upperStarComp`), and a
class on `Dᵢ` which vanishes on `X` already vanishes on some `Dⱼ`, `j ⟶ i`.

The proof transports the case of sheaves of `ULift ℤ`-modules
(`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_of_isLimit`,
`AlgebraicGeometry.Etale.exists_cohomologyRestrictOver_eq_zero_of_isLimit`) along the equivalence
between sheaves of `ULift ℤ`-modules and abelian sheaves. -/
@[stacks 09YQ]
theorem cohomologyMap_isColimit_of_isLimit {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Over S) [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left] [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c)) (q : ℕ) :
    (∀ x : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} c.pt.hom).obj F) q,
      ∃ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
        Etale.cohomologyMap (c.π.app i).left _ q y =
          Sheaf.H.map ((Etale.upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
            c.pt.hom (Over.w (c.π.app i)).symm).hom.app F) q x) ∧
    ∀ (i : I) (y : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (D.obj i).hom).obj F) q),
      Etale.cohomologyMap (c.π.app i).left _ q y = 0 →
        ∃ (j : I) (g : j ⟶ i), Etale.cohomologyMap (D.map g).left _ q y = 0 := by
  let E := (Ψ S).asEquivalence
  let G := E.inverse.obj F
  let ε : (Ψ S).obj G ≅ F := E.counitIso.app F
  let e : (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ)) ≅
      (Ψ S).obj (SemiSimplicialObject.constSheaf S.smallEtaleTopology (ULift.{u + 1} ℤ)) :=
    ((constantCommuteCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      AddCommGrpCat.{u + 1})).app (ModuleCat.of _ (ULift.{u + 1} ℤ))).symm
  have hmap {Y Z : Scheme.{u}} (pY : Y ⟶ S) (pZ : Z ⟶ S) (f : Y ⟶ Z) (hf : f ≫ pZ = pY) (x) :
      cohomologyMap f _ q (cohomologyForget₂AddEquiv e ε pZ q x) =
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} f pZ pY hf.symm).hom.app F) q
          (cohomologyForget₂AddEquiv e ε pY q
            (cohomologyRestrictOver (ULift.{u + 1} ℤ) pY pZ f hf G q x)) := by
    rw [cohomologyForget₂AddEquiv_cohomologyRestrictOver, ← Sheaf.H.map_comp_apply,
      Iso.inv_hom_id_app, Sheaf.H.map_id_apply]
  refine ⟨fun x ↦ ?_, fun i y hy ↦ ?_⟩
  · obtain ⟨i, y, hy⟩ := exists_cohomologyRestrictOver_eq_of_isLimit (ULift.{u + 1} ℤ) D c hc G q
      ((cohomologyForget₂AddEquiv e ε c.pt.hom q).symm x)
    refine ⟨i, cohomologyForget₂AddEquiv e ε (D.obj i).hom q y, ?_⟩
    erw [hmap c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _), hy, AddEquiv.apply_symm_apply]
    rfl
  · obtain ⟨y, rfl⟩ := (cohomologyForget₂AddEquiv e ε (D.obj i).hom q).surjective y
    erw [hmap c.pt.hom (D.obj i).hom (c.π.app i).left (Over.w _)] at hy
    have hy' : cohomologyRestrictOver (ULift.{u + 1} ℤ) c.pt.hom (D.obj i).hom (c.π.app i).left
        (Over.w _) G q y = 0 := by
      have := congrArg (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (c.π.app i).left
        (D.obj i).hom c.pt.hom (Over.w (c.π.app i)).symm).inv.app F) q) hy
      erw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id_app, Sheaf.H.map_id_apply, map_zero,
        AddEquiv.map_eq_zero_iff] at this
      exact this
    obtain ⟨j, g, hg⟩ :=
      exists_cohomologyRestrictOver_eq_zero_of_isLimit (ULift.{u + 1} ℤ) D c hc G q i y hy'
    exact ⟨j, g, by
      rw [hmap (D.obj j).hom (D.obj i).hom (D.map g).left (Over.w _), hg, map_zero, map_zero]⟩

end Continuity

end AlgebraicGeometry.Etale
