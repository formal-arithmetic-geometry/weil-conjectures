/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Pullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The pullback map on the cohomology of an abelian sheaf, and its composition law

For a morphism of schemes `f : Z ⟶ X` and an abelian sheaf `𝒢` on `X`, this file constructs the
pullback map

`H^n(X, 𝒢) ⟶ H^n(Z, f^{-1} 𝒢)`

on sheaf cohomology and proves that it is compatible with the composition of morphisms of
schemes. This is the abelian-sheaf shadow of
`AlgebraicGeometry.Scheme.Modules.H.pullbackAddHom`, from which the latter is obtained by
composing with the comparison map
`AlgebraicGeometry.Scheme.Modules.pullbackAbComparison`.

Because the pullback of abelian sheaves is only defined as *a* left adjoint of the pushforward,
the pullback along a composite `a ≫ b` is not the composite of the pullbacks, but only
canonically isomorphic to it; the isomorphism is
`AlgebraicGeometry.Scheme.Hom.pullbackAbComp`, and the composition law is stated modulo it.

## Main definitions and results

* `AlgebraicGeometry.Scheme.Hom.pullbackAbComp` — the canonical isomorphism
  `(a ≫ b)^{-1} ≅ b^{-1} ⋙ a^{-1}` of pullback functors on abelian sheaves.
* `AlgebraicGeometry.Scheme.Hom.whiskerLeft_pullbackAbComp_hom_comp` — the
  identification `f^{-1} ℤ_X ≅ ℤ_Z` of the pullback of a constant sheaf is compatible with
  `pullbackAbComp`.
* `AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom` — the pullback map on the cohomology of an
  abelian sheaf.
* `AlgebraicGeometry.Scheme.Hom.H.pullbackAddHom_comp` — **the composition law**: pulling back
  along `b` and then along `a` is pulling back along `a ≫ b`, modulo `pullbackAbComp`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Abelian

namespace AlgebraicGeometry

namespace Scheme

variable (W : Scheme.{u})

/-- The constant sheaf functor of abelian groups on a scheme. -/
noncomputable abbrev constantSheafAb :
    AddCommGrpCat.{u} ⥤ Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u} :=
  constantSheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}

/-- The global sections of an abelian sheaf on a scheme. -/
noncomputable abbrev sectionsAb :
    Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  (sheafSections (Opens.grothendieckTopology W) AddCommGrpCat.{u}).obj (op ⊤)

/-- The constant sheaf functor is left adjoint to the global sections functor. -/
noncomputable abbrev constantSheafAbAdjunction : constantSheafAb W ⊣ sectionsAb W :=
  constantSheafAdj _ _ isTerminalTop

namespace Hom

variable {X Y Z : Scheme.{u}}

/-- The composition of `Scheme.constantSheafAbAdjunction` with the adjunction between the
pullback and the pushforward of abelian sheaves: this exhibits `ℤ_X ↦ f^{-1} ℤ_X` as a left
adjoint of the global sections on `Z`, and is the adjunction from which
`AlgebraicGeometry.Scheme.Hom.pullbackAbConstantSheafIso` is obtained. -/
noncomputable abbrev constantSheafPullbackAbAdjunction (f : Z ⟶ X) :
    constantSheafAb X ⋙ f.pullbackAb ⊣ sectionsAb Z :=
  ((constantSheafAbAdjunction X).comp f.pullbackPushforwardAbAdjunction).ofNatIsoRight
    ((Opens.map f.base).sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z) (op ⊤))

/-- The identification of the pullback of the constant sheaf functor with the constant sheaf
functor, of which `AlgebraicGeometry.Scheme.Hom.pullbackAbConstantSheafIso` is the value at an
abelian group. -/
noncomputable abbrev constantSheafPullbackAbIso (f : Z ⟶ X) :
    constantSheafAb X ⋙ f.pullbackAb ≅ constantSheafAb Z :=
  (Opens.map f.base).constantSheafsheafPullbackIso AddCommGrpCat.{u}
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Z) isTerminalTop isTerminalTop

/-- **The pullback of abelian sheaves along a composite**: the canonical isomorphism
`(a ≫ b)^{-1} ≅ b^{-1} ⋙ a^{-1}`, obtained from the uniqueness of left adjoints, the
pushforward along a composite being the composite of the pushforwards. -/
noncomputable def pullbackAbComp (a : Z ⟶ X) (b : X ⟶ Y) :
    (a ≫ b).pullbackAb ≅ b.pullbackAb ⋙ a.pullbackAb :=
  Adjunction.leftAdjointUniq (a ≫ b).pullbackPushforwardAbAdjunction
    (b.pullbackPushforwardAbAdjunction.comp a.pullbackPushforwardAbAdjunction)

lemma unit_pullbackAbComp_hom_app (a : Z ⟶ X) (b : X ⟶ Y)
    (𝒢 : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) :
    (a ≫ b).pullbackPushforwardAbAdjunction.unit.app 𝒢 ≫
        (a ≫ b).pushforwardAb.map ((pullbackAbComp a b).hom.app 𝒢) =
      b.pullbackPushforwardAbAdjunction.unit.app 𝒢 ≫
        b.pushforwardAb.map
          (a.pullbackPushforwardAbAdjunction.unit.app (b.pullbackAb.obj 𝒢)) :=
  NatTrans.congr_app
    ((a ≫ b).pullbackPushforwardAbAdjunction.unit_leftAdjointUniq_hom
      (b.pullbackPushforwardAbAdjunction.comp a.pullbackPushforwardAbAdjunction)) 𝒢

lemma unit_pullbackAbConstantSheafIso_hom (f : Z ⟶ X) (A : AddCommGrpCat.{u}) :
    (constantSheafAbAdjunction X).unit.app A ≫ (sectionsAb X).map
        (f.pullbackPushforwardAbAdjunction.unit.app ((constantSheafAb X).obj A)) ≫
      (sectionsAb Z).map ((constantSheafPullbackAbIso f).hom.app A) =
      (constantSheafAbAdjunction Z).unit.app A := by
  have h := NatTrans.congr_app
    ((constantSheafPullbackAbAdjunction f).unit_leftAdjointUniq_hom
      (constantSheafAbAdjunction Z)) A
  simp only [NatTrans.comp_app] at h
  exact h

/-- **The identification of the pullback of the constant sheaf is compatible with composition**:
`ℤ_Z ≅ (a ≫ b)^{-1} ℤ_Y` is `ℤ_Z ≅ a^{-1} ℤ_X ≅ a^{-1} b^{-1} ℤ_Y ≅ (a ≫ b)^{-1} ℤ_Y`. -/
lemma whiskerLeft_pullbackAbComp_hom_comp (a : Z ⟶ X) (b : X ⟶ Y) :
    Functor.whiskerLeft (constantSheafAb Y) (pullbackAbComp a b).hom ≫
      Functor.whiskerRight (constantSheafPullbackAbIso b).hom a.pullbackAb ≫
        (constantSheafPullbackAbIso a).hom = (constantSheafPullbackAbIso (a ≫ b)).hom := by
  refine Adjunction.eq_leftAdjointUniq_hom (constantSheafPullbackAbAdjunction (a ≫ b))
    (constantSheafAbAdjunction Z) _ fun A ↦ ?_
  have hu : (constantSheafPullbackAbAdjunction (a ≫ b)).unit.app A =
      (constantSheafAbAdjunction Y).unit.app A ≫ (sectionsAb Y).map
        ((a ≫ b).pullbackPushforwardAbAdjunction.unit.app ((constantSheafAb Y).obj A)) := by
    simp only [constantSheafPullbackAbAdjunction, Adjunction.ofNatIsoRight_unit,
      NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
      Functor.sheafPushforwardContinuousCompSheafSectionsObjIso, NatIso.ofComponents_hom_app,
      Iso.refl_hom]
    rfl
  have hg : (sectionsAb Y).map ((a ≫ b).pullbackPushforwardAbAdjunction.unit.app
        ((constantSheafAb Y).obj A)) ≫
      (sectionsAb Z).map ((pullbackAbComp a b).hom.app ((constantSheafAb Y).obj A)) =
      (sectionsAb Y).map (b.pullbackPushforwardAbAdjunction.unit.app
          ((constantSheafAb Y).obj A)) ≫
        (sectionsAb X).map (a.pullbackPushforwardAbAdjunction.unit.app
          (b.pullbackAb.obj ((constantSheafAb Y).obj A))) := by
    have h1 := congrArg (fun ψ ↦ (sectionsAb Y).map ψ)
      (unit_pullbackAbComp_hom_app a b ((constantSheafAb Y).obj A))
    simp only [Functor.map_comp] at h1
    exact h1
  have hnat : (sectionsAb X).map (a.pullbackPushforwardAbAdjunction.unit.app
        (b.pullbackAb.obj ((constantSheafAb Y).obj A))) ≫
      (sectionsAb Z).map (a.pullbackAb.map ((constantSheafPullbackAbIso b).hom.app A)) =
      (sectionsAb X).map ((constantSheafPullbackAbIso b).hom.app A) ≫
        (sectionsAb X).map (a.pullbackPushforwardAbAdjunction.unit.app
          ((constantSheafAb X).obj A)) := by
    have h2 := a.pullbackPushforwardAbAdjunction.unit.naturality
      ((constantSheafPullbackAbIso b).hom.app A)
    have h3 := congrArg (fun ψ ↦ (sectionsAb X).map ψ) h2.symm
    simp only [Functor.map_comp, Functor.comp_map, Functor.id_map] at h3
    exact h3
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  rw [hu, Category.assoc, reassoc_of% hg, reassoc_of% hnat,
    ← unit_pullbackAbConstantSheafIso_hom a A, ← unit_pullbackAbConstantSheafIso_hom b A]
  simp

/-- The inverse form of `pullbackAbComp_hom_app_pullbackAbConstantSheafIso`. -/
lemma pullbackAbConstantSheafIso_inv_comp (a : Z ⟶ X) (b : X ⟶ Y) (A : AddCommGrpCat.{u}) :
    ((a ≫ b).pullbackAbConstantSheafIso A).inv =
      (a.pullbackAbConstantSheafIso A).inv ≫
        a.pullbackAb.map (b.pullbackAbConstantSheafIso A).inv ≫
          (pullbackAbComp a b).inv.app ((constantSheafAb Y).obj A) := by
  have h : (pullbackAbComp a b).hom.app ((constantSheafAb Y).obj A) ≫
        a.pullbackAb.map (b.pullbackAbConstantSheafIso A).hom ≫
          (a.pullbackAbConstantSheafIso A).hom =
      ((a ≫ b).pullbackAbConstantSheafIso A).hom := by
    have h0 := NatTrans.congr_app (whiskerLeft_pullbackAbComp_hom_comp a b) A
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h0
    exact h0
  refine (cancel_epi ((a ≫ b).pullbackAbConstantSheafIso A).hom).1 ?_
  rw [Iso.hom_inv_id, ← h]
  simp

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace H

/-- **The pullback map on the cohomology of an abelian sheaf** along a morphism of schemes
`f : Z ⟶ X`: apply the exact functor `f^{-1}` to a class in `Ext^n(ℤ_X, 𝒢)` and precompose with
the identification `ℤ_Z ≅ f^{-1} ℤ_X`. -/
noncomputable def pullbackAddHom (f : Z ⟶ X)
    (𝒢 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    𝒢.H n →+ (f.pullbackAb.obj 𝒢).H n where
  toFun e := (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
    (e.mapExactFunctor f.pullbackAb) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp [Ext.comp_add]

@[simp]
lemma pullbackAddHom_apply (f : Z ⟶ X)
    (𝒢 : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) (e : 𝒢.H n) :
    pullbackAddHom f 𝒢 n e = (Ext.mk₀ (f.pullbackAbConstantSheafIso _).inv).comp
      (e.mapExactFunctor f.pullbackAb) (zero_add n) :=
  rfl

/-- The pullback map on cohomology is natural in the abelian sheaf. -/
lemma pullbackAddHom_comp_mk₀ (f : Z ⟶ X)
    {𝒢 𝒢' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : 𝒢 ⟶ 𝒢') (n : ℕ)
    (e : 𝒢.H n) :
    pullbackAddHom f 𝒢' n (e.comp (Ext.mk₀ φ) (add_zero n)) =
      (pullbackAddHom f 𝒢 n e).comp (Ext.mk₀ (f.pullbackAb.map φ)) (add_zero n) := by
  rw [pullbackAddHom_apply, pullbackAddHom_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by lia)]

/-- **The composition law for the pullback map on cohomology**: pulling back along `b` and then
along `a` is pulling back along `a ≫ b`, followed by the identification
`AlgebraicGeometry.Scheme.Hom.pullbackAbComp` of `(a ≫ b)^{-1} 𝒢` with `a^{-1} b^{-1} 𝒢`. -/
lemma pullbackAddHom_comp (a : Z ⟶ X) (b : X ⟶ Y)
    (𝒢 : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) (e : 𝒢.H n) :
    pullbackAddHom a (b.pullbackAb.obj 𝒢) n (pullbackAddHom b 𝒢 n e) =
      (pullbackAddHom (a ≫ b) 𝒢 n e).comp
        (Ext.mk₀ ((pullbackAbComp a b).hom.app 𝒢)) (add_zero n) := by
  rw [pullbackAddHom_apply, pullbackAddHom_apply, pullbackAddHom_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.mapExactFunctor_comp_functor,
    Ext.mapExactFunctor_natIso (pullbackAbComp a b) e,
    pullbackAbConstantSheafIso_inv_comp a b]
  simp only [Ext.comp_assoc_of_third_deg_zero]
  rw [← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀]
  simp only [Ext.comp_assoc_of_second_deg_zero]

end H

end Hom

end Scheme

end AlgebraicGeometry
