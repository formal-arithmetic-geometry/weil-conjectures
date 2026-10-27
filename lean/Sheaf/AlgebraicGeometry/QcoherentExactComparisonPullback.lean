/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E9
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentZariskiCohomologyMap
public import Sheaf.AlgebraicGeometry.QcoherentEtaleExactComparisonData

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact comparison presentations and pullback
Source: Stacks Project, Tags 01FD, 03AX, 03FD and 03P2.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false
attribute [local irreducible] tensorPullback tensorPullbackObj
  moduleAbelianCohomologyLarge moduleAbelianHMap
  CategoryTheory.Adjunction.homEquiv
  CategoryTheory.Abelian.Ext CategoryTheory.Abelian.Ext.comp
  CategoryTheory.Abelian.Ext.mapExactFunctor CategoryTheory.Abelian.Ext.instAddCommGroup

private theorem exact_functor_square
    {A B C D : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    [EnoughInjectives A]
    (P : A ⥤ B) (E : B ⥤ D) (Z : A ⥤ C) (Q : C ⥤ D)
    [P.Additive] [E.Additive] [Z.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (τ : P ⋙ E ≅ Z ⋙ Q) {S M : A} (q : ℕ) (x : Abelian.Ext S M q) :
    (Abelian.Ext.mk₀ (τ.hom.app S)).comp
        ((x.mapExactFunctor Z).mapExactFunctor Q) (zero_add q) =
      ((x.mapExactFunctor P).mapExactFunctor E).comp
        (Abelian.Ext.mk₀ (τ.hom.app M)) (add_zero q) := by
  have h₁ := Abelian.Ext.mapExactFunctor_mapExactFunctor_of_iso
    P E (P ⋙ E) (Iso.refl _) x
  simp only [Iso.refl_inv, Iso.refl_hom, NatTrans.id_app,
    Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id] at h₁
  have h₂ := Abelian.Ext.mapExactFunctor_mapExactFunctor_of_iso Z Q (P ⋙ E) τ x
  rw [h₂, ← Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app, Abelian.Ext.mk₀_id_comp, h₁]

private theorem exact_functor_square_coefficients
    {A B C D : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [Category C] [Abelian C] [Category D] [Abelian D]
    [HasExt.{u + 1} A] [HasExt.{u + 1} B] [HasExt.{u + 1} C] [HasExt.{u + 1} D]
    [EnoughInjectives A]
    (P : A ⥤ B) (E : B ⥤ D) (Z : A ⥤ C) (Q : C ⥤ D)
    [P.Additive] [E.Additive] [Z.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (τ : P ⋙ E ≅ Z ⋙ Q)
    {S M : A} {T N : B} {S' M' : C} {T' N' : D}
    (b : T ⟶ P.obj S) (b' : T' ⟶ Q.obj S')
    (z : S' ⟶ Z.obj S) (e : T' ⟶ E.obj T)
    (d : P.obj M ⟶ N) (d' : Q.obj M' ⟶ N')
    (f : Z.obj M ⟶ M') (t : E.obj N ⟶ N')
    (hb : e ≫ E.map b ≫ τ.hom.app S = b' ≫ Q.map z)
    (hd : τ.hom.app M ≫ Q.map f ≫ d' = E.map d ≫ t)
    (q : ℕ) (x : Abelian.Ext S M q) :
    ((Abelian.Ext.mk₀ b').comp
      ((((Abelian.Ext.mk₀ z).comp (x.mapExactFunctor Z) (zero_add q)).comp
        (Abelian.Ext.mk₀ f) (add_zero q)).mapExactFunctor Q) (zero_add q)).comp
        (Abelian.Ext.mk₀ d') (add_zero q) =
    ((Abelian.Ext.mk₀ e).comp
      ((((Abelian.Ext.mk₀ b).comp (x.mapExactFunctor P) (zero_add q)).comp
        (Abelian.Ext.mk₀ d) (add_zero q)).mapExactFunctor E) (zero_add q)).comp
        (Abelian.Ext.mk₀ t) (add_zero q) := by
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  have h := congrArg
    (fun a : Abelian.Ext (E.obj (P.obj S)) (Q.obj (Z.obj M)) q ↦
      (Abelian.Ext.mk₀ (e ≫ E.map b)).comp
        (a.comp (Abelian.Ext.mk₀ (Q.map f ≫ d')) (add_zero q)) (zero_add q))
    (exact_functor_square P E Z Q τ q x)
  simpa only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀,
    Category.assoc, hb, hd] using h

/-- Compatible exact functors give the pullback square before identifying normalized families.
Source: Stacks Project, Tag 03FD; naturality of exact-functor maps on Ext.
(blueprint: lem-pbc-exact-comparison-pullback-square).

Proof: Apply exact-functor Ext naturality to the isomorphism tau. Precompose with
its integer map and postcompose with its coefficient map. The two prescribed
triangles identify these composites. Associativity of Ext composition gives the
claimed equality, after evaluating the definitions of the three cohomology maps. -/
theorem exactComparison_hmap_square
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ (pushforward g).obj G)
    (θ : liftedCoherentEtaleSheaf F ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj (liftedCoherentEtaleSheaf G))
    (D₁ : CoherentEtale.ExactComparison X) (D₂ : CoherentEtale.ExactComparison Y) :
    let J := Opens.grothendieckTopology X
    let K := Opens.grothendieckTopology Y
    let Z := (Opens.map g.base).sheafPullback AddCommGrpCat.{u} J K
    let z := ((Opens.map g.base).constantSheafsheafPullbackIso AddCommGrpCat.{u} J K
      isTerminalTop isTerminalTop).symm.app (AddCommGrpCat.of (ULift ℤ))
    let f := (((Opens.map g.base).sheafAdjunctionContinuous AddCommGrpCat.{u} J K).homEquiv
      _ _).symm (moduleAbelianHMap g φ)
    let E := Etale.upperStar AddCommGrpCat.{u + 1} g
    let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
      (AddCommGrpCat.of (ULift ℤ))
    let t := ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
      (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G)).symm θ
    ∀ (τ : D₁.P ⋙ E ≅ Z ⋙ D₂.P),
      e.hom ≫ E.map D₁.integer ≫ τ.hom.app (CoherentEtale.zariskiInteger X) =
        D₂.integer ≫ D₂.P.map z.hom →
      τ.hom.app ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ≫
          D₂.P.map f ≫ D₂.coefficient G = E.map (D₁.coefficient F) ≫ t →
      ∀ (q : ℕ) (x : CoherentEtale.Source X F q),
        D₂.map G q (zariskiModuleHMap g φ q x) =
          Sheaf.H.map t q
            (Etale.cohomologyMap g (liftedCoherentEtaleSheaf F) q (D₁.map F q x)) := by
  classical
  dsimp only
  intro τ hb hd q x
  let J := Opens.grothendieckTopology X
  let K := Opens.grothendieckTopology Y
  let : HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u}) := HasExt.standard _
  let : HasExt.{u + 1} (Sheaf K AddCommGrpCat.{u}) := HasExt.standard _
  let Z := (Opens.map g.base).sheafPullback AddCommGrpCat.{u} J K
  let z := ((Opens.map g.base).constantSheafsheafPullbackIso
    AddCommGrpCat.{u} J K isTerminalTop isTerminalTop).symm.app
      (AddCommGrpCat.of (ULift ℤ))
  let f := ((Opens.map g.base).sheafAdjunctionContinuous
    AddCommGrpCat.{u} J K).homEquiv _ _ |>.symm (moduleAbelianHMap g φ)
  let E := Etale.upperStar AddCommGrpCat.{u + 1} g
  let e := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app
    (AddCommGrpCat.of (ULift ℤ))
  let t := (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).homEquiv
    (liftedCoherentEtaleSheaf F) (liftedCoherentEtaleSheaf G) |>.symm θ
  have := lan_preservesFiniteLimits_of_flat (E := AddCommGrpCat.{u})
    (Opens.map g.base)
  have : PreservesFiniteLimits Z :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  have := ((Opens.map g.base).sheafAdjunctionContinuous
    AddCommGrpCat.{u} J K).leftAdjoint_preservesColimits
  have : Z.Additive := Functor.additive_of_preserves_binary_products Z
  have h := exact_functor_square_coefficients D₁.P E Z D₂.P τ
    D₁.integer D₂.integer z.hom e.hom (D₁.coefficient F) (D₂.coefficient G)
    f t hb hd q x
  exact h

end
end AlgebraicGeometry.Scheme.Modules
