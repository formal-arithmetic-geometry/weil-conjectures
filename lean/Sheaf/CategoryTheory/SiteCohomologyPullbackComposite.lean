/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Sheaf.CategoryTheory.SiteCohomologyPullbackData
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB


/-!
# Pullback on cohomology over objects of sites

Source: Stacks Project, Cohomology, Tags 01F7, 01F8 and 01FB; Sites, Tag 08J6;
Derived Categories, Tag 015B
(blueprint: lem-weil-pbc-site-cohomology-pullback-composite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory


/-- Composition followed by the unit-compatible left-adjoint isomorphism preserves
the degree-zero normalization and connecting-map identities; dimension shifting
gives the composition formula for the specified normalized family of U ⋙ W.

Source: Stacks Project, Cohomology, Tag 01F8; Sites, Tags 03CB and 03CC.
(blueprint: lem-weil-pbc-site-cohomology-pullback-composite)

Proof: In degree zero, use the three normalization equations and the
unit compatibility of e to identify evaluations on the universal generator.
In positive degree, embed the coefficient in an injective and lift each class
through the surjective boundary of its cokernel sequence. For that short exact S,
apply the boundary
compatibility of fU to S, then that of fW to f⁻¹S. Exactness of both inverse images
makes the intermediate rows short exact. The components e.inv on the three objects
form an isomorphism of short exact sequences onto (fg)⁻¹S, so naturality of the
Yoneda boundary gives the last square. For degree zero, use naturality of evaluation
on the universal generator to move the map induced by e.inv outside evaluation.
Apply normalization first for fW and then fU. The unit equation for e identifies
the resulting composite of section maps with e.hom applied after the composite
unit. Cancel e.inv with e.hom. This gives normalization for U ⋙ W.
Finally use the dimension-shifting
induction: every normalized family is determined in degree zero by its unit, and in positive degree
by the surjective boundary for an injective embedding. Thus the given fUW equals
the normalized composite family. -/
theorem siteCohomology_pullback_composite
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (J : Precoverage C) (K : Precoverage D) (L : Precoverage E)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    [L.HasIsos] [L.IsStableUnderComposition] [L.IsStableUnderBaseChange] [L.HasPullbacks]
    (U : C ⥤ D) (W : D ⥤ E)
    (hUcover : ∀ (X : C) (R : Presieve X), R ∈ J X → R.map U ∈ K (U.obj X))
    (hUpullback : ∀ (X Y Z : C) (R : Presieve X), R ∈ J X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U)
    (hWcover : ∀ (X : D) (R : Presieve X), R ∈ K X → R.map W ∈ L (W.obj X))
    (hWpullback : ∀ (X Y Z : D) (R : Presieve X), R ∈ K X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) W)
    [U.IsContinuous J.toGrothendieck K.toGrothendieck]
    [W.IsContinuous K.toGrothendieck L.toGrothendieck]
    [(U ⋙ W).IsContinuous J.toGrothendieck L.toGrothendieck]
    [PreservesFiniteLimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback U (Type u) J.toGrothendieck K.toGrothendieck)]
    [PreservesFiniteLimits (sheafPullback W (Type u) K.toGrothendieck L.toGrothendieck)]
    [PreservesFiniteColimits (sheafPullback W (Type u) K.toGrothendieck L.toGrothendieck)]
    [(sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).Additive]
    [(sheafPullback W AddCommGrpCat.{u} K.toGrothendieck L.toGrothendieck).Additive]
    [(sheafPullback (U ⋙ W) AddCommGrpCat.{u} J.toGrothendieck L.toGrothendieck).Additive]
    [HasExt.{u} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{u} (Sheaf L.toGrothendieck AddCommGrpCat.{u})] :
    ∀ (fU : ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).obj A) p (U.obj V))
      (fW : ∀ (p : ℕ) (V : D) (A : Sheaf K.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback W AddCommGrpCat.{u}
            K.toGrothendieck L.toGrothendieck).obj A) p (W.obj V))
      (fUW : ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        Sheaf.H' A p V ⟶
          Sheaf.H' ((sheafPullback (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).obj A) p ((U ⋙ W).obj V)),
      ((∀ (p : ℕ) (V : C) (A A' : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck p).map φ).app (op V) ≫
            fU p V A' =
          fU p V A ≫
            ((Sheaf.cohomologyPresheafFunctor K.toGrothendieck p).map
              ((sheafPullback U AddCommGrpCat.{u}
                J.toGrothendieck K.toGrothendieck).map φ)).app (op (U.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback U AddCommGrpCat.{u}
          J.toGrothendieck K.toGrothendieck)).ShortExact)
        (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
        (fU (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fU p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fU 0 V A).hom x)).hom.app (op (U.obj V))).hom
            (((toSheafify K.toGrothendieck
              (yoneda.obj (U.obj V) ⋙ AddCommGrpCat.free)).app (op (U.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (U.obj V)))) =
          (((sheafAdjunctionContinuous U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify J.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ((∀ (p : ℕ) (V : D) (A A' : Sheaf K.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor K.toGrothendieck p).map φ).app (op V) ≫
            fW p V A' =
          fW p V A ≫
            ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map
              ((sheafPullback W AddCommGrpCat.{u}
                K.toGrothendieck L.toGrothendieck).map φ)).app (op (W.obj V))) ∧
      (∀ (S : ShortComplex (Sheaf K.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback W AddCommGrpCat.{u}
          K.toGrothendieck L.toGrothendieck)).ShortExact)
        (p : ℕ) (V : D) (x : Sheaf.H' S.X₃ p V),
        (fW (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fW p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : D) (A : Sheaf K.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fW 0 V A).hom x)).hom.app (op (W.obj V))).hom
            (((toSheafify L.toGrothendieck
              (yoneda.obj (W.obj V) ⋙ AddCommGrpCat.free)).app (op (W.obj V))).hom
                (FreeAbelianGroup.of (𝟙 (W.obj V)))) =
          (((sheafAdjunctionContinuous W AddCommGrpCat.{u}
            K.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify K.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ((∀ (p : ℕ) (V : C) (A A' : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (φ : A ⟶ A'),
        ((Sheaf.cohomologyPresheafFunctor J.toGrothendieck p).map φ).app (op V) ≫
            fUW p V A' =
          fUW p V A ≫
            ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map
              ((sheafPullback (U ⋙ W) AddCommGrpCat.{u}
                J.toGrothendieck L.toGrothendieck).map φ)).app (op ((U ⋙ W).obj V))) ∧
      (∀ (S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u})) (hS : S.ShortExact)
        (hS' : (S.map (sheafPullback (U ⋙ W) AddCommGrpCat.{u}
          J.toGrothendieck L.toGrothendieck)).ShortExact)
        (p : ℕ) (V : C) (x : Sheaf.H' S.X₃ p V),
        (fUW (p + 1) V S.X₁).hom (Abelian.Ext.comp x hS.extClass rfl) =
          Abelian.Ext.comp ((fUW p V S.X₃).hom x) hS'.extClass rfl) ∧
      (∀ (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}) (x : Sheaf.H' A 0 V),
        ((Abelian.Ext.addEquiv₀ ((fUW 0 V A).hom x)).hom.app (op ((U ⋙ W).obj V))).hom
            (((toSheafify L.toGrothendieck
              (yoneda.obj ((U ⋙ W).obj V) ⋙ AddCommGrpCat.free)).app
                (op ((U ⋙ W).obj V))).hom
                (FreeAbelianGroup.of (𝟙 ((U ⋙ W).obj V)))) =
          (((sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
            (((Abelian.Ext.addEquiv₀ x).hom.app (op V)).hom
              (((toSheafify J.toGrothendieck
                (yoneda.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
                  (FreeAbelianGroup.of (𝟙 V)))))) →
      ∀ (e : sheafPullback (U ⋙ W) AddCommGrpCat.{u} J.toGrothendieck L.toGrothendieck ≅
          sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck ⋙
            sheafPullback W AddCommGrpCat.{u} K.toGrothendieck L.toGrothendieck),
        (∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{u},
          (sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
            J.toGrothendieck L.toGrothendieck).unit.app F ≫
            ((U ⋙ W).sheafPushforwardContinuous AddCommGrpCat.{u}
              J.toGrothendieck L.toGrothendieck).map (e.hom.app F) =
          (sheafAdjunctionContinuous U AddCommGrpCat.{u}
            J.toGrothendieck K.toGrothendieck).unit.app F ≫
            (U.sheafPushforwardContinuous AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).map
              ((sheafAdjunctionContinuous W AddCommGrpCat.{u}
                K.toGrothendieck L.toGrothendieck).unit.app
                ((sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj F))) →
        ∀ (p : ℕ) (V : C) (A : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
          fUW p V A =
            fU p V A ≫ fW p (U.obj V)
                ((sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck).obj A) ≫
              ((Sheaf.cohomologyPresheafFunctor L.toGrothendieck p).map (e.inv.app A)).app
                (op (W.obj (U.obj V))) := by
  obtain ⟨_, hUl, hUc, _⟩ := sitePullback_abelian_exact J K U hUcover hUpullback
  let := hUl
  let := hUc
  obtain ⟨_, hWl, hWc, _⟩ := sitePullback_abelian_exact K L W hWcover hWpullback
  let := hWl
  let := hWc
  intro fU fW fUW hfU hfW hfUW e he p V A
  let F := sheafPullback U AddCommGrpCat.{u} J.toGrothendieck K.toGrothendieck
  let G := sheafPullback W AddCommGrpCat.{u} K.toGrothendieck L.toGrothendieck
  let H := sheafPullback (U ⋙ W) AddCommGrpCat.{u} J.toGrothendieck L.toGrothendieck
  let : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteColimits H := preservesFiniteColimits_of_natIso e.symm
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  induction p generalizing A with
  | zero =>
    apply Sheaf.objectCohomologyEval₀_injective L.toGrothendieck (W.obj (U.obj V)) _
    change Sheaf.objectCohomologyEval₀ L.toGrothendieck _ _ ((fUW 0 V A).hom x) =
      Sheaf.objectCohomologyEval₀ L.toGrothendieck _ _
        ((((Sheaf.cohomologyPresheafFunctor L.toGrothendieck 0).map
          (e.inv.app A)).app (op (W.obj (U.obj V)))).hom
            ((fW 0 (U.obj V) (F.obj A)).hom ((fU 0 V A).hom x)))
    rw [Sheaf.objectCohomologyEval₀_naturality]
    have hU := hfU.2.2 V A x
    have hW := hfW.2.2 (U.obj V) (F.obj A) ((fU 0 V A).hom x)
    have hUW := hfUW.2.2 V A x
    change Sheaf.objectCohomologyEval₀ _ _ _ _ = _ at hU hW hUW
    have hu := congrArg (fun f ↦ (f.hom.app (op V)).hom
      (Sheaf.objectCohomologyEval₀ J.toGrothendieck V A x)) (he A)
    have hc := congrArg (fun z ↦ ((e.inv.app A).hom.app
      (op (W.obj (U.obj V)))).hom z) hu
    have hb := hW.trans (congrArg (fun z ↦
      (((sheafAdjunctionContinuous W AddCommGrpCat.{u}
        K.toGrothendieck L.toGrothendieck).unit.app (F.obj A)).hom.app (op (U.obj V))).hom z)
      hU)
    refine hUW.trans (Eq.trans ?_ (congrArg (fun z ↦
      ((e.inv.app A).hom.app (op (W.obj (U.obj V)))).hom z) hb.symm))
    change ((e.inv.app A).hom.app (op (W.obj (U.obj V)))).hom
      (((e.hom.app A).hom.app (op (W.obj (U.obj V)))).hom
        ((((sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
          J.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
            (Sheaf.objectCohomologyEval₀ J.toGrothendieck V A x))) = _ at hc
    have hcancel := congrArg (fun f ↦ (f.hom.app (op (W.obj (U.obj V)))).hom
      ((((sheafAdjunctionContinuous (U ⋙ W) AddCommGrpCat.{u}
        J.toGrothendieck L.toGrothendieck).unit.app A).hom.app (op V)).hom
          (Sheaf.objectCohomologyEval₀ J.toGrothendieck V A x))) (e.hom_inv_id_app A)
    change ((e.inv.app A).hom.app (op (W.obj (U.obj V)))).hom
      (((e.hom.app A).hom.app (op (W.obj (U.obj V)))).hom _) = _ at hcancel
    rw [hcancel] at hc
    exact hc
  | succ n ih =>
    let S : ShortComplex (Sheaf J.toGrothendieck AddCommGrpCat.{u}) :=
      ShortComplex.mk (Injective.ι A) (cokernel.π (Injective.ι A)) (cokernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    have hSU := hS.map_of_exact F
    have hSUW := hSU.map_of_exact G
    have hSH := hS.map_of_exact H
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁
      ((presheafToSheaf J.toGrothendieck AddCommGrpCat.{u}).obj
        (yoneda.obj V ⋙ AddCommGrpCat.free))
      hS x (Abelian.Ext.eq_zero_of_injective _) rfl
    change (fUW (n + 1) V A).hom x =
      (((Sheaf.cohomologyPresheafFunctor L.toGrothendieck (n + 1)).map
        (e.inv.app A)).app (op (W.obj (U.obj V)))).hom
          ((fW (n + 1) (U.obj V) (F.obj A)).hom ((fU (n + 1) V A).hom x))
    erw [← hy, hfUW.2.1 S hS hSH n V y, hfU.2.1 S hS hSU n V y,
      hfW.2.1 (S.map F) hSU hSUW n (U.obj V) ((fU n V S.X₃).hom y)]
    have hi := ih S.X₃ y
    change (fUW n V S.X₃).hom y =
      (((Sheaf.cohomologyPresheafFunctor L.toGrothendieck n).map
        (e.inv.app S.X₃)).app (op (W.obj (U.obj V)))).hom
          ((fW n (U.obj V) (F.obj S.X₃)).hom ((fU n V S.X₃).hom y)) at hi
    erw [hi]
    let z := (fW n (U.obj V) (F.obj S.X₃)).hom ((fU n V S.X₃).hom y)
    change (z.comp (Abelian.Ext.mk₀ (e.inv.app S.X₃)) (add_zero n)).comp
      hSH.extClass rfl =
        (z.comp hSUW.extClass rfl).comp (Abelian.Ext.mk₀ (e.inv.app S.X₁))
          (add_zero (n + 1))
    let φ : (S.map F).map G ⟶ S.map H :=
      { τ₁ := e.inv.app S.X₁
        τ₂ := e.inv.app S.X₂
        τ₃ := e.inv.app S.X₃
        comm₁₂ := (e.inv.naturality S.f).symm
        comm₂₃ := (e.inv.naturality S.g).symm }
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero,
      ← hSUW.extClass_naturality hSH φ,
      Abelian.Ext.comp_assoc_of_third_deg_zero]

end CategoryTheory
