/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
public import Sheaf.Paper.RingedTopoiDerivedPullback
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-!
# Shift compatibility of a derived adjunction

Source: Stacks Project, sites-cohomology.tex Tags 07A6 and 0B56, and derived.tex
Tag 0A8D (blueprint: lem-weil-pbc-derived-adjunction-shift).
-/

@[expose] public section

set_option autoImplicit false

universe uC vC uD vD r wA wB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem rightKan_postadjoint_ext
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (F : A ⥤ C) (LF : B ⥤ C) (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] (T : D ⥤ C) (S : C ⥤ D) (a : T ⊣ S)
    (H : B ⥤ D) (γ₁ γ₂ : H ⟶ LF ⋙ S)
    (h : ∀ X, γ₁.app (Q.obj X) ≫ S.map (α.app X) =
      γ₂.app (Q.obj X) ≫ S.map (α.app X)) : γ₁ = γ₂ := by
  apply ((a.whiskerRight B).homEquiv H LF).symm.injective
  apply LF.hom_ext_of_isRightKanExtension α
  simp only [Adjunction.homEquiv_counit]
  ext X
  have hx := congrArg ((a.homEquiv (H.obj (Q.obj X)) (F.obj X)).symm) (h X)
  simpa [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    ← a.counit.naturality, Adjunction.whiskerRight_counit_app_app] using hx

private theorem rightKan_postadjoint_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (F : A ⥤ C) [F.CommShift ℤ]
    (LF : B ⥤ C) [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (T : D ⥤ C) (S : C ⥤ D) [S.CommShift ℤ] (a : T ⊣ S)
    (H : B ⥤ D) [H.CommShift ℤ] (τ : H ⟶ LF ⋙ S)
    [NatTrans.CommShift (Functor.whiskerLeft Q τ ≫
      (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S) ℤ] :
    NatTrans.CommShift τ ℤ := by
  let δ := (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S
  have : NatTrans.CommShift δ ℤ := by dsimp [δ]; infer_instance
  have hτ : NatTrans.CommShift (Functor.whiskerLeft Q τ ≫ δ) ℤ := by assumption
  constructor
  intro n
  apply rightKan_postadjoint_ext Q F LF α
    ((shiftEquiv D n).symm.functor ⋙ T) (S ⋙ shiftFunctor D n)
    ((shiftEquiv D n).symm.toAdjunction.comp a)
  intro X
  have hdapp (Y : A) : δ.app Y = S.map (α.app Y) := by
    simp [δ]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, ← hdapp X]
  apply (cancel_epi (H.map ((Q.commShiftIso n).hom.app X))).mp
  have hd := NatTrans.shift_app_comm δ n X
  have ht := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ ≫ δ) n X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
    Category.assoc] at ht
  rw [← hd] at ht
  have hn := τ.naturality ((Q.commShiftIso n).hom.app X)
  dsimp at hn
  have hn' := congrArg (fun f ↦ f ≫ ((LF ⋙ S).commShiftIso n).hom.app (Q.obj X) ≫
    (shiftFunctor D n).map (δ.app X)) hn
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc, Functor.comp_map] at ht
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hn' ⊢
  exact ht.trans hn'.symm

private theorem normalized_unit_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (QA : A ⥤ C) (QB : B ⥤ D) [QA.CommShift ℤ] [QB.CommShift ℤ]
    (F : A ⥤ B) (G : B ⥤ A) [F.CommShift ℤ] [G.CommShift ℤ]
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    (ah : F ⊣ G) [NatTrans.CommShift ah.unit ℤ] (adj : L ⊣ R)
    (α : QA ⋙ L ⟶ F ⋙ QB) (β : G ⋙ QA ⟶ QB ⋙ R)
    [L.IsRightKanExtension α] [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ]
    (hnorm : ∀ M, adj.unit.app (QA.obj M) ≫ R.map (α.app M) =
      QA.map (ah.unit.app M) ≫ β.app (F.obj M)) :
    NatTrans.CommShift adj.unit ℤ := by
  let δ := Functor.whiskerLeft QA adj.unit ≫
    (Functor.associator QA L R).inv ≫ Functor.whiskerRight α R
  have heq : δ =
      (Functor.rightUnitor QA).hom ≫ (Functor.leftUnitor QA).inv ≫
      Functor.whiskerRight ah.unit QA ≫ (Functor.associator F G QA).hom ≫
      Functor.whiskerLeft F β ≫ (Functor.associator F QB R).inv := by
    ext M
    simpa [δ] using hnorm M
  have hδ : NatTrans.CommShift δ ℤ := by
    rw [heq]
    infer_instance
  exact rightKan_postadjoint_commShift QA _ L α L R adj (𝟭 _) adj.unit

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived ringed-topos adjunction is compatible with its resolution shifts.
Source: Stacks Project, Tags 07A6, 0FND, 0DVC and 0A8D
(blueprint: lem-weil-pbc-derived-adjunction-shift).

The module pullback is fixed on objects and maps by the tensor/change-of-rings formula.
Its right adjoint `G` represents the module direct image. The comparison transformations
`α` and `β` specify the universal derived functors. Their `NatTrans.CommShift` instances
express the resolution normalization of the displayed, already fixed shift structures.
The equation `normalization` is the normalized derived Hom bijection, so the derived
adjunction is the one induced by the original module adjunction.

Proof:
1. The termwise module adjunction induces the homotopy adjunction
   (`lem-weil-pbc-termwise-adjunction-homotopy`). Additivity makes its Hom bijection
   commute with every integer shift, including the differential sign.
2. K-flat complexes with flat terms remain so after shifting: on tensor summand (i,j),
   the comparison multiplies by (-1)^(n*i). K-injectives remain K-injective by
   `lem-weil-pbc-kinjective-shift`. Shifted quasi-isomorphisms remain quasi-isomorphisms.
3. The shift comparisons are characterized by commutation with α and β. On K-flat
   sources and K-injective targets these transformations are invertible, by
   `lem-weil-pbc-ringed-topoi-derived-pullback` and `def-sfb-right-derived-functor`.
4. The normalized pre-derived Hom bijection
   (`lem-pc-pre-derived-adjoint-functors-general`, `lem-pc-derived-adjoint-functors`)
   sends α followed by Q(t) to Q(T(t)) followed by β; this is `normalization`.
5. Apply this formula to shifted representatives and use Step 1 and the two comparison
   normalizations. The Hom bijection intertwines the fixed shifts.
6. Every source has a K-flat resolution (`lem-pc-kflat-resolution`) and every target
   a K-injective resolution (`prop-pur-kinjective-resolutions-exist`). Naturality and
   cancellation of the resolution isomorphisms extend Step 5 to all objects.
7. Specialize the Hom identity to the identity of L(A). This gives the unit equation.
8. Apply `lem-weil-pbc-adjunction-shift-compatibility-unique` to obtain the counit
   equation and uniqueness of each right comparison from the unit equation. This is
   uniqueness among all natural shift isomorphisms, without a coherence assumption.
-/
theorem derivedAdjunctionShiftCompatible
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{r} C] [EssentiallySmall.{r} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {RY : Sheaf JC CommRingCat.{r}} {RX RI : Sheaf JD CommRingCat.{r}}
    (uInv : Sheaf JC (Type r) ⥤ Sheaf JD (Type r))
    (uPush : Sheaf JD (Type r) ⥤ Sheaf JC (Type r))
    (toposAdj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : SheafOfModules.AlgebraicInverseImage uInv RY RI) (c : RI ⟶ RX)
    (F : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY) ⥤
      SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX))
    (hobj : ∀ M : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY),
      F.obj M = SheafOfModules.changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)} (f : M ⟶ N),
      F.map f = eqToHom (hobj M) ≫
        SheafOfModules.changeOfRingsHom c (I.modules.obj M) (I.modules.map f) ≫
          eqToHom (hobj N).symm)
    (G : SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX) ⥤
      SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY))
    [F.Additive] [G.Additive] (adj₀ : F ⊣ G)
    [HasDerivedCategory.{wA} (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY))]
    [HasDerivedCategory.{wB} (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX))]
    (L : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) ⥤
      DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)))
    (R : DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) ⥤
      DerivedCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)))
    (α : DerivedCategory.Qh ⋙ L ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ R)
    (hL : L.IsLeftDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) (ComplexShape.up ℤ)))
    (hR : R.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) (ComplexShape.up ℤ)))
    (adj : L ⊣ R)
    (normalization : ∀
      (M : HomotopyCategory (SheafOfModules.{r}
      ((sheafCompose JC (forget₂ CommRingCat.{r} RingCat.{r})).obj RY)) (ComplexShape.up ℤ))
      (K : HomotopyCategory (SheafOfModules.{r}
      ((sheafCompose JD (forget₂ CommRingCat.{r} RingCat.{r})).obj RX)) (ComplexShape.up ℤ))
      (f : (F.mapHomotopyCategory (ComplexShape.up ℤ)).obj M ⟶ K),
      adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
        (α.app M ≫ DerivedCategory.Qh.map f) =
      DerivedCategory.Qh.map ((adj₀.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv M K f)
        ≫ β.app K)
    [L.CommShift ℤ] [R.CommShift ℤ]
    [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ] :
    (∀ n : ℤ, Adjunction.CommShift.CompatibilityUnit adj
      (L.commShiftIso n) (R.commShiftIso n)) ∧
    (∀ n : ℤ, Adjunction.CommShift.CompatibilityCounit adj
      (L.commShiftIso n) (R.commShiftIso n)) ∧
    (∀ (n : ℤ) (e : shiftFunctor _ n ⋙ R ≅ R ⋙ shiftFunctor _ n),
      Adjunction.CommShift.CompatibilityUnit adj (L.commShiftIso n) e →
        e = R.commShiftIso n) := by
  have _ := toposAdj
  have _ := @hmap
  have _ := hR
  have := hL.isRightKanExtension
  let Fh := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let Gh := G.mapHomotopyCategory (ComplexShape.up ℤ)
  let ah := adj₀.mapHomotopyCategory (ComplexShape.up ℤ)
  have hnorm (M) : adj.unit.app (DerivedCategory.Qh.obj M) ≫ R.map (α.app M) =
      DerivedCategory.Qh.map (ah.unit.app M) ≫ β.app (Fh.obj M) := by
    have h := normalization M (Fh.obj M) (𝟙 _)
    simpa only [Adjunction.homEquiv_unit, Functor.map_id, Category.comp_id,
      Functor.comp_obj] using h
  have : NatTrans.CommShift adj.unit ℤ :=
    normalized_unit_commShift DerivedCategory.Qh DerivedCategory.Qh Fh Gh L R ah adj α β
      hnorm
  have hu (n : ℤ) : Adjunction.CommShift.CompatibilityUnit adj
      (L.commShiftIso n) (R.commShiftIso n) := by
    intro X
    have h := NatTrans.shift_app_comm adj.unit n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app] at h
    erw [Category.id_comp] at h
    exact h
  exact ⟨hu, fun n ↦ Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit
    adj _ _ (hu n), fun n e he ↦
      Adjunction.CommShift.compatibilityUnit_unique_right adj _ _ _ he (hu n)⟩

end CategoryTheory
