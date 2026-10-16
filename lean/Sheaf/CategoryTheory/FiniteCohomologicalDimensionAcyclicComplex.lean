/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-!
# Unbounded acyclic-complex computation in finite cohomological dimension

Source: Stacks Project, Derived Categories, Tag 07K7, assertions (1)-(2), with n = d + 1
(blueprint: lem-kun-finite-cd-acyclic-complex).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- A left exact additive functor of finite cohomological dimension has an unbounded right
derived functor, computed on every complex of right acyclic objects, naturally in chain maps.
Source: Stacks Project, Derived Categories, Tag 07K7, assertions (1)-(2)
(blueprint: lem-kun-finite-cd-acyclic-complex).

Proof plan:
1. Grothendieck abelian categories have enough injectives
   (lem-sp-grothendieck-enough-injectives). Injective objects are right acyclic
   (lem-weil-pbc-derived-functor-injective-vanishing).
2. Choose degreewise injective K-injective replacements
   (lem-pur-kinjective-degreewise-existence). Additivity makes termwise F descend to the
   homotopy category and preserve shifts and cone triangles: the canonical biproduct
   comparison preserves all four entries of the cone differential, including its minus sign.
   Apply lem-weil-pbc-kinjective-total-derived to obtain RF and its universal comparison,
   invertible on K-injectives. Pull the comparison back to complexes.
3. For an exact complex C of right acyclic terms, its cycles fit into short exact sequences
   0 → Zʳ → Cʳ → Zʳ⁺¹ → 0. The long exact sequence
   (lem-weil-pbc-derived-functor-long-exact) gives RᑫF(Zʳ⁺¹) ≅ Rᑫ⁺¹F(Zʳ) for q > 0.
   Iterating backwards d times gives RᑫF(Zʳ) ≅ Rᑫ⁺ᵈF(Zʳ⁻ᵈ) = 0.
   At d = 0 the given bound already gives the vanishing.
4. The degree-zero portion of the same long exact sequence makes
   0 → F(Zʳ) → F(Cʳ) → F(Zʳ⁺¹) → 0 exact. Left exactness identifies the first term
   with the kernel of F(dʳ); hence F(C) is exact in every degree.
5. For a quasi-isomorphism between complexes of right acyclic terms its cone is exact
   (lem-pur-quasi-iso-cone-acyclic). Its terms are right acyclic, by the split short exact
   biproduct sequences and the long exact sequence. Steps 3-4 make its image exact.
   The cone comparison of Step 2 and the cone criterion show F preserves this
   quasi-isomorphism. No boundedness or infinite-filtration convergence is used.
6. Apply Step 5 to L → I(L). Naturality compares its image with RF(Q(L → I(L))).
   These maps and the comparison at I(L) are invertible, so the comparison at L is
   invertible as well.
7. Naturality for any map L → M gives the displayed square. Since its comparison
   components are invertible on right acyclic terms, this identifies RF of the map
   with its termwise image under F, without any quasi-isomorphism assumption on the map. -/
theorem exists_rightDerived_computes_acyclic_of_finite_dimension
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [IsGrothendieckAbelian.{v₁} A] [Abelian B]
    [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (d : ℕ) (hd : ∀ (M : A) (q : ℕ), d < q → IsZero ((F.rightDerived q).obj M)) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ RF),
      (∀ G : DerivedCategory A ⥤ DerivedCategory B,
        Function.Bijective
          (fun β : RF ⟶ G ↦ α ≫ Functor.whiskerLeft DerivedCategory.Q β)) ∧
      (∀ L : CochainComplex A ℤ, (∀ r : ℤ, F.rightAcyclic (L.X r)) →
        IsIso (α.app L)) ∧
      (∀ (L M : CochainComplex A ℤ),
        (∀ r : ℤ, F.rightAcyclic (L.X r)) →
        (∀ r : ℤ, F.rightAcyclic (M.X r)) → ∀ f : L ⟶ M,
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) ≫
          α.app M = α.app L ≫ RF.map (DerivedCategory.Q.map f)) := by
  let RF := F.rightDerivedFunctor
  let α : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF := {
    app := fun K =>
      (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app K) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
        RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K)
    naturality := by
      intro K L f
      have h := F.rightDerivedFunctorUnit.naturality
        ((HomotopyCategory.quotient A (.up ℤ)).map f)
      have hfac := (F.mapHomotopyCategoryFactors (.up ℤ)).inv.naturality
        f
      simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
      simp only [Functor.comp_map,
        DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
      simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at hfac
      have hfac' := congrArg DerivedCategory.Qh.map hfac
      simp only [Functor.map_comp] at hfac'
      rw [← DerivedCategory.Qh.map_comp_assoc, hfac,
        DerivedCategory.Qh.map_comp_assoc]
      rw [reassoc_of% h,
        ← RF.map_comp, ← RF.map_comp,
        DerivedCategory.quotientCompQhIso_hom_naturality] }
  have hα (L : CochainComplex A ℤ)
      (hL : ∀ r : ℤ, F.rightAcyclic (L.X r)) : IsIso (α.app L) := by
    dsimp [α, RF]
    have h := F.isIso_rightDerivedFunctorUnit_app_of_rightAcyclic d hd L hL
    infer_instance
  let c := ComplexShape.up ℤ
  let qA := HomotopyCategory.quotient A c
  let qB := HomotopyCategory.quotient B c
  let eA := DerivedCategory.quotientCompQhIso A
  let eB := DerivedCategory.quotientCompQhIso B
  let αh := F.rightDerivedFunctorUnit
  have hαh : RF.IsRightDerivedFunctor αh (HomotopyCategory.quasiIso A c) := by
    dsimp [RF, αh]
    infer_instance
  refine ⟨RF, α, ?_, ?_, ?_⟩
  · intro G
    let iL : qA ⋙ F.mapHomotopyCategory c ⋙ DerivedCategory.Qh ≅
        F.mapHomologicalComplex c ⋙ DerivedCategory.Q :=
      Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors c) DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex c) eB
    let iR : DerivedCategory.Q ⋙ G ≅ qA ⋙ DerivedCategory.Qh ⋙ G :=
      Functor.isoWhiskerRight eA.symm G
    let lift (β : F.mapHomologicalComplex c ⋙ DerivedCategory.Q ⟶
        DerivedCategory.Q ⋙ G) :
        F.mapHomotopyCategory c ⋙ DerivedCategory.Qh ⟶
          DerivedCategory.Qh ⋙ G := by
      let τ : qA ⋙ (F.mapHomotopyCategory c ⋙ DerivedCategory.Qh) ⟶
          qA ⋙ (DerivedCategory.Qh ⋙ G) :=
        iL.hom ≫ β ≫ iR.hom
      exact Quotient.natTransLift _ τ
    constructor
    · intro f g hfg
      have hfg' : αh ≫ Functor.whiskerLeft DerivedCategory.Qh f =
          αh ≫ Functor.whiskerLeft DerivedCategory.Qh g := by
        apply NatTrans.ext
        apply funext
        intro X
        obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
        have hk := congr_app hfg K
        dsimp [αh, α, eA, eB, RF, c] at hk ⊢
        apply (cancel_epi ((DerivedCategory.quotientCompQhIso B).inv.app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K))).mp
        have hf := f.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
        have hg := g.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
        simp only [Category.assoc] at hk
        rw [hf, hg] at hk
        apply (cancel_mono (G.map ((DerivedCategory.quotientCompQhIso A).hom.app K))).mp
        simpa only [Category.assoc, Functor.comp_obj, Functor.comp_map,
          IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc] using hk
      set_option linter.style.haveILetI false in
        letI : RF.IsRightDerivedFunctor αh (HomotopyCategory.quasiIso A c) := hαh
      exact Functor.rightDerived_ext RF αh (HomotopyCategory.quasiIso A c) G f g hfg'
    · intro β
      let β' := lift β
      let f := RF.rightDerivedDesc αh (HomotopyCategory.quasiIso A c) G β'
      refine ⟨f, ?_⟩
      apply NatTrans.ext
      apply funext
      intro K
      have hf := Functor.rightDerived_fac_app RF αh
        (HomotopyCategory.quasiIso A c) G β' (qA.obj K)
      have hβ : β'.app (qA.obj K) = (iL.hom ≫ β ≫ iR.hom).app K := by
        dsimp [β', lift]
        exact Quotient.natTransLift_app _ _ _ _ _
      dsimp [lift, β', f, iL, iR] at hf hβ
      dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
      dsimp [α]
      have hrest :
          (αh.app (qA.obj K) ≫ RF.map ((DerivedCategory.quotientCompQhIso A).hom.app K)) ≫
            f.app (DerivedCategory.Q.obj K) =
          (DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
            (DerivedCategory.quotientCompQhIso B).hom.app
              ((F.mapHomologicalComplex c).obj K)) ≫ β.app K := by
        have hf' : αh.app (qA.obj K) ≫ f.app (DerivedCategory.Qh.obj (qA.obj K)) =
            β'.app (qA.obj K) := by simpa [f, β', lift, iL, iR] using hf
        have hβ' : β'.app (qA.obj K) =
            (DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
              eB.hom.app ((F.mapHomologicalComplex c).obj K)) ≫ β.app K ≫
              G.map (eA.inv.app K) := by
          simpa [β', lift, iL, iR] using hβ
        calc
          _ = αh.app (qA.obj K) ≫ f.app (DerivedCategory.Qh.obj (qA.obj K)) ≫
              G.map ((DerivedCategory.quotientCompQhIso A).hom.app K) := by
            set_option linter.unnecessarySimpa false in
              simpa [Functor.mapHomotopyCategoryFactors, Category.assoc] using congrArg
                (fun t ↦ αh.app (qA.obj K) ≫ t)
                (f.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K))
          _ = β'.app (qA.obj K) ≫
              G.map ((DerivedCategory.quotientCompQhIso A).hom.app K) := by
            rw [reassoc_of% hf']
          _ = (DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
              eB.hom.app ((F.mapHomologicalComplex c).obj K)) ≫ β.app K := by
            rw [hβ']
            simp only [Category.assoc, Functor.comp_obj]
            rw [← G.map_comp, (DerivedCategory.quotientCompQhIso A).inv_hom_id_app,
              G.map_id, Category.comp_id]
      have hclean : αh.app (qA.obj K) ≫ f.app (DerivedCategory.Qh.obj (qA.obj K)) ≫
          G.map ((DerivedCategory.quotientCompQhIso A).hom.app K) =
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
            eB.hom.app ((F.mapHomologicalComplex c).obj K) ≫ β.app K := by
        simpa [Category.assoc] using hrest
      simp only [Category.assoc]
      rw [f.naturality (eA.hom.app K)]
      have hclean' : αh.app (qA.obj K) ≫
          f.app ((qA ⋙ DerivedCategory.Qh).obj K) ≫ G.map (eA.hom.app K) =
          DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors c).hom.app K) ≫
            eB.hom.app ((F.mapHomologicalComplex c).obj K) ≫ β.app K := by
        simpa only [Functor.comp_obj] using hclean
      rw [hclean']
      dsimp [c]
      rw [← DerivedCategory.Qh.map_comp_assoc]
      have hq := (DerivedCategory.Qh :
        HomotopyCategory B (ComplexShape.up ℤ) ⥤ DerivedCategory B).map_id
      rw [(F.mapHomotopyCategoryFactors (.up ℤ)).inv_hom_id_app]
      have hqK := hq ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K))
      simp only [Functor.comp_obj]
      rw [hqK]
      simp only [Category.id_comp]
      dsimp [eB]
      rw [← Category.assoc, (DerivedCategory.quotientCompQhIso B).inv_hom_id_app,
        Category.id_comp]
  · intro L hL
    exact hα L hL
  · intro L M hL hM f
    exact α.naturality f

end CategoryTheory.Functor
