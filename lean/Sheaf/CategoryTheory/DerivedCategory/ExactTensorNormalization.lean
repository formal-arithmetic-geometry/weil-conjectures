/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso
public import Sheaf.CategoryTheory.DerivedTensorComparison
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory

import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare

/-! # Normalization of exact derived tensor comparisons

Source: Stacks Project, `sites-cohomology.tex`, Tags 0FPQ and 0FPT, and the explicit
cross-functor cancellation argument of the DAG node
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

The derived monoidal structures are the fixed K-flat structures. The comparison is
assumed natural and normalized on K-flat pairs only. The normalization below uses the
native lax tensorator, the inverse of the model isomorphism in the node. Multiplying
by the two model isomorphisms gives precisely the node's displayed equation.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.Functor

private theorem oplax_conclusions {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B] (G : A ⥤ B) (o : G.OplaxMonoidal)
    (u : G.obj (𝟙_ A) ≅ 𝟙_ B)
    (t : ∀ X Y : A, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (hu : o.η = u.hom) (ht : ∀ X Y, o.δ X Y = t X Y)
    (hi : ∀ X Y, IsIso (t X Y)) :
    (∀ X Y, IsIso (t X Y)) ∧
    (∀ X Y Z, G.map (α_ X Y Z).hom ≫ t X (Y ⊗ Z) ≫ (G.obj X ◁ t Y Z) =
      t (X ⊗ Y) Z ≫ (t X Y ▷ G.obj Z) ≫ (α_ (G.obj X) (G.obj Y) (G.obj Z)).hom) ∧
    (∀ X, G.map (λ_ X).hom = t (𝟙_ A) X ≫ (u.hom ▷ G.obj X) ≫
      (λ_ (G.obj X)).hom) ∧
    (∀ X, G.map (ρ_ X).hom = t X (𝟙_ A) ≫ (G.obj X ◁ u.hom) ≫
      (ρ_ (G.obj X)).hom) ∧
    (∃ c : G.CoreMonoidal, c.εIso = u.symm ∧ ∀ X Y, (c.μIso X Y).inv = t X Y) := by
  let : G.OplaxMonoidal := o
  have : IsIso (OplaxMonoidal.η G) := by
    change IsIso o.η
    rw [hu]
    infer_instance
  have (X Y : A) : IsIso (OplaxMonoidal.δ G X Y) := by
    change IsIso (o.δ X Y)
    rw [ht]
    exact hi X Y
  refine ⟨hi, ?_, ?_, ?_, ?_⟩
  · intro X Y Z
    have h := (OplaxMonoidal.associativity G X Y Z).symm
    simpa only [ht] using h
  · intro X
    have h := (OplaxMonoidal.left_unitality_hom G X).symm
    simpa only [ht, hu] using h
  · intro X
    have h := (OplaxMonoidal.right_unitality_hom G X).symm
    simpa only [ht, hu] using h
  · refine ⟨CoreMonoidal.ofOplaxMonoidal G, ?_, ?_⟩
    · apply Iso.ext
      change CategoryTheory.inv o.η = u.inv
      apply IsIso.inv_eq_of_hom_inv_id
      rw [hu]
      exact u.hom_inv_id
    · intro X Y
      exact ht X Y

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem totalKFlat_iff {C : Type uC} [Category.{vC} C] [Abelian C]
    [IsGrothendieckAbelian.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalClosed C] [MonoidalPreadditive C] (P : CochainComplex C ℤ) :
    P.IsKFlatForTotalTensor ↔ (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P := by
  rfl

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [IsGrothendieckAbelian.{vC} C] [HasDerivedCategory.{wC} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [IsGrothendieckAbelian.{vD} D] [HasDerivedCategory.{wD} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D] [MonoidalPreadditive D]
  [Abelian.HasFunctorialFlatResolution D]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorLocalization_isIso (P Q : CochainComplex C ℤ)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q) :
    IsIso (LaxMonoidal.μ DerivedCategory.Q P Q) := by
  have : IsIso (LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj Q)) :=
    DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff Q).2 hQ)
  change IsIso ((_ ⊗ₘ _) ≫
    (LaxMonoidal.μ DerivedCategory.Qh _ _ ≫ DerivedCategory.Qh.map _) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem localizationUnit_isIso :
    IsIso (LaxMonoidal.ε (DerivedCategory.Q (C := C))) := by
  have : IsIso (LaxMonoidal.ε (DerivedCategory.Qh (C := C))) := by
    change IsIso (𝟙 _)
    infer_instance
  change IsIso ((LaxMonoidal.ε DerivedCategory.Qh ≫
    DerivedCategory.Qh.map (LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_totalKFlat_model (K : DerivedCategory C) :
    ∃ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, π, hπ, -, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage K)
  have := hπ
  exact ⟨P, (totalKFlat_iff P).2 hP,
    ⟨asIso (DerivedCategory.Q.map π) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unitModel_inv :
    (((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app (𝟙_ C) ≪≫
      DerivedCategory.singleFunctorObjUnitIso C).inv) =
        LaxMonoidal.ε (DerivedCategory.Q (C := C)) := by
  simp only [DerivedCategory.singleFunctorObjUnitIso]
  change _ = (LaxMonoidal.ε DerivedCategory.Qh ≫
    DerivedCategory.Qh.map (𝟙 _)) ≫ _
  simp only [comp_obj, HomotopyCategory.quotient_obj_singleFunctors_obj,
    DerivedCategory.Qh_obj_singleFunctors_obj, mapIso_symm, Iso.trans_inv, Iso.symm_inv,
    asIso_hom, mapIso_hom, Monoidal.εIso_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, map_id]
  change LaxMonoidal.ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ = _
  simp only [Functor.map_id, Category.id_comp]
  rfl

/-- The prescribed inverse unit comparison of the exact derived functor.
Source: Stacks 0FPQ, 0FPT; the unit formula in
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

The two composites of `singleFunctorIsoCompQ` and `singleFunctorObjUnitIso` are the
native maps `u_C` and `u_D` from the localized unit complex to the derived unit.
`mapCochainComplexεIso.inv` is exactly `e_F⁻¹[0]`, with its termwise single-complex
identification. Thus this composite is `E(u_C⁻¹); κ_I; Q_D(e_F⁻¹[0]); u_D`.
All data are actual composites of the existing canonical isomorphisms. -/
noncomputable def exactDerivedTensorUnitIso (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.IsLeftAdjoint]
    [F.Monoidal] :
    F.mapDerivedCategory.obj (𝟙_ (DerivedCategory C)) ≅ 𝟙_ (DerivedCategory D) :=
  F.mapDerivedCategory.mapIso
      (((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app (𝟙_ C) ≪≫
        DerivedCategory.singleFunctorObjUnitIso C).symm) ≪≫
    F.mapDerivedCategoryFactors.app (𝟙_ (CochainComplex C ℤ)) ≪≫
    DerivedCategory.Q.mapIso F.mapCochainComplexεIso.symm ≪≫
    (DerivedCategory.singleFunctorIsoCompQ D 0).symm.app (𝟙_ D) ≪≫
    DerivedCategory.singleFunctorObjUnitIso D

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A normalized exact derived tensor comparison is invertible and satisfies the native
associativity and both unit equations, and its inverses form a strong monoidal structure.
Source: Stacks 0FPQ and 0FPT, with the explicit abstract cross-functor argument in
(blueprint: lem-sfb-exact-tensor-functor-derived-normalization).

Proof:
1. Grothendieck categories have small colimits. Closedness and symmetry make both tensor
functors left adjoints. The given left adjoint F preserves colimits. Apply
`lem-sfb-termwise-strong-monoidal` (the existing `mapCochainComplexMonoidal` instance)
to obtain the signed total comparison τ and its associativity and both unit equations.
2. By `lem-sfb-abstract-kflat-resolution`, every derived object has a K-flat model.
The complex unit is K-flat by its unitors. Reassociation shows that the tensor of two
K-flat complexes is K-flat. Their F-images are K-flat by the explicit hypothesis.
3. On a K-flat pair, solve the normalization for t by cancelling the source tensor
counit and the two exact-functor factorization isomorphisms. The target counit and τ
are isomorphisms as well, so t is invertible there. The defined unit is already an iso.
4. The native associator and unitors obey the localized complex coherence equations:
this is the lax monoidal coherence of Q, with the invertible model maps cancelled.
5. For associativity on P,Q,R, precompose by E of the left-associated model comparison
and postcompose by κ_P tensor (κ_Q tensor κ_R). Naturality of t and κ, its normalization
twice, and the native equations of step 4 reduce both sides to Q_D of the two termwise
associativity composites. These agree by step 1; cancel the model isomorphisms.
6. For the left unit at Q_C P, precompose by E of (u_C tensor 1) m_{I,P} and postcompose
by κ_P. Substitute the unit formula and normalization at I,P. Naturality of the target
model map and its left-unit equation reduce to the termwise left-unit equation.
7. Repeat on P,I with (1 tensor u_C) m_{P,I}; the termwise right-unit equation gives the
right-unit identity. No braiding compatibility of F is used in either calculation.
8. Transport invertibility and these three equations from K-flat models to arbitrary
objects by naturality of t and the native constraints, cancelling model isomorphisms.
9. Invert t and the prescribed unit iso. Naturality and the three inverted coherence
equations give `CoreMonoidal`, whose forward maps are precisely these inverses. -/
theorem exactDerivedTensorComparison_normalization
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.IsLeftAdjoint] [F.Monoidal] [F.PreservesFlat]
    (hKFlat : ∀ P : CochainComplex C ℤ, P.IsKFlatForTotalTensor →
      CochainComplex.IsKFlatForTotalTensor ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (t : ∀ K L : DerivedCategory C,
      F.mapDerivedCategory.obj (K ⊗ L) ⟶
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L)
    (ht : ∀ (K K' L L' : DerivedCategory C) (a : K ⟶ K') (b : L ⟶ L'),
      F.mapDerivedCategory.map (a ⊗ₘ b) ≫ t K' L' =
        t K L ≫ (F.mapDerivedCategory.map a ⊗ₘ F.mapDerivedCategory.map b))
    (hnorm : ∀ P Q : CochainComplex C ℤ,
      P.IsKFlatForTotalTensor → Q.IsKFlatForTotalTensor →
      F.mapDerivedCategory.map (LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (F.mapCochainComplexμIso P Q).inv =
      t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          F.mapDerivedCategoryFactors.hom.app Q) ≫
        LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q)) :
    (∀ K L : DerivedCategory C, IsIso (t K L)) ∧
    (∀ K L M : DerivedCategory C,
      F.mapDerivedCategory.map (α_ K L M).hom ≫ t K (L ⊗ M) ≫
          (F.mapDerivedCategory.obj K ◁ t L M) =
        t (K ⊗ L) M ≫ (t K L ▷ F.mapDerivedCategory.obj M) ≫
          (α_ (F.mapDerivedCategory.obj K) (F.mapDerivedCategory.obj L)
            (F.mapDerivedCategory.obj M)).hom) ∧
    (∀ K : DerivedCategory C,
      F.mapDerivedCategory.map (λ_ K).hom = t (𝟙_ _) K ≫
        ((F.exactDerivedTensorUnitIso).hom ▷ F.mapDerivedCategory.obj K) ≫
        (λ_ (F.mapDerivedCategory.obj K)).hom) ∧
    (∀ K : DerivedCategory C,
      F.mapDerivedCategory.map (ρ_ K).hom = t K (𝟙_ _) ≫
        (F.mapDerivedCategory.obj K ◁ (F.exactDerivedTensorUnitIso).hom) ≫
        (ρ_ (F.mapDerivedCategory.obj K)).hom) ∧
    (∃ s : F.mapDerivedCategory.CoreMonoidal,
      s.εIso = (F.exactDerivedTensorUnitIso).symm ∧
        ∀ K L : DerivedCategory C, (s.μIso K L).inv = t K L) := by
  let E := F.mapDerivedCategory
  let T := F.mapHomologicalComplex (.up ℤ)
  let W := (HomologicalComplex.quasiIso C (.up ℤ)).kFlat
  let i := W.ι
  let q := i ⋙ DerivedCategory.Q
  let f := i ⋙ T
  let δ : (postcompose₂.obj E).obj (curriedTensor (DerivedCategory C)) ⟶
      (((whiskeringLeft₂ _).obj E).obj E).obj (curriedTensor (DerivedCategory D)) :=
    { app K :=
        { app L := t K L
          naturality L L' b := by
            change E.map (K ◁ b) ≫ t K L' = t K L ≫ (E.obj K ◁ E.map b)
            simpa only [id_tensorHom, E, Functor.map_id] using
              ht K K L L' (𝟙 K) b }
      naturality K K' a := by
        ext L
        change E.map (a ▷ L) ≫ t K' L = t K L ≫ (E.map a ▷ E.obj L)
        simpa only [tensorHom_id, E, Functor.map_id] using
          ht K K' L L a (𝟙 L) }
  have hres : ∀ K : DerivedCategory C, ∃ P : W.FullSubcategory,
      (⊤ : ObjectProperty W.FullSubcategory) P ∧ Nonempty (q.obj P ≅ K) := by
    intro K
    obtain ⟨P, hP, e⟩ := exists_totalKFlat_model K
    exact ⟨⟨P, (totalKFlat_iff P).1 hP⟩, trivial, e⟩
  have hμ (P : CochainComplex D ℤ) (Q : W.FullSubcategory)
      (_ : (⊤ : ObjectProperty W.FullSubcategory) Q) :
      IsIso (LaxMonoidal.μ DerivedCategory.Q P (f.obj Q)) :=
    tensorLocalization_isIso P (f.obj Q)
      ((totalKFlat_iff _).1 (hKFlat Q.obj ((totalKFlat_iff _).2 Q.property)))
  have he (P : W.FullSubcategory) :
      IsIso (F.mapDerivedCategoryFactors.hom.app P.obj) := inferInstance
  have hn (P Q : W.FullSubcategory) :
      (δ.app (q.obj P)).app (q.obj Q) ≫
          (F.mapDerivedCategoryFactors.hom.app P.obj ⊗ₘ
            F.mapDerivedCategoryFactors.hom.app Q.obj) ≫
          LaxMonoidal.μ DerivedCategory.Q (f.obj P) (f.obj Q) =
        E.map (LaxMonoidal.μ q P Q) ≫
          F.mapDerivedCategoryFactors.hom.app (P ⊗ Q).obj ≫
          DerivedCategory.Q.map (OplaxMonoidal.δ f P Q) := by
    simpa [q, f, i, δ, E, T, LaxMonoidal.comp_μ, OplaxMonoidal.comp_δ,
      mapCochainComplex_δ, mapCochainComplexμIso_inv] using
      (hnorm P.obj Q.obj ((totalKFlat_iff _).2 P.property)
        ((totalKFlat_iff _).2 Q.property)).symm
  have := localizationUnit_isIso (C := D)
  let o : E.OplaxMonoidal := OplaxMonoidal.ofLaxSquare (Q₁ := q)
    (Q₂ := DerivedCategory.Q) (F := f) δ
    (fun P ↦ F.mapDerivedCategoryFactors.hom.app P.obj)
    (fun _ _ a ↦ F.mapDerivedCategoryFactors.hom.naturality a.hom)
    hn ⊤ hres hμ
  have hη : o.η = F.exactDerivedTensorUnitIso.hom := by
    change E.map (LaxMonoidal.ε q) ≫
        F.mapDerivedCategoryFactors.hom.app (𝟙_ (CochainComplex C ℤ)) ≫
        DerivedCategory.Q.map (OplaxMonoidal.η f) ≫
        CategoryTheory.inv (LaxMonoidal.ε DerivedCategory.Q) = _
    have hc := unitModel_inv (C := C)
    have hd := unitModel_inv (C := D)
    change E.map (LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map (𝟙 _)) ≫
        F.mapDerivedCategoryFactors.hom.app (𝟙_ (CochainComplex C ℤ)) ≫
        DerivedCategory.Q.map (T.map (𝟙 _) ≫ F.mapCochainComplexεIso.inv) ≫
        CategoryTheory.inv (LaxMonoidal.ε DerivedCategory.Q) = _
    simp only [Functor.map_id, Category.comp_id]
    rw [Category.id_comp]
    rw [← hc]
    have hd' : CategoryTheory.inv (LaxMonoidal.ε (DerivedCategory.Q (C := D))) =
        ((DerivedCategory.singleFunctorIsoCompQ D 0).symm.app (𝟙_ D) ≪≫
          DerivedCategory.singleFunctorObjUnitIso D).hom := by
      apply IsIso.inv_eq_of_hom_inv_id
      rw [← hd]
      exact Iso.inv_hom_id _
    rw [hd']
    rfl
  have hi : ∀ K L : DerivedCategory C, IsIso (t K L) := by
    have hm (P Q : CochainComplex C ℤ) (hP : P.IsKFlatForTotalTensor)
        (hQ : Q.IsKFlatForTotalTensor) :
        IsIso (t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)) := by
      have := tensorLocalization_isIso P Q ((totalKFlat_iff _).1 hQ)
      have := tensorLocalization_isIso (T.obj P) (T.obj Q)
        ((totalKFlat_iff _).1 (hKFlat Q hQ))
      have : IsIso (t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
          (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
            F.mapDerivedCategoryFactors.hom.app Q) ≫
          LaxMonoidal.μ DerivedCategory.Q (T.obj P) (T.obj Q)) := by
        rw [← hnorm P Q hP hQ]
        infer_instance
      exact IsIso.of_isIso_comp_right
        (t (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q))
        ((F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          F.mapDerivedCategoryFactors.hom.app Q) ≫
          LaxMonoidal.μ DerivedCategory.Q (T.obj P) (T.obj Q))
    intro K L
    obtain ⟨P, hP, ⟨a⟩⟩ := exists_totalKFlat_model K
    obtain ⟨Q, hQ, ⟨b⟩⟩ := exists_totalKFlat_model L
    have := hm P Q hP hQ
    have : IsIso (E.map (a.hom ⊗ₘ b.hom) ≫ t K L) := by
      rw [ht]
      infer_instance
    exact IsIso.of_isIso_comp_left (E.map (a.hom ⊗ₘ b.hom)) (t K L)
  exact oplax_conclusions E o F.exactDerivedTensorUnitIso t hη (fun _ _ ↦ rfl) hi

end CategoryTheory.Functor
