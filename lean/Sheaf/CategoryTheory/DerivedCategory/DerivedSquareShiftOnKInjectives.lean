/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-! # Shift coherence of a normalized derived square

Source: Stacks Project, sites-cohomology.tex, Tag 0D6G, with Tag 08FI and the
integer-shift refinement in the DAG.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives)

The two computation maps below insert the canonical exact-functor factorization
isomorphisms. The comparison and its right-derived presentations remain specified data.
-/

@[expose] public section

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']

private theorem shift_app_comm_of_comp
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {U V W : C ⥤ D} [U.CommShift ℤ] [V.CommShift ℤ] [W.CommShift ℤ]
    (α : U ⟶ V) (τ : V ⟶ W) [NatTrans.CommShift α ℤ]
    [NatTrans.CommShift (α ≫ τ) ℤ] (X : C) (n : ℤ) [Epi (α.app (X⟦n⟧))] :
    τ.app (X⟦n⟧) ≫ (W.commShiftIso n).hom.app X =
      (V.commShiftIso n).hom.app X ≫ (τ.app X)⟦n⟧' := by
  apply (cancel_epi (α.app (X⟦n⟧))).1
  have h := NatTrans.shift_app_comm (α ≫ τ) n X
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← Category.assoc, NatTrans.shift_app_comm α n X, Category.assoc] at h
  simpa only [Category.assoc] using h.symm

private theorem commShift_of_kinjective
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category* D] [HasShift D ℤ]
    (L : CochainComplex C ℤ ⥤ D) (R : DerivedCategory C ⥤ D)
    [L.CommShift ℤ] [R.CommShift ℤ] (η : L ⟶ DerivedCategory.Q ⋙ R)
    (hres : ∀ K : CochainComplex C ℤ, ∃ I : CochainComplex C ℤ,
      I.IsKInjective ∧ ∃ s : K ⟶ I, QuasiIso s)
    (hshift : ∀ (I : CochainComplex C ℤ), I.IsKInjective → ∀ n : ℤ,
      η.app (I⟦n⟧) ≫ ((DerivedCategory.Q ⋙ R).commShiftIso n).hom.app I =
        (L.commShiftIso n).hom.app I ≫ (η.app I)⟦n⟧') :
    NatTrans.CommShift η ℤ where
  shift_comm n := by
    ext K
    obtain ⟨I, hI, s, hs⟩ := hres K
    have := hs
    have : IsIso ((DerivedCategory.Q ⋙ R).map s) := by
      change IsIso (R.map (DerivedCategory.Q.map s))
      infer_instance
    change (L.commShiftIso n).hom.app K ≫ (η.app K)⟦n⟧' =
      η.app (K⟦n⟧) ≫ ((DerivedCategory.Q ⋙ R).commShiftIso n).hom.app K
    rw [← cancel_mono (((DerivedCategory.Q ⋙ R).map s)⟦n⟧'),
      Category.assoc, ← Functor.map_comp, ← η.naturality,
      Functor.map_comp, ← Functor.commShiftIso_hom_naturality_assoc,
      ← hshift I hI n, Category.assoc,
      ← Functor.commShiftIso_hom_naturality, η.naturality_assoc]

/-- The computation map `a_I = r_D(η_I) φ_r⁻¹` in the proof of Stacks Tag 0D6G.
It is defined for every complex, and is invertible on K-injectives.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives) -/
noncomputable def derivedSquareLeftComputation
    (F : A ⥤ B) (r : B ⥤ B') [F.Additive] [r.Additive]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj
        ((r.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (RF ⋙ r.mapDerivedCategory).obj (DerivedCategory.Q.obj I) :=
  r.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
    r.mapDerivedCategory.map (ηF.app I)

/-- The computation map `b_I = RG(φ_t⁻¹) η_{C(t)I}` in Stacks Tag 0D6G.
It is defined for every complex, and is invertible when `C(t)I` is K-injective.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives) -/
noncomputable def derivedSquareRightComputation
    (G : A' ⥤ B') (t : A ⥤ A') [G.Additive] [t.Additive]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    (RG : DerivedCategory A' ⥤ DerivedCategory B')
    (ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    (I : CochainComplex A ℤ) :
    DerivedCategory.Q.obj
        ((G.mapHomologicalComplex (.up ℤ)).obj ((t.mapHomologicalComplex (.up ℤ)).obj I)) ⟶
      (t.mapDerivedCategory ⋙ RG).obj (DerivedCategory.Q.obj I) :=
  ηG.app ((t.mapHomologicalComplex (.up ℤ)).obj I) ≫
    RG.map (t.mapDerivedCategoryFactors.inv.app I)

/-- A normalized derived square is computed by its specified termwise comparison and
commutes with every integer shift.

Source: Stacks Project, sites-cohomology.tex, Tag 0D6G (restriction of direct images),
Tag 08FI (restriction preserves K-injectives), and derived.tex, Tags 015F and 070H.
(blueprint: lem-weil-pbc-derived-square-shift-on-kinjectives)

Proof: (1) Insert the exact factorization isomorphisms to form `a_I` and `b_I`.
The comparison units are invertible on K-injectives, and `C(t)` preserves these,
so both computation maps are isomorphisms. (2) Apply the stipulated normalization
at `I`; naturality along any representative isomorphism `QI ≅ E` gives the first
formula. (3) The K-injective-shift lemma makes `I[n]` another admissible model,
including negative integers. Additivity identifies termwise functors applied to
this model with their shifts. (4) Naturality of δ shows that both shifted chain
maps have component δ at `I.X (a+n)`; their differentials are multiplied by
`n.negOnePow`, with no sign on δ. (5) The prescribed shift compatibility of the
two units and the exact factorization isomorphisms transports this chain-map
identity to the derived square at `QI`; cancel `a_(I[n])`. (6) Every derived
object has a K-injective representative: first use essential surjectivity of Q,
then a quasi-isomorphism to a K-injective. Naturality of γ and both shift
comparisons transports the equality to every E. This proves the assertion for
the specified γ, without choosing another derived isomorphism.
-/
theorem derivedSquare_shift_on_kinjectives
    (F : A ⥤ B) (G : A' ⥤ B') (t : A ⥤ A') (r : B ⥤ B')
    [F.Additive] [G.Additive] [t.Additive] [r.Additive]
    [PreservesFiniteLimits t] [PreservesFiniteColimits t]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    (δ : F ⋙ r ≅ t ⋙ G)
    (hA : ∀ K : CochainComplex A ℤ, ∃ I : CochainComplex A ℤ,
      I.IsKInjective ∧ ∃ s : K ⟶ I, QuasiIso s)
    (hA' : ∀ K : CochainComplex A' ℤ, ∃ I : CochainComplex A' ℤ,
      I.IsKInjective ∧ ∃ s : K ⟶ I, QuasiIso s)
    (ht : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      CochainComplex.IsKInjective ((t.mapHomologicalComplex (.up ℤ)).obj I))
    (RF : DerivedCategory A ⥤ DerivedCategory B)
    (RG : DerivedCategory A' ⥤ DerivedCategory B')
    (ηF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RF)
    (ηG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RG)
    [RF.IsRightDerivedFunctor ηF (HomologicalComplex.quasiIso A (.up ℤ))]
    [RG.IsRightDerivedFunctor ηG (HomologicalComplex.quasiIso A' (.up ℤ))]
    (hηF : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηF.app I))
    (hηG : ∀ I : CochainComplex A' ℤ, I.IsKInjective → IsIso (ηG.app I))
    [RF.CommShift ℤ] [RG.CommShift ℤ]
    (hshiftF : ∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n : ℤ,
      ηF.app (I⟦n⟧) ≫ ((DerivedCategory.Q ⋙ RF).commShiftIso n).hom.app I =
        ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso n).hom.app I ≫
          (ηF.app I)⟦n⟧')
    (hshiftG : ∀ (I : CochainComplex A' ℤ), I.IsKInjective → ∀ n : ℤ,
      ηG.app (I⟦n⟧) ≫ ((DerivedCategory.Q ⋙ RG).commShiftIso n).hom.app I =
        ((G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).commShiftIso n).hom.app I ≫
          (ηG.app I)⟦n⟧')
    (γ : RF ⋙ r.mapDerivedCategory ≅ t.mapDerivedCategory ⋙ RG)
    (hnorm : ∀ K : CochainComplex A ℤ,
      derivedSquareLeftComputation F r RF ηF K ≫ γ.hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app K) ≫
          derivedSquareRightComputation G t RG ηG K) :
    (∀ (E : DerivedCategory A) (I : CochainComplex A ℤ), I.IsKInjective →
      ∀ e : DerivedCategory.Q.obj I ≅ E,
      IsIso (derivedSquareLeftComputation F r RF ηF I) ∧
      IsIso (derivedSquareRightComputation G t RG ηG I) ∧
      derivedSquareLeftComputation F r RF ηF I ≫
          (RF ⋙ r.mapDerivedCategory).map e.hom ≫ γ.hom.app E =
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I) ≫
          derivedSquareRightComputation G t RG ηG I ≫
            (t.mapDerivedCategory ⋙ RG).map e.hom) ∧
    (∀ (n : ℤ) (E : DerivedCategory A),
      γ.hom.app (E⟦n⟧) ≫ ((t.mapDerivedCategory ⋙ RG).commShiftIso n).hom.app E =
        ((RF ⋙ r.mapDerivedCategory).commShiftIso n).hom.app E ≫ (γ.hom.app E)⟦n⟧') ∧
    (∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n : ℤ,
      (NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app (I⟦n⟧) ≫
          ((t.mapHomologicalComplex (.up ℤ) ⋙
            G.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app I =
        ((F.mapHomologicalComplex (.up ℤ) ⋙
          r.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app I ≫
            ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I)⟦n⟧') ∧
    (∀ (I : CochainComplex A ℤ), I.IsKInjective → ∀ n a : ℤ,
      ((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app (I⟦n⟧)).f a = δ.hom.app (I.X (a + n)) ∧
      (((NatTrans.mapHomologicalComplex δ.hom (.up ℤ)).app I)⟦n⟧').f a = δ.hom.app (I.X (a + n)) ∧
      ((r.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj (I⟦n⟧))).d a (a + 1) =
        n.negOnePow • r.map (F.map (I.d (a + n) (a + 1 + n))) ∧
      ((G.mapHomologicalComplex (.up ℤ)).obj
          ((t.mapHomologicalComplex (.up ℤ)).obj (I⟦n⟧))).d a (a + 1) =
        n.negOnePow • G.map (t.map (I.d (a + n) (a + 1 + n)))) := by
  have hleft (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (derivedSquareLeftComputation F r RF ηF I) := by
    have := hηF I hI
    unfold derivedSquareLeftComputation
    infer_instance
  have hright (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
      IsIso (derivedSquareRightComputation G t RG ηG I) := by
    have := hηG _ (ht I hI)
    unfold derivedSquareRightComputation
    infer_instance
  have hδ : NatTrans.CommShift
      (F₁ := F.mapHomologicalComplex (.up ℤ) ⋙ r.mapHomologicalComplex (.up ℤ))
      (F₂ := t.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ))
      (NatTrans.mapHomologicalComplex δ.hom (.up ℤ)) ℤ := by
    constructor
    intro n
    ext I a
    simp only [Functor.comp_obj, CochainComplex.shiftFunctor_obj_X', NatTrans.comp_app,
      Functor.whiskerRight_app, HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f',
      Functor.whiskerLeft_app, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Category.comp_id, Functor.commShiftIso_comp_hom_app,
      Functor.mapHomologicalComplex_map_f]
    erw [Functor.map_id, Category.id_comp, Functor.map_id, Category.comp_id]
    rfl
  have := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E I hI e
    refine ⟨hleft I hI, hright I hI, ?_⟩
    rw [γ.hom.naturality, ← Category.assoc, hnorm I, Category.assoc]
  · have := commShift_of_kinjective _ RF ηF hA hshiftF
    have := commShift_of_kinjective _ RG ηG hA' hshiftG
    let a : (F.mapHomologicalComplex (.up ℤ) ⋙ r.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (RF ⋙ r.mapDerivedCategory) :=
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ r.mapDerivedCategoryFactors.inv ≫
        (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ηF _ ≫
        (Functor.associator _ _ _).hom
    let b : (t.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ)) ⋙
        DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ (t.mapDerivedCategory ⋙ RG) :=
      (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft _ ηG ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight t.mapDerivedCategoryFactors.inv _ ≫
        (Functor.associator _ _ _).hom
    let u : F.mapHomologicalComplex (.up ℤ) ⋙ r.mapHomologicalComplex (.up ℤ) ⟶
        t.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) :=
      NatTrans.mapHomologicalComplex δ.hom (.up ℤ)
    have : NatTrans.CommShift a ℤ := by dsimp [a]; infer_instance
    have : NatTrans.CommShift b ℤ := by dsimp [b]; infer_instance
    have : NatTrans.CommShift u ℤ := hδ
    have heq : a ≫ Functor.whiskerLeft DerivedCategory.Q γ.hom =
        Functor.whiskerRight u DerivedCategory.Q ≫ b := by
      ext K
      simpa [a, b, u, derivedSquareLeftComputation, derivedSquareRightComputation] using
        hnorm K
    have : NatTrans.CommShift (a ≫ Functor.whiskerLeft DerivedCategory.Q γ.hom) ℤ := by
      rw [heq]
      infer_instance
    have : NatTrans.CommShift (Functor.whiskerLeft DerivedCategory.Q γ.hom) ℤ :=
      commShift_of_kinjective _ _ _ hA (by
        intro I hI n
        have := hI
        have : IsIso (a.app (I⟦n⟧)) := by
          simpa [a, derivedSquareLeftComputation] using hleft (I⟦n⟧) inferInstance
        exact shift_app_comm_of_comp a _ I n)
    have : NatTrans.CommShift γ.hom ℤ :=
      NatTrans.CommShift.of_whiskerLeft γ.hom DerivedCategory.Q (fun E ↦
        ⟨DerivedCategory.Q.objPreimage E, (DerivedCategory.Q.objObjPreimageIso E).inv,
          inferInstance⟩)
    intro n E
    exact (NatTrans.shift_app_comm γ.hom n E).symm
  · intro I _ n
    exact (NatTrans.shift_app_comm
      (F₁ := F.mapHomologicalComplex (.up ℤ) ⋙ r.mapHomologicalComplex (.up ℤ))
      (F₂ := t.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ))
      (NatTrans.mapHomologicalComplex δ.hom (.up ℤ)) n I).symm
  · intro I _ n a
    refine ⟨rfl, rfl, ?_, ?_⟩ <;>
      simp only [Functor.mapHomologicalComplex_obj_d, CochainComplex.shiftFunctor_obj_d',
        Units.smul_def, Functor.map_zsmul]

end CategoryTheory
