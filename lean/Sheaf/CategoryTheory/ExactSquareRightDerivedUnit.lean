/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-! # Right-derived comparison unit for an exact coefficient square

Source: Stacks Project, Derived Categories, Tags 070I and 070Y, and the exact
postcomposition argument in the node's proof
(blueprint: lem-sfb-exact-square-right-derived-unit).

The derived pairs are the recorded pairs constructed from arbitrary quasi-isomorphisms
to K-injective complexes. All localization identifications are explicit.
-/

@[expose] public section

set_option autoImplicit false

universe uA uA' uB uB' vA vA' vB vB' wA wA' wB wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {A : Type uA} {A' : Type uA'} {B : Type uB} {B' : Type uB'}
  [Category.{vA} A] [Category.{vA'} A'] [Category.{vB} B] [Category.{vB'} B']
  [Abelian A] [Abelian A'] [Abelian B] [Abelian B']
  [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wA'} A']
  [HasDerivedCategory.{wB} B] [HasDerivedCategory.{wB'} B']

/-- The unit D(V)(ηF), with the canonical identifications from QVF to D(V)QF.
Source: Stacks Tag 070Y and node proof step 1
(blueprint: lem-sfb-exact-square-right-derived-unit).
The data are the inverse composition comparison, the inverse exact-localization
comparison for V, and the recorded right-derived unit whiskered by D(V). -/
noncomputable def exactSquareRightDerivedPostcompositionUnit
    (F : A ⥤ B) (V : B ⥤ B') [F.Additive] [V.Additive]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (hA : ∀ P : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : P ⟶ I), I.IsKInjective ∧ QuasiIso s) :
    (F ⋙ V).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions hA ⋙
        V.mapDerivedCategory :=
  whiskerRight (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ V)) (.up ℤ)).inv
      DerivedCategory.Qh ≫
    (associator _ _ _).hom ≫
    whiskerLeft (F.mapHomotopyCategory (.up ℤ)) V.mapDerivedCategoryFactorsh.inv ≫
    (associator _ _ _).inv ≫
    whiskerRight (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA) V.mapDerivedCategory ≫
    (associator _ _ _).hom

-- A unit computed on K-injectives has the universal property, independently of
-- the functor used after taking the derived category.
private theorem isLeftKanExtension_of_isIso_on_kInjectives
    (h : ∀ P : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : P ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (E : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory B')
    (H : DerivedCategory A ⥤ DerivedCategory B')
    (α : E ⟶ DerivedCategory.Qh ⋙ H)
    (hα : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient A (.up ℤ)).obj I))) :
    H.IsLeftKanExtension α := by
  classical
  let π := HomotopyCategory.quotient A (.up ℤ)
  let Q : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory A := DerivedCategory.Qh
  choose J f hJ hf using h
  let j (X : DerivedCategory A) := J (DerivedCategory.Q.objPreimage X)
  have hj (X : DerivedCategory A) : (j X).IsKInjective := hJ _
  have hq (P : CochainComplex A ℤ) : IsIso (DerivedCategory.Q.map (f P)) := by
    have := hf P
    infer_instance
  let e (X : DerivedCategory A) : X ≅ Q.obj (π.obj (j X)) :=
    (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
      asIso (DerivedCategory.Q.map (f (DerivedCategory.Q.objPreimage X))) ≪≫
      (DerivedCategory.quotientCompQhIso A).symm.app (j X)
  have hi (X : DerivedCategory A) : IsIso (α.app (π.obj (j X))) := hα _
  let lift {P : HomotopyCategory A (.up ℤ)} {X : DerivedCategory A}
      (a : Q.obj P ⟶ Q.obj (π.obj (j X))) : P ⟶ π.obj (j X) :=
    (Equiv.ofBijective Q.map (CochainComplex.IsKInjective.Qh_map_bijective P (j X))).symm a
  have lift_spec {P : HomotopyCategory A (.up ℤ)} {X : DerivedCategory A}
      (a : Q.obj P ⟶ Q.obj (π.obj (j X))) : Q.map (lift a) = a := by
    exact (Equiv.ofBijective Q.map
      (CochainComplex.IsKInjective.Qh_map_bijective P (j X))).apply_symm_apply a
  let desc (T : DerivedCategory A ⥤ DerivedCategory B') (τ : E ⟶ Q ⋙ T) : H ⟶ T :=
    { app := fun X ↦ H.map (e X).hom ≫ CategoryTheory.inv (α.app (π.obj (j X))) ≫
        τ.app (π.obj (j X)) ≫ T.map (e X).inv
      naturality := by
        intro X Y a
        let b := lift ((e X).inv ≫ a ≫ (e Y).hom)
        have hb : Q.map b = (e X).inv ≫ a ≫ (e Y).hom := lift_spec _
        have ha := α.naturality b
        have ht := τ.naturality b
        change E.map b ≫ α.app (π.obj (j Y)) =
          α.app (π.obj (j X)) ≫ H.map (Q.map b) at ha
        change E.map b ≫ τ.app (π.obj (j Y)) =
          τ.app (π.obj (j X)) ≫ T.map (Q.map b) at ht
        have he : a ≫ (e Y).hom = (e X).hom ≫ Q.map b := by simp [hb]
        have he' : Q.map b ≫ (e Y).inv = (e X).inv ≫ a := by simp [hb]
        change H.map a ≫ (H.map (e Y).hom ≫ _ ≫ _ ≫ _) =
          (H.map (e X).hom ≫ _ ≫ _ ≫ _) ≫ T.map a
        rw [← H.map_comp_assoc, he, H.map_comp, Category.assoc]
        have hn : H.map (Q.map b) ≫ CategoryTheory.inv (α.app (π.obj (j Y))) =
            CategoryTheory.inv (α.app (π.obj (j X))) ≫ E.map b := by
          apply (cancel_epi (α.app (π.obj (j X)))).mp
          rw [← Category.assoc, ← ha, Category.assoc, IsIso.hom_inv_id,
            Category.comp_id, IsIso.hom_inv_id_assoc]
        rw [reassoc_of% hn, reassoc_of% ht, ← T.map_comp, he', T.map_comp]
        simp only [Category.assoc] }
  have fac (T : DerivedCategory A ⥤ DerivedCategory B') (τ : E ⟶ Q ⋙ T) :
      α ≫ whiskerLeft Q (desc T τ) = τ := by
    ext P
    let t := lift (e (Q.obj P)).hom
    have ht : Q.map t = (e (Q.obj P)).hom := lift_spec _
    change α.app P ≫ (H.map (e (Q.obj P)).hom ≫ _ ≫ _ ≫ _) = τ.app P
    have ha : E.map t ≫ α.app (π.obj (j (Q.obj P))) =
        α.app P ≫ H.map (Q.map t) := α.naturality t
    have hτ : E.map t ≫ τ.app (π.obj (j (Q.obj P))) =
        τ.app P ≫ T.map (Q.map t) := τ.naturality t
    rw [← ht, ← Category.assoc, ← ha]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, hτ, ht]
    simp [← T.map_comp]
  have uniq (T : DerivedCategory A ⥤ DerivedCategory B') (β γ : H ⟶ T)
      (heq : α ≫ whiskerLeft Q β = α ≫ whiskerLeft Q γ) : β = γ := by
    ext X
    have hc := NatTrans.congr_app heq (π.obj (j X))
    have he : β.app (Q.obj (π.obj (j X))) = γ.app (Q.obj (π.obj (j X))) :=
      (cancel_epi (α.app (π.obj (j X)))).mp hc
    apply (cancel_mono (T.map (e X).hom)).mp
    rw [← β.naturality, ← γ.naturality, he]
  refine ⟨⟨IsInitial.ofUniqueHom (fun Z ↦ StructuredArrow.homMk (desc Z.right Z.hom)
    (fac Z.right Z.hom)) ?_⟩⟩
  intro Z k
  apply StructuredArrow.hom_ext
  exact uniq Z.right k.right (desc Z.right Z.hom) (k.w.trans (fac Z.right Z.hom).symm)

/-- Exact postcomposition is a total right-derived pair, and an exact coefficient
square has a unique comparison compatible with the units on every complex.
Source: Stacks Tags 070I and 070Y; agent exact-postcomposition and unit-comparison
consequence, node proof steps 1--6
(blueprint: lem-sfb-exact-square-right-derived-unit).

Proof plan:
1. Put H = RF ⋙ D(V), E = (F ⋙ V)_K ⋙ Qh and let α be the displayed unit.
   The exact-localization and composition comparisons identify α_I with D(V)(ηF_I).
   The recorded K-injective computation clause makes this invertible for K-injective I.
2. Essential surjectivity of Q and the hypothesis hA give, for each derived object X,
   a K-injective I_X and an isomorphism e_X : X ≅ QI_X. The Hom bijection into a
   K-injective target lifts every conjugated derived arrow uniquely to the homotopy
   category; no preservation of K-injectives by U is needed.
3. For T and τ : E ⟶ Qh ⋙ T, set β_X = H(e_X) ≫ α_(I_X)⁻¹ ≫ τ_(I_X) ≫ T(e_X)⁻¹.
   Naturality of α and τ at the lifted arrow gives naturality of β.
4. Lift e_(QP) to a homotopy-class map P ⟶ I_(QP), using only K-injectivity of
   its target. Naturality at this lift proves α_P ≫ β_(QP) = τ_P for every P.
5. Any other β with this factorization agrees at I_X by cancellation of α_(I_X).
   Naturality at e_X then forces agreement at X. Thus the factorization map is
   bijective for every T, precisely the total right-derived universal property.
6. Take T = D(U) ⋙ RG. Compose Q(c) with the unit ηG at U(P) and transport by
   the exact-localization comparison for U. The preceding bijection produces the
   unique γ satisfying the displayed equation. The composition and localization
   maps in that equation are exactly the canonical identifications in steps 1 and 6.
-/
theorem exactSquare_rightDerived_unit
    (F : A ⥤ B) (G : A' ⥤ B') (U : A ⥤ A') (V : B ⥤ B')
    [F.Additive] [G.Additive] [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (hA : ∀ P : CochainComplex A ℤ,
      ∃ (I : CochainComplex A ℤ) (s : P ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (hA' : ∀ P : CochainComplex A' ℤ,
      ∃ (I : CochainComplex A' ℤ) (s : P ⟶ I), I.IsKInjective ∧ QuasiIso s)
    (c : F ⋙ V ≅ U ⋙ G) :
    (F.rightDerivedFunctorOfQuasiIsoResolutions hA ⋙ V.mapDerivedCategory).IsRightDerivedFunctor
        (exactSquareRightDerivedPostcompositionUnit F V hA)
        (HomotopyCategory.quasiIso A (.up ℤ)) ∧
      ∃! γ : F.rightDerivedFunctorOfQuasiIsoResolutions hA ⋙ V.mapDerivedCategory ⟶
          U.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hA',
        ∀ P : CochainComplex A ℤ,
          (exactSquareRightDerivedPostcompositionUnit F V hA).app
              ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
            γ.app (DerivedCategory.Qh.obj
              ((HomotopyCategory.quotient A (.up ℤ)).obj P)) =
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app
              ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
            DerivedCategory.Qh.map
              ((mapHomotopyCategoryCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).inv.app
                ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
            (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA').app
              ((U.mapHomotopyCategory (.up ℤ)).obj
                ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≫
            (G.rightDerivedFunctorOfQuasiIsoResolutions hA').map
              (U.mapDerivedCategoryFactorsh.inv.app
                ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := by
  classical
  let H := F.rightDerivedFunctorOfQuasiIsoResolutions hA ⋙ V.mapDerivedCategory
  let α := exactSquareRightDerivedPostcompositionUnit F V hA
  let T := U.mapDerivedCategory ⋙ G.rightDerivedFunctorOfQuasiIsoResolutions hA'
  let τ : (F ⋙ V).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ T :=
    whiskerRight (NatTrans.mapHomotopyCategory c.hom (.up ℤ)) DerivedCategory.Qh ≫
      whiskerRight (mapHomotopyCategoryCompIso (Iso.refl (U ⋙ G)) (.up ℤ)).inv
        DerivedCategory.Qh ≫
      (associator _ _ _).hom ≫
      whiskerLeft (U.mapHomotopyCategory (.up ℤ))
        (G.rightDerivedFunctorOfQuasiIsoResolutionsUnit hA') ≫
      (associator _ _ _).inv ≫
      whiskerRight U.mapDerivedCategoryFactorsh.inv
        (G.rightDerivedFunctorOfQuasiIsoResolutions hA') ≫
      (associator _ _ _).hom
  have hα : H.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (.up ℤ)) := by
    constructor
    apply isLeftKanExtension_of_isIso_on_kInjectives hA
    intro I hI
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso hA I
    dsimp [α, exactSquareRightDerivedPostcompositionUnit]
    infer_instance
  refine ⟨hα, ?_⟩
  let γ := H.rightDerivedDesc α (HomotopyCategory.quasiIso A (.up ℤ)) T τ
  have hγ : ∀ P : CochainComplex A ℤ,
      α.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        γ.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient A (.up ℤ)).obj P)) =
        τ.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
    intro P
    exact H.rightDerived_fac_app α (HomotopyCategory.quasiIso A (.up ℤ)) T τ _
  refine ⟨γ, ?_, ?_⟩
  · intro P
    simpa [τ] using hγ P
  · intro δ hδ
    apply H.rightDerived_ext α (HomotopyCategory.quasiIso A (.up ℤ)) T
    ext K
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    exact (hδ P).trans (by simpa [τ] using (hγ P).symm)

end CategoryTheory.Functor
