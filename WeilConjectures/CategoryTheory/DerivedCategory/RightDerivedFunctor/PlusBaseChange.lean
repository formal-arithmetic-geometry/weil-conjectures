/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Base change for bounded below right derived functors

Consider a square of additive functors between abelian categories
```
    B ───── G ─────▶ C
    │                │
    β                γ
    ▼                ▼
    B' ──── G' ────▶ C'
```
commuting up to an isomorphism `e : G ⋙ γ ≅ β ⋙ G'`, where `β` and `γ` are exact. We construct
the base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` of functors
`DerivedCategory.Plus B ⥤ DerivedCategory.Plus C'`, where `β⁺` and `γ⁺` are the functors
induced by `β` and `γ` on the bounded below derived categories
(`Functor.rightDerivedFunctorPlusBaseChange`), and the induced base change morphisms
`γ (R^p G Y) ⟶ R^p G' (β Y)` of the classical right derived functors
(`Functor.rightDerivedBaseChange`).

The morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` is the unique one compatible with the units: on a bounded
below complex `K` it is the composite of `γ G(K) ≅ G' β(K)` with the unit
`G' β(K) ⟶ R⁺G'(β K)`. It is an isomorphism when `β` preserves injective objects, but in
general it is not.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The base change morphism `G(K) ⟶ R⁺G'(β K)` at the level of bounded below homotopy
categories, from which `Functor.rightDerivedFunctorPlusBaseChange` is obtained by the universal
property of `R⁺G`: it is `γ G(K) ≅ G' β(K)` followed by the unit of `R⁺G'`. -/
noncomputable def rightDerivedFunctorPlusBaseChangeAux (e : G ⋙ γ ≅ β ⋙ G') :
    G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ γ.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙ β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  Functor.whiskerLeft G.mapHomotopyCategoryPlus γ.mapDerivedCategoryPlusFactorsh.hom ≫
    Functor.whiskerRight ((mapHomotopyCategoryPlusCompIso (Iso.refl (G ⋙ γ))).hom ≫
      NatTrans.mapHomotopyCategoryPlus e.hom ≫
      (mapHomotopyCategoryPlusCompIso (Iso.refl (β ⋙ G'))).inv) DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft β.mapHomotopyCategoryPlus G'.rightDerivedFunctorPlusUnit ≫
    Functor.whiskerRight β.mapDerivedCategoryPlusFactorsh.inv G'.rightDerivedFunctorPlus

/-- The base change morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` attached to an isomorphism
`e : G ⋙ γ ≅ β ⋙ G'` with `β` and `γ` exact. -/
noncomputable def rightDerivedFunctorPlusBaseChange (e : G ⋙ γ ≅ β ⋙ G') :
    G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G'.rightDerivedFunctorPlus :=
  (G.rightDerivedFunctorPlus ⋙ γ.mapDerivedCategoryPlus).rightDerivedDesc
    (Functor.whiskerRight G.rightDerivedFunctorPlusUnit γ.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom)
    (HomotopyCategory.Plus.quasiIso B) _ (rightDerivedFunctorPlusBaseChangeAux e)

/-- The base change morphism is characterized by its compatibility with the units. -/
@[reassoc]
lemma rightDerivedFunctorPlusBaseChange_fac (e : G ⋙ γ ≅ β ⋙ G') :
    (Functor.whiskerRight G.rightDerivedFunctorPlusUnit γ.mapDerivedCategoryPlus ≫
      (Functor.associator _ _ _).hom) ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedFunctorPlusBaseChange e) =
    rightDerivedFunctorPlusBaseChangeAux e :=
  rightDerived_fac _ _ _ _ _

/-- The base change morphism `γ (R^p G Y) ⟶ R^p G' (β Y)` of the classical right derived
functors, natural in `Y`, attached to an isomorphism `e : G ⋙ γ ≅ β ⋙ G'` with `β` and `γ`
exact. It is induced by `Functor.rightDerivedFunctorPlusBaseChange` through the
identifications `R^p G Y ≅ H^p(R⁺G(Y[0]))`. -/
noncomputable def rightDerivedBaseChange (e : G ⋙ γ ≅ β ⋙ G') (p : ℕ) :
    G.rightDerived p ⋙ γ ⟶ β ⋙ G'.rightDerived p :=
  (Functor.isoWhiskerRight (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).symm
      γ).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0 ⋙ G.rightDerivedFunctorPlus)
      (γ.mapDerivedCategoryPlusHomologyFunctorIso p).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (Functor.whiskerRight (rightDerivedFunctorPlusBaseChange e)
        (DerivedCategory.Plus.homologyFunctor C' p)) ≫
    Functor.whiskerRight (β.mapDerivedCategoryPlusSingleFunctor 0).hom
      (G'.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor C' p) ≫
    Functor.whiskerLeft β (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom

/-- **The base change morphism is invertible when `β` sends injectives to `G'`-acyclics.** If `G'`
is left exact and `β` sends injective objects to `G'`-acyclic objects, then the base change
morphism `R⁺G ⋙ γ⁺ ⟶ β⁺ ⋙ R⁺G'` attached to `e : G ⋙ γ ≅ β ⋙ G'` is an isomorphism. On a
bounded below complex `T` of injectives it is the composite of `γ G(T) ≅ G' β(T)` with the unit
`G' β(T) ⟶ R⁺G'(β T)`, which is invertible since `β T` is a bounded below complex of
`G'`-acyclic objects. -/
theorem isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic [PreservesFiniteLimits G']
    (e : G ⋙ γ ≅ β ⋙ G') (h : ∀ (I : B) [Injective I], G'.rightAcyclic (β.obj I)) :
    IsIso (rightDerivedFunctorPlusBaseChange e) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  -- represent `X` by a bounded below complex of injectives `T`
  obtain ⟨K, ⟨eK⟩⟩ : ∃ K : HomotopyCategory.Plus B,
      Nonempty (DerivedCategory.Plus.Qh.obj K ≅ X) :=
    ⟨_, ⟨DerivedCategory.Plus.Qh.objObjPreimageIso X⟩⟩
  obtain ⟨M, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  obtain ⟨a, _⟩ := M.2
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective M a
  let T' := (InjectiveObject.ι B).mapCochainComplexPlus.obj T
  have : ∀ n, Injective (T'.obj.X n) := fun n ↦ (T.obj.X n).2
  have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map i)) :=
    Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso B) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
  rw [← NatTrans.isIso_app_iff_of_iso _ eK,
    NatTrans.isIso_app_iff_of_iso _
      (asIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient B).map i)))]
  set K' := (HomotopyCategory.Plus.quotient B).obj T'
  have hK' : ∀ n : ℤ, Injective (K'.obj.as.X n) := fun n ↦ (T.obj.X n).2
  have h₁ : IsIso (G.rightDerivedFunctorPlusUnit.app K') := inferInstance
  let LT : CochainComplex.Plus B' := ⟨(β.mapHomotopyCategoryPlus.obj K').obj.as,
    (HomotopyCategory.plus_quotient_obj_iff _).1 (β.mapHomotopyCategoryPlus.obj K').property⟩
  have h₂ : IsIso (G'.rightDerivedFunctorPlusUnit.app (β.mapHomotopyCategoryPlus.obj K')) :=
    G'.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic LT (fun n ↦ h (T'.obj.X n))
  have hfac := congr_app (rightDerivedFunctorPlusBaseChange_fac e) K'
  have h₃ : IsIso ((rightDerivedFunctorPlusBaseChangeAux e).app K') := by
    dsimp [rightDerivedFunctorPlusBaseChangeAux]
    infer_instance
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id, Functor.whiskerLeft_app] at hfac
  rw [← hfac] at h₃
  exact IsIso.of_isIso_comp_left (γ.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusUnit.app K')) _

end CategoryTheory.Functor
