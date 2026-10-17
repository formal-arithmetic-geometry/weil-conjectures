/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex

/-!

# The monoidal structure of the derived pullback on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧) : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` is strong monoidal for
the derived tensor products `- ⊗ᴸ_{Λ} -` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`:
```
m_{K,L} : Lf^* (K ⊗ᴸ_{Λ_Y} L) ≅ Lf^* K ⊗ᴸ_{Λ_X} Lf^* L,    Lf^* Λ_Y ≅ Λ_X.
```
This comparison is the input of the derived projection morphisms, hence of Verdier duality and
Poincaré duality.

The pullback `f^*` of module objects over `Λ` is strong monoidal for the relative tensor products
(`ProEtale.CondensedRing.monoidal_upperStar`), with comparison isomorphisms
`μ : f^* M ⊗_{Λ_X} f^* N ≅ f^* (M ⊗_{Λ_Y} N)`. The comparison `m` is constructed from `μ`
(`ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`) in three steps:

1. **Complexes.** For complexes `A` and `B` of module objects over `Λ_Y`, `μ` applied degreewise
   gives a map of complexes `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` for the total tensor product of
   complexes (`ProEtale.CondensedRing.upperStarTensorComplexHom`): on the summand
   `f^* A^p ⊗ f^* B^q` of degree `n = p + q` it is `μ` followed by the inclusion of
   `f^* (A^p ⊗ B^q)` into `f^* ((A ⊗ B)^n)`.
2. **Homotopy category.** Composing with the lax structure `Qh A' ⊗ᴸ Qh B' ⟶ Qh (A' ⊗ B')` of
   the localization `Qh : K(Mod_{Λ_X}) ⥤ D(Mod_{Λ_X})`, this gives a natural transformation of
   bifunctors `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` on the homotopy category of
   `Mod_{Λ_Y}` (`ProEtale.CondensedRing.upperStarTensorCounit`).
3. **Derived categories.** The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`, with the
   transformation of step 2 precomposed with the counits of `Lf^*`, is a left derived bifunctor
   of `(A, B) ↦ Qh (f^* (A ⊗ B))` (`ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`).
   The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` receives a canonical transformation to the same
   bifunctor, so the universal property of left derived bifunctors
   (`Functor.leftDerived₂Lift`) gives the comparison
   `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` (`ProEtale.CondensedRing.leftDerivedUpperStarTensor`),
   characterized by its compatibility with the counits.

The unit comparison `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso` is
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙) ≅ Qh 𝟙`: the counit of `Lf^*`, an isomorphism since `f^*` is exact,
followed by the unit comparison of `monoidal_upperStar` in degree `0`. Together with the inverse
of `m` as tensorator, it makes `Lf^*` strong monoidal
(`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`).

## Sorried input

All the data is constructed; the following properties are `sorry`ed.

- `ProEtale.CondensedRing.upperStarTensorComplexHom_comm`: the degreewise maps of step 1
  commute with the differentials. This is the naturality of `μ` together with the additivity of
  `f^*`.
- the naturality of the transformations `upperStarTensorCounit` and
  `leftDerivedUpperStarTensorLeftCounit` (in both variables): the naturality of `μ`, of the lax
  structure of `Qh` and of the counit of `Lf^*`, checked on representatives in the homotopy
  category.
- `ProEtale.CondensedRing.isLeftDerivedFunctor₂_upperStarTensor`: the bifunctor
  `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor. It is computed on pairs of K-flat complexes,
  `f^*` preserving K-flat complexes; on such a pair both the counits of `Lf^*` and the lax
  structure of `Qh` are isomorphisms.
- `ProEtale.CondensedRing.isIso_leftDerivedUpperStarTensor`: the comparison `m` is an
  isomorphism. On a pair of K-flat complexes both sides are computed by `f^* A ⊗ f^* B` and
  `f^* (A ⊗ B)`, and `m` is induced by `μ`, an isomorphism.
- the associativity and the unitality of `monoidal_leftDerivedUpperStar`. They are checked on
  pairs (resp. triples) of K-flat complexes, where all the comparisons are induced by the
  coherent tensorator `μ`.

## Main definitions

- `ProEtale.CondensedRing.leftDerivedUpperStarTensor`: the comparison
  `Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L`, as a natural transformation of bifunctors.
- `ProEtale.CondensedRing.leftDerivedUpperStarTensorIso`: the comparison isomorphism.
- `ProEtale.CondensedRing.leftDerivedUpperStarUnitIso`: the unit comparison `Lf^* 𝟙 ≅ 𝟙`.
- `ProEtale.CondensedRing.monoidal_leftDerivedUpperStar`: the strong monoidal structure on `Lf^*`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

private lemma mapCochainComplexμIso_hom_f_eq_desc
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (n : ℤ) :
    (G.mapCochainComplexμIso K L).hom.f n =
      HomologicalComplex.mapBifunctorDesc (fun p q h ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n h)) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  exact Functor.ιTensorObj_mapCochainComplexμIso_hom_f G K L p q n h

private lemma mapCochainComplexDesc_comm
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D] [HasZeroObject C] [HasZeroObject D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
    [∀ (X₁ X₂ : GradedObject ℤ D), X₁.HasTensor X₂]
    [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ X₁, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).obj X₁)]
    [∀ X₂, PreservesColimit (Functor.empty.{0} D) ((curriedTensor D).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (G : C ⥤ D) [G.Additive] [G.Monoidal]
    [∀ j, PreservesColimitsOfShape
      (Discrete (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) ⁻¹' {j})) G]
    (K L : CochainComplex C ℤ) (n n' : ℤ)
    (h : (ComplexShape.up ℤ).Rel n n') :
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n hpq)) ≫
      ((G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)).d n n' =
    ((G.mapHomologicalComplex (.up ℤ)).obj K ⊗
        (G.mapHomologicalComplex (.up ℤ)).obj L).d n n' ≫
      HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
        Functor.LaxMonoidal.μ G (K.X p) (L.X q) ≫
          G.map (HomologicalComplex.ιTensorObj K L p q n' hpq)) := by
  simpa only [mapCochainComplexμIso_hom_f_eq_desc] using
    (G.mapCochainComplexμIso K L).hom.comm' n n' h

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### Instances

Direct instances for complexes of module objects over `Λ_Z`. Finding them from the generic
instances on `Mod` exceeds the default heartbeat limit, so they are recorded once here. -/

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
instance hasTensor_cochainComplex (Z : Scheme.{u})
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) ℤ) :
    HomologicalComplex.HasTensor A B :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategoryStruct_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategoryStruct
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

set_option synthInstance.maxHeartbeats 200000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
noncomputable instance monoidalCategory_cochainComplex (Z : Scheme.{u}) :
    MonoidalCategory
      (CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
        ℤ) :=
  inferInstance

/-! ### Complexes -/

/-- The degreewise comparison `(f^* A ⊗ f^* B)^n ⟶ f^* ((A ⊗ B)^n)` for complexes `A` and `B`
of module objects over `Λ_Y`: on the summand `f^* A^p ⊗ f^* B^q` with `p + q = n`, the tensorator
`μ : f^* A^p ⊗ f^* B^q ⟶ f^* (A^p ⊗ B^q)` followed by `f^*` of the inclusion of the summand. -/
noncomputable def upperStarTensorComplexHomX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).X n ⟶
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).X n :=
  HomologicalComplex.mapBifunctorDesc fun p q h ↦
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ (A.X p) (B.X q) ≫
      (f)^*⟦Λ⟧.map (HomologicalComplex.ιTensorObj A B p q n h)

/-- The degreewise comparisons `upperStarTensorComplexHomX` commute with the differentials. -/
lemma upperStarTensorComplexHom_comm
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n n' : ℤ)
    (_ : (ComplexShape.up ℤ).Rel n n') :
    upperStarTensorComplexHomX Λ f A B n ≫
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B)).d n n' =
      (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B).d n n' ≫
        upperStarTensorComplexHomX Λ f A B n' := by
  simpa only [upperStarTensorComplexHomX] using
    mapCochainComplexDesc_comm ((f)^*⟦Λ⟧) A B n n' (by assumption)

/-- The comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` of complexes of module objects, induced
degreewise by the tensorator of the strong monoidal pullback `f^*`. -/
noncomputable def upperStarTensorComplexHom
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A ⊗
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B ⟶
      ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj (A ⊗ B) where
  f n := upperStarTensorComplexHomX Λ f A B n
  comm' n n' h := upperStarTensorComplexHom_comm Λ f A B n n' h

/-! ### The homotopy category -/

/-- The bifunctor `(A, B) ↦ Qh (f^* (A ⊗ B))` on the homotopy category of complexes of module
objects over `Λ_Y`, of which both sides of the comparison are left derived bifunctors. -/
noncomputable def upperStarTensorTarget :
    HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) (ComplexShape.up ℤ) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj
    ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)

/-- The transformation `Qh (f^* A) ⊗ᴸ Qh (f^* B) ⟶ Qh (f^* (A ⊗ B))` of bifunctors on the
homotopy category of `Mod_{Λ_Y}`: the lax structure of `Qh` followed by `Qh` of the comparison
`upperStarTensorComplexHom`. -/
noncomputable def upperStarTensorCounit :
    (((whiskeringLeft₂ _).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        ((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)).obj
        (curriedTensor _) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := Functor.LaxMonoidal.μ DerivedCategory.Qh
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).obj B) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))
      naturality B B' ψ := sorry }
  naturality A A' φ := sorry

/-! ### Derived categories -/

/-- The bifunctor `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorRight :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  (((whiskeringLeft₂ _).obj L((f)^*⟦Λ⟧)).obj L((f)^*⟦Λ⟧)).obj (curriedTensor _)

/-- The bifunctor `(K, L) ↦ Lf^* (K ⊗ᴸ L)` on `D(Mod_{Λ_Y})`. -/
noncomputable def leftDerivedUpperStarTensorLeft :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) ⥤
        DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X)) :=
  curriedTensor _ ⋙ (whiskeringRight _ _ _).obj L((f)^*⟦Λ⟧)

/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -`: the counits
`Qh ⋙ Lf^* ⟶ f^* ⋙ Qh` of the derived pullback in both variables, followed by
`upperStarTensorCounit`. -/
noncomputable def leftDerivedUpperStarTensorRightCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorRight Λ f) ⟶
      upperStarTensorTarget Λ f :=
  (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map (𝟙 _) ≫
    whiskeringLeft₂Equiv.symm
      (whiskeringLeft₂Equiv (𝟙 _) ≫ whiskerRight
        (NatTrans.prod (f)^*⟦Λ⟧.leftDerivedFunctorCounit (f)^*⟦Λ⟧.leftDerivedFunctorCounit)
          (uncurry.obj (curriedTensor _)) ≫ whiskeringLeft₂Equiv (upperStarTensorCounit Λ f))

/-- The bifunctor `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor of `(A, B) ↦ Qh (f^* (A ⊗ B))`,
for the counit `leftDerivedUpperStarTensorRightCounit`. See the module docstring. -/
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  sorry

/-- The counit of the bifunctor `Lf^* (- ⊗ᴸ -)`: `Lf^*` of the lax structure
`Qh A ⊗ᴸ Qh B ⟶ Qh (A ⊗ B)` of the localization, followed by the counit
`Lf^* (Qh (A ⊗ B)) ⟶ Qh (f^* (A ⊗ B))` of the derived pullback. -/
noncomputable def leftDerivedUpperStarTensorLeftCounit :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).obj
        (leftDerivedUpperStarTensorLeft Λ f) ⟶
      upperStarTensorTarget Λ f where
  app A :=
    { app B := L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B)
      naturality B B' ψ := sorry }
  naturality A A' φ := sorry

/-- The comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback with the
derived tensor product, as a natural transformation of bifunctors on `D(Mod_{Λ_Y})`: the
morphism to the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -` induced by the counit
`leftDerivedUpperStarTensorLeftCounit` (`Functor.leftDerived₂Lift`). -/
noncomputable def leftDerivedUpperStarTensor :
    leftDerivedUpperStarTensorLeft Λ f ⟶ leftDerivedUpperStarTensorRight Λ f :=
  (leftDerivedUpperStarTensorRight Λ f).leftDerived₂Lift
    (leftDerivedUpperStarTensorRightCounit Λ f)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (leftDerivedUpperStarTensorLeft Λ f) (leftDerivedUpperStarTensorLeftCounit Λ f)

/-- The comparison `m` is compatible with the counits. -/
lemma leftDerivedUpperStarTensor_fac :
    (((whiskeringLeft₂ _).obj DerivedCategory.Qh).obj DerivedCategory.Qh).map
        (leftDerivedUpperStarTensor Λ f) ≫ leftDerivedUpperStarTensorRightCounit Λ f =
      leftDerivedUpperStarTensorLeftCounit Λ f :=
  Functor.leftDerived₂_fac _ _ _ _ _ _

/-- The comparison `m : Lf^* (- ⊗ᴸ -) ⟶ Lf^* - ⊗ᴸ Lf^* -` is an isomorphism. See the module
docstring. -/
instance isIso_leftDerivedUpperStarTensor : IsIso (leftDerivedUpperStarTensor Λ f) :=
  sorry

/-- The comparison isomorphism `m_{K,L} : Lf^* (K ⊗ᴸ L) ≅ Lf^* K ⊗ᴸ Lf^* L` of the derived
pullback with the derived tensor product. -/
noncomputable def leftDerivedUpperStarTensorIso :
    leftDerivedUpperStarTensorLeft Λ f ≅ leftDerivedUpperStarTensorRight Λ f :=
  asIso (leftDerivedUpperStarTensor Λ f)

/-! ### The monoidal structure -/

/-- The derived pullback of the tensor unit `Λ_Y` is the tensor unit `Λ_X`: the counit
`Lf^* (Qh 𝟙) ≅ Qh (f^* 𝟙)` of the derived pullback of the exact functor `f^*`, followed by the
unit comparison `f^* 𝟙 ≅ 𝟙` of the strong monoidal pullback of module objects, in degree `0`. -/
noncomputable def leftDerivedUpperStarUnitIso :
    L((f)^*⟦Λ⟧).obj (𝟙_ _) ≅ 𝟙_ _ :=
  asIso ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (𝟙_ _)) ≪≫
    DerivedCategory.Qh.mapIso
      (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app (𝟙_ _) ≪≫
        (HomotopyCategory.quotient _ _).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex (f)^*⟦Λ⟧
              (ComplexShape.up ℤ) 0).app (𝟙_ _) ≪≫
            (HomologicalComplex.single _ _ 0).mapIso (Functor.Monoidal.εIso (f)^*⟦Λ⟧).symm))

/-- The derived pullback `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` on module objects over `Λ` is
strong monoidal for the derived tensor products, with tensorator the inverse of
`leftDerivedUpperStarTensorIso` and unit comparison `leftDerivedUpperStarUnitIso`. -/
noncomputable instance monoidal_leftDerivedUpperStar : L((f)^*⟦Λ⟧).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := (leftDerivedUpperStarUnitIso Λ f).symm
      μIso K L := (((leftDerivedUpperStarTensorIso Λ f).app K).app L).symm
      μIso_hom_natural_left φ L :=
        NatTrans.congr_app ((leftDerivedUpperStarTensorIso Λ f).inv.naturality φ) L
      μIso_hom_natural_right K ψ :=
        ((leftDerivedUpperStarTensorIso Λ f).inv.app K).naturality ψ
      associativity := sorry
      left_unitality := sorry
      right_unitality := sorry }

end AlgebraicGeometry.ProEtale.CondensedRing
