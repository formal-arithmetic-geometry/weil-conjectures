/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.Monoidal.KFlatEquivalence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

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

/-! ### K-flatness of pullbacks -/

set_option synthInstance.maxHeartbeats 400000 in
-- the generic search goes through the colimits of `Mod (Sheaf (ProEt.topology Z) Ab) _`
/-- The K-flat complexes of module objects over `Λ_Z` form a left derivability structure for the
quasi-isomorphisms of the homotopy category. -/
instance isLeftDerivabilityStructure_localizerMorphismKFlat (Z : Scheme.{u}) :
    (HomotopyCategory.quasiIso
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
      (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure := by
  have (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have h₁ : HasColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₂ : HasExactColimitsOfShape ℤ
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₃ (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) :
      PreservesColimitsOfShape ℤ ((curriedTensor _).obj M) := inferInstance
  have h₄ : Abelian.HasFunctorialFlatResolution
    (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)) := inferInstance
  have h₅ (X₁ X₂ X₃ X₄ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
  have h₆ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
  have h₇ (X₁ X₂ X₃ : GradedObject ℤ
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
  infer_instance

/-- The extension of scalars along the isomorphism `α_f : f^* Λ_Y ⟶ Λ_X` is an equivalence. -/
instance isEquivalence_extendScalars_condensedPullbackHom :
    (Mod.extendScalars (condensedPullbackHom Λ f)).IsEquivalence :=
  have : (Mod.comap (asIso (condensedPullbackHom Λ f)).inv).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (condensedPullbackHom Λ f)).symm.isEquivalence_functor
  Functor.isEquivalence_of_iso (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).symm

/-- The pullback of module objects preserves K-flat complexes. -/
lemma kFlat_upperStar_mapHomologicalComplex_obj
    {P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧).mapHomologicalComplex (.up ℤ) |>.obj P) :=
  ObjectProperty.prop_of_iso _
    ((Functor.mapHomologicalComplexCompIso (Iso.refl ((f)^*⟦Λ⟧)) (.up ℤ)).app P)
    ((Mod.extendScalars (condensedPullbackHom Λ f)).kFlat_mapHomologicalComplex_obj_of_isEquivalence
      (((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).kFlat_mapHomologicalComplex_obj P hP))

/-- The pullback of module objects preserves K-flat objects of the homotopy category. -/
lemma kFlat_upperStar_mapHomotopyCategory_obj
    {R : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ℤ}
    (hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj R)) :=
  ObjectProperty.prop_of_iso _ (((f)^*⟦Λ⟧.mapHomotopyCategoryFactors (.up ℤ)).app R).symm
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2
      (kFlat_upperStar_mapHomologicalComplex_obj Λ f hR))

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

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The degreewise comparison `upperStarTensorComplexHomX` is a section of the comparison
`f^* ((A ⊗ B)^n) ⟶ (f^* A ⊗ f^* B)^n` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHomX_comp_mapBifunctorComparisonX
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) (n : ℤ) :
    upperStarTensorComplexHomX Λ f A B n ≫
      (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B).f n =
      𝟙 _ := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  dsimp only [upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Category.comp_id]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
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
  have hc := HomologicalComplex.Hom.comm
    (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
      (.up ℤ) A B) n n'
  have hX := upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B
  simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app] at hX
  rw [← cancel_mono ((HomologicalComplex.mapBifunctorComparison
      (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) A B).f n'), Category.assoc,
    Category.assoc,
    hX, Category.comp_id]
  exact (congrArg (upperStarTensorComplexHomX Λ f A B n ≫ ·) hc).symm.trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (hX n)).trans (Category.id_comp _)))

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

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `upperStarTensorComplexHom` is the inverse of the comparison
`f^* (A ⊗ B) ⟶ f^* A ⊗ f^* B` induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_eq_inv
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B =
      inv (HomologicalComplex.mapBifunctorComparison (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧)
        (.up ℤ) A B) := by
  refine (IsIso.inv_eq_of_inv_hom_id (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)).symm
  exact upperStarTensorComplexHomX_comp_mapBifunctorComparisonX Λ f A B n

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `upperStarTensorComplexHom` is natural in both complexes. -/
lemma upperStarTensorComplexHom_naturality
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) ≫
        upperStarTensorComplexHom Λ f A' B' =
      upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ) := by
  rw [upperStarTensorComplexHom_eq_inv, upperStarTensorComplexHom_eq_inv, IsIso.comp_inv_eq,
    Category.assoc, IsIso.eq_inv_comp]
  exact (HomologicalComplex.mapBifunctorComparison_naturality
    (Functor.OplaxMonoidal.δNatTrans (f)^*⟦Λ⟧) (.up ℤ) φ ψ).symm

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

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The naturality square of the components of `upperStarTensorCounit`, on complexes. -/
lemma upperStarTensorCounit_naturality_aux
    {A A' B B' : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ}
    (φ : A ⟶ A') (ψ : B ⟶ B') :
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)) ⊗ₘ
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ))) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A'))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B')) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A' B')) =
    Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj A))
        ((HomotopyCategory.quotient _ _).obj
          (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).obj B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (upperStarTensorComplexHom Λ f A B)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map (φ ⊗ₘ ψ))) := by
  have key : ((HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) ⊗ₘ
      (HomotopyCategory.quotient _ _).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ⊗ₘ
          ((f)^*⟦Λ⟧.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := by
    rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def, Functor.map_comp]
    rfl
  rw [Functor.LaxMonoidal.μ_natural_assoc, key, ← DerivedCategory.Qh.map_comp,
    ← Functor.map_comp, upperStarTensorComplexHom_naturality, Functor.map_comp,
    DerivedCategory.Qh.map_comp]

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
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
      naturality B B' ψ := by
        obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
        obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
        obtain ⟨B', rfl⟩ := B'.quotient_obj_surjective
        obtain ⟨ψ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective ψ
        have h := upperStarTensorCounit_naturality_aux Λ f (𝟙 A) ψ
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.id_tensorHom,
          MonoidalCategory.id_tensorHom] at h
        rw [Category.assoc]
        exact h }
  naturality A A' φ := by
    ext B
    obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
    obtain ⟨A', rfl⟩ := A'.quotient_obj_surjective
    obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
    obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective φ
    have h := upperStarTensorCounit_naturality_aux Λ f φ (𝟙 B)
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at h
    rw [NatTrans.comp_app, NatTrans.comp_app, Category.assoc]
    exact h

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

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The comparison `f^* A ⊗ f^* B ⟶ f^*(A ⊗ B)` of complexes is a section of the comparison
induced by the comonoidal structure of `f^*`. -/
lemma upperStarTensorComplexHom_δ
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (f)^*⟦Λ⟧).app A).app B =
      𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i₁ i₂ h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, 
    Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
    HomologicalComplex.mapBifunctorComparison_f]
  dsimp only [upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [Category.comp_id]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open DerivedCategory in
/-- The counit of the bifunctor `Lf^* - ⊗ᴸ Lf^* -` on objects of the homotopy category. -/
lemma leftDerivedUpperStarTensorRightCounit_app_app (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B) ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map (upperStarTensorComplexHom Λ f A.as B.as)) := by
  dsimp only [leftDerivedUpperStarTensorRightCounit, NatTrans.comp_app]
  erw [Category.id_comp]
  refine (?_ : _ = 𝟙 _ ≫ (((f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B)) ≫
        (Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B)) ≫
        (Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as)))).trans ?_
  · rfl
  · exact (Category.id_comp _).trans (Category.assoc _ _ _)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
/-- The bifunctor `Lf^* - ⊗ᴸ Lf^* -` is a left derived bifunctor of `(A, B) ↦ Qh (f^* (A ⊗ B))`,
for the counit `leftDerivedUpperStarTensorRightCounit`. See the module docstring. -/
instance isLeftDerivedFunctor₂_upperStarTensor :
    (leftDerivedUpperStarTensorRight Λ f).IsLeftDerivedFunctor₂
      (leftDerivedUpperStarTensorRightCounit Λ f)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor₂_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ (fun X₁ X₂ ↦ ?_)
  obtain ⟨A, hA⟩ := X₁
  obtain ⟨B, hB⟩ := X₂
  obtain ⟨A, rfl⟩ := A.quotient_obj_surjective
  obtain ⟨B, rfl⟩ := B.quotient_obj_surjective
  have hB' := (HomotopyCategory.kFlat_quotient_obj_iff B).1 hB
  change IsIso (((leftDerivedUpperStarTensorRightCounit Λ f).app
    ((HomotopyCategory.quotient _ _).obj A)).app ((HomotopyCategory.quotient _ _).obj B))
  rw [leftDerivedUpperStarTensorRightCounit_app_app]
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hA
  have := (f)^*⟦Λ⟧.isIso_leftDerivedFunctorCounit_app_of_kFlat' _ hB
  have h₃ : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj A))
      (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj B))) :=
    isIso_μNatTrans_Qh_app_app_of_kFlat _ _ (kFlat_upperStar_mapHomotopyCategory_obj Λ f hB')
  have h₄ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A B))) := by
    rw [upperStarTensorComplexHom_eq_inv]
    infer_instance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h₃ h₄))

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
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
      naturality B B' ψ := by
        have h₁ := Functor.LaxMonoidal.μ_natural_right DerivedCategory.Qh A ψ
        have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (A ◁ ψ)
        dsimp only [Functor.comp_map] at h₂
        change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.obj A ◁ DerivedCategory.Qh.map ψ) ≫
            L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B') ≫ _ =
          (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
            DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (A ◁ ψ))
        rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂] }
  naturality A A' φ := by
    ext B
    have h₁ := Functor.LaxMonoidal.μ_natural_left DerivedCategory.Qh φ B
    have h₂ := (f)^*⟦Λ⟧.leftDerivedFunctorCounit.naturality (φ ▷ B)
    dsimp only [Functor.comp_map] at h₂
    change L((f)^*⟦Λ⟧).map (DerivedCategory.Qh.map φ ▷ DerivedCategory.Qh.obj B) ≫
        L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A' B) ≫ _ =
      (L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ DerivedCategory.Qh A B) ≫ _) ≫
        DerivedCategory.Qh.map (((f)^*⟦Λ⟧.mapHomotopyCategory (ComplexShape.up ℤ)).map (φ ▷ B))
    rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc, h₂]

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

set_option maxHeartbeats 1600000 in
-- the instances on complexes of module objects make the elaboration slow
open DerivedCategory in
/-- The defining property of the tensor comparison of `Lf^*`, in the form used by
`DerivedCategory.commShift_of_tensorLeft_fac`. -/
lemma leftDerivedUpperStarTensor_app_app_fac (A B : HomotopyCategory
    (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) (ComplexShape.up ℤ)) :
    ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) =
      L((f)^*⟦Λ⟧).map (Functor.LaxMonoidal.μ Qh A B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app (A ⊗ B) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
  have h : ((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
      ((leftDerivedUpperStarTensorRightCounit Λ f).app A).app B =
      ((leftDerivedUpperStarTensorLeftCounit Λ f).app A).app B :=
    congr_app (congr_app (leftDerivedUpperStarTensor_fac Λ f) A) B
  rw [leftDerivedUpperStarTensorRightCounit_app_app] at h
  have hδ : Qh.map ((HomotopyCategory.quotient _ _).map
      (upperStarTensorComplexHom Λ f A.as B.as)) ≫
      Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) = 𝟙 _ := by
    rw [← Functor.map_comp]
    erw [Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app]
    rw [← Functor.map_comp, upperStarTensorComplexHom_δ]
    exact (congrArg Qh.map ((HomotopyCategory.quotient _ _).map_id _)).trans (Qh.map_id _)
  calc _ = (((leftDerivedUpperStarTensor Λ f).app (Qh.obj A)).app (Qh.obj B) ≫
        (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app A ▷ L((f)^*⟦Λ⟧).obj (Qh.obj B) ≫
        Qh.obj (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A) ◁
          (f)^*⟦Λ⟧.leftDerivedFunctorCounit.app B ≫
        Functor.LaxMonoidal.μ Qh (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj A)
          (((f)^*⟦Λ⟧.mapHomotopyCategory (.up ℤ)).obj B) ≫
        Qh.map ((HomotopyCategory.quotient _ _).map
          (upperStarTensorComplexHom Λ f A.as B.as))) ≫
        Qh.map (((Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans (.up ℤ)
          (f)^*⟦Λ⟧).app A).app B) := by
        simp only [Category.assoc]
        erw [hδ, Category.comp_id]
    _ = _ := by
        erw [h]
        exact Category.assoc _ _ _


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
