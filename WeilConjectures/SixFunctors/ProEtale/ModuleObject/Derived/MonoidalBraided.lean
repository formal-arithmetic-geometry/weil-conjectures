/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.BraidedModule

/-!

# The derived pullback of module objects is braided

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The tensor
comparison `m_{K,L} : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` of the derived pullback of module objects
is compatible with the Koszul braidings `DerivedCategory.braidedCategory'` of the derived tensor
products (`ProEtale.CondensedRing.leftDerivedUpperStarTensor_braiding`).

Both sides of the identity are natural transformations between the bifunctors
`(K, L) ↦ Lf^* (K ⊗ᴸ L)` and `(K, L) ↦ Lf^* K ⊗ᴸ Lf^* L`, the latter a left derived bifunctor,
so it suffices to compare them on complexes. There the identity follows from the compatibility
of the underived pullback `f^*` of module objects with the symmetries
(`ProEtale.CondensedRing.laxBraided_upperStar`), extended to complexes with the Koszul sign rule
(`ProEtale.CondensedRing.upperStarTensorComplexHom_braiding`), and from the characterisation of
the braiding of the derived tensor product by its compatibility with the localization
(`DerivedMonoidal.braiding_hom_μ`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the Koszul
braidings. -/
@[reassoc]
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    upperStarTensorComplexHom Λ f A B ≫
        ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (β_ A B).hom =
      (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫ upperStarTensorComplexHom Λ f B A := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Category.assoc, ← Functor.map_comp]
  have hβ : HomologicalComplex.ιTensorObj A B p q n h ≫ (β_ A B).hom.f n = _ :=
    CochainComplex.Monoidal.ι_braiding_hom (K := A) (L := B) p q n h
  have hβ' : HomologicalComplex.ιTensorObj (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
      (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B) p q n h ≫
        (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
          (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom.f n = _ :=
    CochainComplex.Monoidal.ι_braiding_hom (K := ((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
      (L := ((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B) p q n h
  rw [hβ]
  erw [reassoc_of% hβ']
  rw [Functor.map_zsmul, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc,
    Functor.map_comp]
  erw [HomologicalComplex.ι_mapBifunctorDesc]
  rw [LaxBraided.braided_assoc]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
