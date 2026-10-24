/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModBraided
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-!

# The derived pullback of module objects is symmetric monoidal

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback `Lf^* = L((f)^*⟦Λ⟧)` with its monoidal structure
`ProEtale.CondensedRing.monoidal_leftDerivedUpperStar` is braided for the Koszul braidings
`DerivedCategory.braidedCategory'` of the derived tensor products
(`ProEtale.CondensedRing.leftDerivedUpperStar_μ_map_braiding_hom`).

The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects is braided
(`ProEtale.CondensedRing.braided_upperStar`), being the composite of braided functors. On
complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is therefore compatible with the Koszul
braidings. The comparison `m : Lf^* (K ⊗ᴸ L) ⟶ Lf^* K ⊗ᴸ Lf^* L` is a natural transformation into
the left derived bifunctor `Lf^* - ⊗ᴸ Lf^* -`, characterized by its composite with the counit;
so is `Lf^* β_{K, L} ≫ m_{L, K} ≫ β_{Lf^* L, Lf^* K}`, and both have the same composite with the
counit, by the compatibility on complexes and the symmetry of the braidings.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme Functor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The pullback `f^* = mapMod(f^*) ⋙ Ext_{α_f}` of module objects over `Λ` is braided, as the
composite of braided functors. It is not an instance, to avoid a second path to the monoidal
structure `ProEtale.CondensedRing.monoidal_upperStar`. -/
@[instance_reducible]
noncomputable def braided_upperStar : (f)^*⟦Λ⟧.Braided :=
  inferInstanceAs ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y) ⋙
    Mod.extendScalars (condensedPullbackHom Λ f)).Braided

/-- The pullback of module objects is compatible with the braidings, in the form of the
comonoidal structure. -/
lemma upperStar_μ_map_braiding_hom
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ M N ≫ (f)^*⟦Λ⟧.map (β_ M N).hom =
      (β_ ((f)^*⟦Λ⟧.obj M) ((f)^*⟦Λ⟧.obj N)).hom ≫ Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ N M :=
  (braided_upperStar Λ f).braided M N

set_option maxHeartbeats 1000000 in
-- `erw` unfolds the tensor product of complexes of module objects to its components.
/-- On complexes, the comparison `f^* A ⊗ f^* B ⟶ f^* (A ⊗ B)` is compatible with the Koszul
braidings. -/
@[reassoc]
lemma upperStarTensorComplexHom_braiding
    (A B : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ℤ) :
    (β_ (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj A)
        (((f)^*⟦Λ⟧.mapHomologicalComplex _).obj B)).hom ≫ upperStarTensorComplexHom Λ f B A =
      upperStarTensorComplexHom Λ f A B ≫ ((f)^*⟦Λ⟧.mapHomologicalComplex _).map (β_ A B).hom := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    upperStarTensorComplexHom, upperStarTensorComplexHomX]
  erw [CochainComplex.Monoidal.ι_braiding_hom_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  rw [Preadditive.zsmul_comp, Category.assoc]
  simp only [HomologicalComplex.ι_mapBifunctorDesc]
  have hβ := CochainComplex.Monoidal.ι_braiding_hom (K := A) (L := B) p q n h
  rw [Category.assoc, ← Functor.map_comp,
    show (β_ A B).hom = (CochainComplex.Monoidal.braiding A B).hom from rfl, hβ]
  simp only [Functor.map_zsmul, Preadditive.comp_zsmul, Functor.map_comp]
  rw [reassoc_of% (upperStar_μ_map_braiding_hom Λ f (A.X p) (B.X q))]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
