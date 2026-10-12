/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.MapBraided
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraidedQh
public import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquareBraided
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Braided

/-!
# The derived pullback is braided

For a morphism of schemes `g : Z ⟶ Y`, the derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)`, with its
monoidal structure `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`, is a braided monoidal
functor for the braidings `DerivedCategory.braidedCategory` of the derived tensor products (the
braidings of the sheaf categories with the Koszul sign rule, descended along K-flat resolutions).

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_braiding_comp_tensorComparison`: the tensor
  comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` is compatible with the braidings.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarBraided`: `Lg^*` is a braided monoidal functor.

The compatibility is checked on complexes whose pullback is K-flat
(`CategoryTheory.Functor.OplaxMonoidal.map_braiding_comp_app_app_of_lax_square`), where it
reduces to the braidedness of `g^*` on homotopy categories
(`CategoryTheory.Functor.mapHomotopyCategory_δ_comp_braiding`), which follows from the
braidedness of the pullback of sheaves (`AlgebraicGeometry.Etale.braided_upperStar`).
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) [(g)^*[A].PreservesFlat]

open DerivedCategory Functor.OplaxMonoidal

attribute [local instance] isLeftDerivedFunctor₂_derivedTensor_leftDerivedUpperStar
  isLeftDerivedFunctor₂_leftDerivedUpperStar_derivedTensor

/-- The tensor comparison `Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` of the derived pullback is compatible
with the braidings `DerivedCategory.braidedCategory` of the derived tensor products. -/
lemma leftDerivedUpperStar_map_braiding_comp_tensorComparison
    (X X' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := DerivedCategory.braidedCategory (Sheaf Y.smallEtaleTopology A)
    letI := DerivedCategory.braidedCategory (Sheaf Z.smallEtaleTopology A)
    L((g)^*[A]).map (β_ X X').hom ≫ ((leftDerivedUpperStarTensorComparison A g).app X').app X =
      ((leftDerivedUpperStarTensorComparison A g).app X).app X' ≫
        (β_ (L((g)^*[A]).obj X) (L((g)^*[A]).obj X')).hom :=
  letI := DerivedCategory.braidedCategory (Sheaf Y.smallEtaleTopology A)
  letI := DerivedCategory.braidedCategory (Sheaf Z.smallEtaleTopology A)
  map_braiding_comp_app_app_of_lax_square (leftDerivedUpperStarTensorComparison A g)
    (fun a ↦ (g)^*[A].leftDerivedFunctorCounit.app a)
    (fun _ _ f ↦ (g)^*[A].leftDerivedFunctorCounit.naturality f)
    (leftDerivedUpperStarTensorComparison_app_app_comp A g) (braiding_hom_μ_Qh)
    (braiding_hom_μ_Qh) (fun a b ↦ ((g)^*[A].mapHomotopyCategory_δ_comp_braiding a b).symm)
    (kFlatUpperStar A g) (exists_kFlatUpperStar_iso A g)
    (fun x _ hb ↦ isIso_μNatTrans_Qh_app_app_of_kFlat x _ hb) X X'

/-- The derived pullback `Lg^* : D(Y_ét) ⥤ D(Z_ét)` is a braided monoidal functor for the
braidings `DerivedCategory.braidedCategory` of the derived tensor products (the braidings of the
sheaf categories with the Koszul sign rule, descended along K-flat resolutions). Its underlying
monoidal structure is `AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`. -/
@[instance_reducible]
noncomputable def leftDerivedUpperStarBraided :
    letI := DerivedCategory.braidedCategory (Sheaf Y.smallEtaleTopology A)
    letI := DerivedCategory.braidedCategory (Sheaf Z.smallEtaleTopology A)
    L((g)^*[A]).Braided :=
  letI := DerivedCategory.braidedCategory (Sheaf Y.smallEtaleTopology A)
  letI := DerivedCategory.braidedCategory (Sheaf Z.smallEtaleTopology A)
  letI := leftDerivedUpperStarMonoidal A g
  Functor.Braided.ofMapBraidingCompδ _
    (leftDerivedUpperStar_map_braiding_comp_tensorComparison A g)

example :
    letI := DerivedCategory.braidedCategory (Sheaf Y.smallEtaleTopology A)
    letI := DerivedCategory.braidedCategory (Sheaf Z.smallEtaleTopology A)
    (leftDerivedUpperStarBraided A g).toMonoidal = leftDerivedUpperStarMonoidal A g :=
  rfl

end Etale

end AlgebraicGeometry
