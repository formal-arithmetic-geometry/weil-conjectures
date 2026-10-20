/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeEtaleFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# Site transport of the open projection formula
Source: Stacks Project, `proetale.tex`, Tag 09AF, `lemma-jshriek-comparison`,
combined with `sites-cohomology.tex`, Tag 0GL1, `lemma-j-shriek-and-tensor`.
The derived statement and its K-flat normalization follow the blueprint item
`lem-pur-open-projection-site-transport` (blueprint: lem-pur-open-projection-site-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private lemma flat_single_shift_tensor_plus
    {C : Type*} [Category C] [Abelian C] [MonoidalCategory C] [SymmetricCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [IsGrothendieckAbelian C]
    [Abelian.HasFunctorialFlatResolution C]
    (L : C) (hf : ObjectProperty.flat L) (m : ℤ)
    (H : DerivedCategory C) (hH : DerivedCategory.TStructure.t.plus H) :
    DerivedCategory.TStructure.t.plus
      (((DerivedCategory.singleFunctor C 0).obj L)⟦m⟧ ⊗ H) := by
  obtain ⟨n, hn⟩ := hH
  have : H.IsGE n := hn
  let S := (DerivedCategory.singleFunctor C 0).obj L
  have ht := DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hf
  have : (S ⊗ H).IsGE (0 + n) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeIn ht H n
  have hs : DerivedCategory.TStructure.t.plus ((S ⊗ H)⟦m⟧) :=
    ⟨0 + n - m,
      DerivedCategory.TStructure.t.isGE_shift _ (0 + n) m (0 + n - m) (by omega)⟩
  exact DerivedCategory.TStructure.t.plus.prop_of_iso
    (((CategoryTheory.MonoidalCategory.tensorRight H).commShiftIso m).app S).symm hs

private lemma source_plus_of_flat
    (A : Type*) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (L : Sheaf U.smallEtaleTopology A) (hf : ObjectProperty.flat L) (m : ℤ)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek A j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar A j).obj
          (((DerivedCategory.singleFunctor (Sheaf U.smallEtaleTopology A) 0).obj L)⟦m⟧)).obj
            (DerivedCategory.Plus.ι.obj G))) := by
  let B := DerivedCategory.Plus.ι.obj G
  let H := (Etale.upperStar A j).leftDerivedFunctor.obj B
  let S := (DerivedCategory.singleFunctor
    (Sheaf U.smallEtaleTopology A) 0).obj L
  have hH : DerivedCategory.TStructure.t.plus H :=
    DerivedCategory.TStructure.t.plus.prop_of_iso
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory
        A j).app B).symm
      (((Etale.upperStar A j).mapDerivedCategoryPlus.obj G).property)
  have hsource := flat_single_shift_tensor_plus L
    hf m H hH
  obtain ⟨n, hn⟩ := hsource
  have : (S⟦m⟧ ⊗ H).IsGE n := hn
  exact ⟨n, (Etale.openImmersionLowerShriek
    A j).isGE_mapDerivedCategory_obj (S⟦m⟧ ⊗ H) n⟩

/-- Boundedness of the source of the transported open projection. Source: Stacks Project,
Tags 09AF and 0GL1; finite locally free tensor boundedness and exact open extension.

Proof: Local freeness makes L a flat object by the fixed-coefficient realization
flatness bridge. Its degree-zero single complex has Tor amplitude [0,0]. Exact inverse
image preserves the lower bound on G. The tensor lower-bound lemma therefore bounds
the tensor with the single complex; the shift changes the bound by -m. Finally exact
open extension preserves the resulting bound. No bound or flatness is required over
any smaller coefficient ring, and rank zero gives the zero tensor.
(blueprint: lem-pur-open-projection-source-plus). -/
theorem openProjectionTransport_source_plus
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (t : ℕ)
    (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u + 1, u, u + 1}
      (R := finiteCoefficientEtaleRingSheaf U Λ)
      ((finiteCoefficientEtaleRealization U Λ).obj L) t) (m : ℤ)
    (G : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.TStructure.t.plus
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategory.obj
        (((Etale.derivedTensorWhiskeringRightLeftDerivedUpperStar
          (ModuleCat.{u + 1} Λ) j).obj
            (((DerivedCategory.singleFunctor
              (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj L)⟦m⟧)).obj
                (DerivedCategory.Plus.ι.obj G))) := by
  exact source_plus_of_flat (ModuleCat.{u + 1} Λ) j L
    (flat_of_finiteCoefficientEtaleRealization_locallyFree Λ U L t hL) m G

end AlgebraicGeometry.ProEtale
