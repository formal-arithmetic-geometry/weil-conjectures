/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.Abelian.Flat.Biproduct
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-!
# Isomorphisms and finite biproducts of flat sheaves of modules

Over an essentially small site, flatness on the site (`SheafOfModules.IsFlatOnSite`) is
categorical flatness for the tensor product of module sheaves. Hence it is invariant under
isomorphisms and stable under finite biproducts.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{w}}

set_option hygiene false in
local notation "𝒜" => SheafOfModules.{w}
  ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)

/-- Over an essentially small site, flatness on the site is categorical flatness for the
tensor product of module sheaves.

Proof: `siteSheafTensorRightIso` identifies the site tensor functor with `tensorRight`, and
the braiding identifies `tensorRight` with `tensorLeft`. -/
theorem isFlatOnSite_iff_flat (M : 𝒜) :
    IsFlatOnSite (J := J) (R := R) M ↔
      letI := isMonoidal_W_independentCoefficients R
      letI := monoidalCategory R
      ObjectProperty.flat M := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  exact ⟨flat_to_cat R M, fun h ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M).symm h.2⟩

/-- Flatness on the site is invariant under isomorphisms of module sheaves. -/
theorem IsFlatOnSite.of_iso {M N : 𝒜} (e : M ≅ N) (hM : IsFlatOnSite (J := J) (R := R) M) :
    IsFlatOnSite (J := J) (R := R) N := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  rw [isFlatOnSite_iff_flat] at hM ⊢
  exact ObjectProperty.prop_of_iso _ e hM

/-- A finite biproduct of module sheaves which are flat on the site is flat on the site.

Proof: transfer to categorical flatness, where tensoring is additive in each variable
(`tensorPreadditive`), and apply `ObjectProperty.flat_biproduct`. -/
theorem isFlatOnSite_biproduct [HasFiniteBiproducts 𝒜] {I : Type} [Finite I] (f : I → 𝒜)
    (hf : ∀ i, IsFlatOnSite (J := J) (R := R) (f i)) :
    IsFlatOnSite (J := J) (R := R) (⨁ f) := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := tensorPreadditive R
  rw [isFlatOnSite_iff_flat]
  exact ObjectProperty.flat_biproduct f fun i ↦ (isFlatOnSite_iff_flat (f i)).1 (hf i)

end SheafOfModules
