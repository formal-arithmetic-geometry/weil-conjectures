/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, an invertible tensor factor passes through `Ri^!` at the
cost of restricting it: `Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L` (blueprint `sk-lem-coprojection`).
This is the input that moves twists through the exceptional inverse image of a zero section in
the model purity (`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`) and in purity
for regular closed immersions (`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekDerivedTensorIsoOfTensorInverse`: co-projection
  for a general coefficient category.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Z : Scheme.{u}}

/-- Co-projection for a closed immersion `i : Z ⟶ X`, for a general coefficient category `A`:
if `L` has a two-sided tensor inverse `M`, then `Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L`. Here
`Ri^!` is right adjoint to `Ri_! ≅ Ri_*`, which is right adjoint to the monoidal functor `Li^*`,
so this is `CategoryTheory.tensorRightCompIsoOfTensorInverse`. -/
noncomputable def rightDerivedUpperShriekDerivedTensorIsoOfTensorInverse (i : Z ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] [(R(i)_![A]).IsLeftAdjoint]
    [(i)^*[A].PreservesFlat] (K L M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (e₁ : ((derivedTensor A X).obj L).obj M ≅ 𝟙_ _)
    (e₂ : ((derivedTensor A X).obj M).obj L ≅ 𝟙_ _) :
    (R(i)^![A]).obj (((derivedTensor A X).obj K).obj L) ≅
      ((derivedTensor A Z).obj ((R(i)^![A]).obj K)).obj ((L((i)^*[A])).obj L) :=
  (tensorRightCompIsoOfTensorInverse (derivedUpperStarLowerStarAdjunction A i)
    ((rightDerivedUpperShriekAdjunction A i).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar A i))
    (leftDerivedUpperStarTensorNatIso A i) (leftDerivedUpperStarUnitIso A i) e₁ e₂).app K

end General

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Z : Scheme.{u}}

omit [HasTateTwist Λ] in
/-- Blueprint `sk-lem-coprojection`: Co-projection for a closed immersion

For a closed immersion `i : Z ⟶ X`, a complex `K ∈ D^b_{ctf}(X, Λ)` and an object `L` of
`D^b_{ctf}(X, Λ)` that is *invertible*, the canonical co-projection

`Ri^! (K ⊗^L L) ≅ Ri^! K ⊗^L Li^* L`

is an isomorphism: an invertible tensor factor passes through `i^!` at the cost of restricting
it. Testing against an arbitrary `A ∈ D^b_{ctf}(Z, Λ)` and using `Ri_! = Ri_*`, the projection
formula for `Ri_*` and invertibility of `L`, the two Hom-functors agree naturally in `A`, so
Yoneda gives the isomorphism.

Taking `L = Λ_X(m)[2m]`, whose restriction is `Λ_Z(m)[2m]`, this reads
`Ri^!(K(m)[2m]) ≅ (Ri^! K)(m)[2m]`; taking `L = Lf^* B` for `B` invertible on `Y` and
`f' = f ∘ i` it reads `Ri^!(K ⊗ Lf^* B) ≅ Ri^! K ⊗ Lf'^* B`. -/
theorem nonempty_iso_rightDerivedUpperShriek_derivedTensor_of_isInvertible
    (i : Z ⟶ X) [IsClosedImmersion i] [HasCompactification i]
    (K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (_hLctf : DerivedCategory.boundedConstructibleFiniteTor Λ X L)
    (hL : DerivedCategory.isInvertible Λ X L) :
    Nonempty ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj
        (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj L) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) Z).obj
          ((rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) i).obj K)).obj
        ((L((i)^*[ModuleCat.{u + 1} Λ])).obj L)) := by
  obtain ⟨M, ⟨e₁⟩, ⟨e₂⟩⟩ := hL
  exact ⟨rightDerivedUpperShriekDerivedTensorIsoOfTensorInverse (ModuleCat.{u + 1} Λ) i K L M e₁ e₂⟩

end Etale

end AlgebraicGeometry
