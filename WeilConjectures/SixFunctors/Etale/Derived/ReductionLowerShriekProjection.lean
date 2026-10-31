/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReduction
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapShift

/-!
# The derived extension of scalars as a tensor product
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Comparison

variable (X : Scheme.{u}) [(derivedExtendScalars hρ ha X).OplaxMonoidal]

/-- The comonoidal comparison `Ψ(b ⊗ᴸ a) ⟶ Ψ b ⊗ᴸ Ψ a` of the derived extension of scalars, as a
natural transformation between the flipped tensor bifunctors. -/
noncomputable def derivedExtendScalarsFlipComparison :
    (Functor.postcompose₂.obj (derivedExtendScalars hρ ha X)).obj (curriedTensor 𝐃(X, Λ)).flip ⟶
      (((Functor.whiskeringLeft₂ 𝐃(X, Λ')).obj (derivedExtendScalars hρ ha X)).obj
        (derivedExtendScalars hρ ha X)).obj (curriedTensor 𝐃(X, Λ')).flip :=
  { app A :=
      { app B := δ (derivedExtendScalars hρ ha X) B A
        naturality B B' f := by
          simpa using (δ_natural_left (derivedExtendScalars hρ ha X) f A) }
    naturality A A' f := by
      ext B
      simpa using (δ_natural_right (derivedExtendScalars hρ ha X) B f) }

/-- The tensor product with `Res Λ'_X`, `K ⊗ᴸ Res Λ'_X ⟶ Res(Ψ K)`: the right adjoint projection
map of `Ψ ⊣ Res` at the unit `Λ'_X`, followed by the right unitor. -/
noncomputable def derivedExtendScalarsTensorMap (K : 𝐃(X, Λ)) :
    K ⊗ (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (𝟙_ 𝐃(X, Λ')) ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj
        ((derivedExtendScalars hρ ha X).obj K) :=
  ((((derivedExtendScalarsAdjunction hρ ha X).rightAdjointProjectionMap
      (derivedExtendScalarsFlipComparison hρ ha X)).app (𝟙_ _)).app K) ≫
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
      (ρ_ ((derivedExtendScalars hρ ha X).obj K)).hom

end Comparison

end AlgebraicGeometry.Etale
