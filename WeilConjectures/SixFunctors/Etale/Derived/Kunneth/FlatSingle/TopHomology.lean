/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.TensorSingle

/-!
# The top homology sheaf of a derived tensor product with a sheaf

For a sheaf `B` on `X_ét` placed in degree `0` and an object `M` of `D(X_ét)` concentrated in
degrees `≤ q`, the top homology sheaf of the derived tensor product is the underived tensor
product with the top homology sheaf: `Hᵠ(B[0] ⊗ᴸ M) ≅ B ⊗ Hᵠ(M)`, naturally in `B`
(`AlgebraicGeometry.Etale.singleFunctorTensorRightHomologyIso`). Indeed `M ⟶ τ^{≥q} M` induces an
isomorphism on `Hᵠ(B[0] ⊗ᴸ -)` (the fibre `τ^{≤q-1} M` gives objects in degrees `≤ q - 1`),
`τ^{≥q} M ≅ Hᵠ(M)[-q]`, and `H⁰(B[0] ⊗ᴸ C[0]) ≅ B ⊗ C`
(`AlgebraicGeometry.Etale.isIso_homologyFunctor_map_singleFunctorTensorToSingle_app`).
This is used in the proof of blueprint `lem-kun-0f1j`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The top homology of a derived tensor product with a sheaf: for `M` concentrated in degrees
`≤ q`, `Hᵠ(B[0] ⊗ᴸ M) ≅ B ⊗ Hᵠ(M)`, naturally in the sheaf `B`. -/
noncomputable def singleFunctorTensorRightHomologyIso
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (q : ℤ) [M.IsLE q] :
    DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology A) 0 ⋙ tensorRight M ⋙
        DerivedCategory.homologyFunctor _ q ≅
      tensorRight ((DerivedCategory.homologyFunctor _ q).obj M) :=
  sorry

end Etale

end AlgebraicGeometry
