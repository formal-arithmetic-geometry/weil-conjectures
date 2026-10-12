/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-! # Dual of a finite constant module sheaf

Source: the finite presentation argument in the docstring of
`WeilConjectures/ConstructibleSheaf/Monoidal.lean`, `IsFiniteLocallyConstantSheaf.ihom_unit`.
(blueprint: lem-weil-pbc-constant-module-dual)
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme

/-- Over a noetherian coefficient ring, dualizing a constant sheaf with a finite module
value produces the constant sheaf with the module dual as value.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit`, finite presentation argument.

Proof: Since Λ is noetherian, the finite module M has a finite presentation
Λᵐ → Λⁿ → M → 0. The constant sheaf functor is exact and monoidal, so it carries
this to a presentation by finite free coefficient sheaves. Applying internal Hom
into the unit gives the kernel of the transposed map between the finite free duals.
Those duals are again the constant finite free sheaves, and the transposed map is
the constant sheafification of the module transpose. Constant sheafification
preserves kernels. In modules the kernel of this transpose is Hom_Λ(M, Λ), by
applying Hom_Λ(-, Λ) to the presentation. Composing these kernel isomorphisms gives
the claimed isomorphism. No projectivity of M is assumed; for M = 0 the same
argument uses a zero presentation, and the empty scheme causes no exception.
(blueprint: lem-weil-pbc-constant-module-dual) -/
theorem nonempty_constantModuleDualIso
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    Nonempty ((ihom ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj
      (𝟙_ _) ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (M →ₗ[Λ] Λ))) := by
  sorry

end AlgebraicGeometry.Scheme
