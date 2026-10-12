module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-! # Natural dual comparison for constant finite free sheaves -/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- Constant sheafification identifies the duals of finite free modules naturally.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring, finite free transpose step.

Proof: Write Λ^n as the finite biproduct of n copies of Λ. Constant sheafification
preserves this biproduct and identifies the constant coefficient module with the
monoidal unit. Internal Hom into the unit takes this finite biproduct to the
finite product of n copies of the unit, using the tensor-Hom adjunction and the
unit constraints. The dual basis identifies Hom(Λ^n, Λ) with that same product.
Compose these comparisons to obtain e_n. For a matrix g, precomposition on
internal Hom sends a functional with coordinates a_i to the coordinates
sum_i g_ij a_i: evaluate on each basis vector and use linearity. The coefficient
dual map has exactly the same coordinates, so its constant sheaf map commutes
with e_n and e_m. Equality is detected by the finite product projections.
For n = 0 or m = 0 these are empty products and the same equations hold;
no noetherian hypothesis or assertion about an infinite product is used.
(blueprint: lem-constant-finite-free-dual-naturality) -/
theorem constantFiniteFreeDualNaturality
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] :
    ∃ e : ∀ n : ℕ,
      (MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).obj
          (Opposite.op ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ)))) ≅
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ ((Fin n → Λ) →ₗ[Λ] Λ)),
      ∀ (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)),
        ((MonoidalClosed.internalHom.flip.obj
          (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom g)).op) ≫ (e m).hom =
          (e n).hom ≫
            (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom g.dualMap) := by sorry

end AlgebraicGeometry.Scheme
