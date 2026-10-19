module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.TraceFormula.WeakRelativeNoetherNormalization

/-!
# Local quasi-finite projection with bounded relative dimension

Source: Orgogozo, *Modifications et cycles proches sur une base générale*,
Proposition 2.3, proof, printed p. 4 (blueprint: lem-trf-local-quasi-finite-projection).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AlgebraicGeometry
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Orgogozo, *Modifications et cycles proches sur une base générale*,
Proposition 2.3, proof, printed p. 4 (blueprint: lem-trf-local-quasi-finite-projection).

The affine-neighbourhood and relative affine-space projection are obtained by the
local quasi-finite projection argument.

Proof (Orgogozo Proposition 2.3, using the recorded Stacks lemmas):
1. Since `g` is locally of finite type and `B` is affine, the affine-pair
   characterization of locally finite type gives an affine open `U` containing the
   image of `y` and a finite-type affine map over `B`.
2. Every fibre of `U.toScheme ⟶ B` is an open subspace of the corresponding fibre of
   `g`, so closures of irreducible chains preserve the bound `N`. The weak relative
   Noether-normalization statement then gives `d ≤ N` and a quasi-finite map from
   `U.toScheme` to the `d`-variable polynomial affine space over `B`.
3. The polynomial-ring map gives `e` and its structural composite is `U.ι ≫ g`.
   Since both schemes are affine, `e` is separated; the quasi-finite definition
   supplies finite type and isolated points, and affine quasi-compact fibres make
   those fibres finite discrete.
-/
theorem localQuasiFiniteProjection {B Y : Scheme.{u}} [IsAffine B]
    (g : Y ⟶ B) [LocallyOfFiniteType g]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (N : ℕ)
    (hN : ∀ s : B, topologicalKrullDim (g.fiber s) ≤ (N : WithBot ℕ∞)) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ y (closedPoint Ω) ∈ U ∧
      ∃ d : ℕ, d ≤ N ∧
        ∃ e : U.toScheme ⟶ 𝔸(ULift.{u} (Fin d); B),
          IsSeparated e ∧ Scheme.Hom.IsQuasiFinite e ∧
            e ≫ (𝔸(ULift.{u} (Fin d); B) ↘ B) = U.ι ≫ g := by
  sorry

end AlgebraicGeometry
