/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

/-! # Stalk comparison for coefficient duals -/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
variable {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

/-- The geometric stalk of the coefficient dual is the linear dual of the geometric stalk.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`, the docstring of
`IsFiniteLocallyConstantSheaf.ihom_unit`, finite presentation and module dual argument.

Proof: Fix s and an étale trivializing neighborhood through which s lifts. On this
neighborhood F is constant with value M, identified with F_s, and M is finitely generated.
Noetherianity gives a finite presentation Λᵐ → Λⁿ → M → 0. After exact constant
sheafification, internal Hom into the unit is the kernel of the transposed finite matrix.
The geometric stalk functor is exact, and its monoidal unit comparison identifies the
stalks of the finite free constant sheaves with Λⁿ and Λᵐ. It therefore identifies the stalk
of the sheaf dual with the kernel of the same transposed matrix on modules, namely
Hom_Λ(M, Λ). Transport along M ≅ F_s yields the asserted module isomorphism. This uses
finite presentation, not projectivity, and does not assert that stalks commute with
internal Hom for arbitrary sheaves.

(blueprint: lem-weil-pbc-flc-dual-stalk) -/
theorem IsFiniteLocallyConstantSheaf.nonempty_ihom_unit_stalk_iso
    (hF : IsFiniteLocallyConstantSheaf F) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Nonempty (((pointSmallEtale s).sheafFiber.obj ((ihom F).obj (𝟙_ _))) ≅
      ModuleCat.of Λ
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F →ₗ[Λ] Λ)) := by sorry

end AlgebraicGeometry.Scheme
