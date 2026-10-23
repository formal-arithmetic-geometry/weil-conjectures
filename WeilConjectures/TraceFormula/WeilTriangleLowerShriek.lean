/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.WeilTriangle

/-!

# The lower shriek of Weil objects preserves distinguished triangles

`ProEtale.CondensedRing.WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map`: the image
under `Rf_!` of a distinguished triangle of Weil objects is distinguished.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y W : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) (eW : W ≅ W)

/-- **The lower shriek of Weil objects preserves distinguished triangles** (standard input, still
`sorry`): `Rf_!` is a triangulated functor (`R(f)_!` on the ambient derived categories commutes
with the shifts and is triangulated), and the compact-support base change isomorphism giving the
Frobenius structure of `Rf_!^Weil` commutes with the shifts, so the image of the connecting
morphism commutes with the Frobenius structures. -/
theorem WeilBoundedConstructible.IsDistTriang.weilLowerShriek_map {f : X ⟶ Y}
    (hf : eX.hom ≫ f = f ≫ eY.hom) {A B C : WeilBoundedConstructible ℓ eX.hom} {a : A ⟶ B}
    {b : B ⟶ C} (h : WeilBoundedConstructible.IsDistTriang ℓ a b) :
    WeilBoundedConstructible.IsDistTriang ℓ ((weilLowerShriek ℓ eX eY hf).map a)
      ((weilLowerShriek ℓ eX eY hf).map b) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
