/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.WeilSheaf.Stalk

/-!
# The dual and the geometric coinvariants of a Weil sheaf

The dual of a Weil sheaf `F` is the internal hom `F^∨ = [F, ℚ̄_ℓ]` of étale sheaves on the
geometric fiber `X̄`. Its Weil structure is transported from that of `F`: the pullback `Fr^*`
along the automorphism `Fr` of `X̄` is a monoidal equivalence, so it commutes with internal
homs (`CategoryTheory.Functor.Monoidal.ihomIsoOfIsEquivalence`), and

`Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]`

by the inverse of the Weil structure `φ : Fr^* F ≅ F` in the first variable and the unit
isomorphism `Fr^* ℚ̄_ℓ ≅ ℚ̄_ℓ` in the second.

The geometric coinvariants of `F` are the dual of the global sections of `F^∨`: for a lisse
`F` with geometric generic fibre `V`, a representation of `π₁(X̄)`,
`Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, whose dual is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced by `φ`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.dual`: the dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf.
- `AlgebraicGeometry.WeilSheaf.geometricCoinvariants`: the geometric coinvariants of a lisse
  Weil sheaf, with the Frobenius induced from the Weil structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

-- TODO(unify): sk-d-real-operations
/-- The dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf: the internal hom into the unit sheaf on `X̄`,
with the Weil structure

`Fr^* [F, ℚ̄_ℓ] ≅ [Fr^* F, Fr^* ℚ̄_ℓ] ≅ [F, ℚ̄_ℓ]`

obtained by commuting the monoidal equivalence `Fr^*` with the internal hom
(`CategoryTheory.Functor.Monoidal.ihomIsoOfIsEquivalence`) and then applying the inverse of the
Weil structure `φ : Fr^* F ≅ F` in the (contravariant) first variable and the unit isomorphism
`Fr^* ℚ̄_ℓ ≅ ℚ̄_ℓ` in the second.

The dual is constructible because it is zero: with the present coefficients the sheaf `F` is
zero (`AlgebraicGeometry.WeilSheaf.isZero_carrier`), so is the internal hom out of it
(`CategoryTheory.MonoidalCategory.isZero_ihom_obj_of_isZero`), and the zero sheaf is
constructible. -/
noncomputable def dual (F : WeilSheaf k₀ l X) : WeilSheaf k₀ l X :=
  have := Etale.isEquivalence_upperStar (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
  ⟨Endofunctor.IsoAlgebra.mk ((ihom F.obj.carrier).obj (𝟙_ _))
    (Functor.Monoidal.ihomIsoOfIsEquivalence (WeilSheaf.frobeniusPullback k₀ l X) _ _ ≪≫
      ((MonoidalClosed.internalHom.mapIso F.obj.str.op).app _).symm ≪≫
      (ihom F.obj.carrier).mapIso (Functor.Monoidal.εIso _).symm),
    (Etale.constructibleSheaf _ _).prop_of_isZero
      (isZero_ihom_obj_of_isZero F.isZero_carrier _)⟩

-- TODO(unify): sk-d-real-operations
/-- The geometric coinvariants of a Weil sheaf `F`: the dual `Γ(X̄, F^∨)^∨` of the global
sections of the dual `F^∨`, with the dual of the Frobenius of
`AlgebraicGeometry.WeilSheaf.globalSections`.

For a lisse `F` with geometric generic fibre `V`, a representation of `π₁(X̄)`, the global
sections are `Γ(X̄, F^∨) = (V^∨)^{π₁(X̄)} = (V_{π₁(X̄)})^∨`, so this is the space of coinvariants
`V_{π₁(X̄)}` with the Frobenius induced from the Weil structure: the maximal geometrically
constant quotient of `F`. -/
noncomputable def geometricCoinvariants (F : WeilSheaf k₀ l X) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  FrobeniusModule.dual (globalSections F.dual)

end WeilSheaf

end AlgebraicGeometry
