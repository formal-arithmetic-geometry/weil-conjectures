/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q125
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-! # A positive tensor power satisfies the square identity over a field

Source: Guo, Divisors on coherent schemes and homogeneous spaces, Proposition 5.2(ii),
field case, Claim 5.2.1 and norm descent, printed pages 11–12, March 31, 2026 version.
(blueprint: lem-sfb-field-product-square-power)

Products in `Over (Spec k)` are fibre products over `k`; their underlying schemes
are identified with Mathlib's chosen pullbacks by `Over.prodLeftIsoPullback`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on a product of three smooth separated geometrically integral
finite-presentation schemes over a field has a positive tensor power whose square difference
is pulled back from the first two doubled factors. The Boolean indices `false`, `true` mean
coordinates `0`, `1`. In `D`, the factors have signs `+,+,-,-` in order `00,11,01,10`.
Finite presentation is expressed by local finite presentation and quasi-compactness;
quasi-separatedness follows from separatedness.

Source: Guo, Proposition 5.2(ii), field case, Claim 5.2.1 and its norm descent paragraph,
printed pages 11–12, March 31, 2026 version.
(blueprint: lem-sfb-field-product-square-power)

Proof:
1. Apply `lem-sfb-field-square-after-finite-extension` to obtain a finite extension `K/k`
and an invertible module `N_K` on `P_K` with `D(A_K)` isomorphic to `pi_K^* N_K`.
2. Put `d = [K:k]`. By `lem-sfb-finite-field-picard-norm-base-change`, the norm on Picard
classes commutes with pullback and sends the pullback of a module to its `d`-fold tensor
power. Pullback commutes with the four coordinate maps, tensor and dual, so the pullback
of `D(A)` is `D(A_K)`. Expanding the factors gives `D(A.tensorPow d)` isomorphic to
`D(A).tensorPow d`.
3. Apply the norm to the isomorphism from step 1. Its left side is the `d`-fold tensor
power of `D(A)` and its right side is `pi^* Nm(N_K)`. Since a finite field extension has
positive degree, take `n = d` and an invertible representative `N` of `Nm(N_K)`.
-/
theorem exists_fieldProductSquare_tensorPower (k : Type u) [Field k]
    (X₁ X₂ X₃ : Over (Spec (CommRingCat.of k)))
    [Smooth X₁.hom] [Smooth X₂.hom] [Smooth X₃.hom]
    [IsSeparated X₁.hom] [IsSeparated X₂.hom] [IsSeparated X₃.hom]
    [LocallyOfFinitePresentation X₁.hom] [LocallyOfFinitePresentation X₂.hom]
    [LocallyOfFinitePresentation X₃.hom]
    [QuasiCompact X₁.hom] [QuasiCompact X₂.hom] [QuasiCompact X₃.hom]
    [GeometricallyIntegral X₁.hom] [GeometricallyIntegral X₂.hom]
    [GeometricallyIntegral X₃.hom] :
    let C := (X₁ ⨯ X₂) ⨯ X₃
    let P := (X₁ ⨯ X₁) ⨯ (X₂ ⨯ X₂)
    let Q := P ⨯ X₃
    let x (a : Bool) : Q ⟶ X₁ :=
      prod.fst ≫ prod.fst ≫ (if a then prod.snd else prod.fst)
    let y (b : Bool) : Q ⟶ X₂ :=
      prod.fst ≫ prod.snd ≫ (if b then prod.snd else prod.fst)
    let r (a b : Bool) : Q ⟶ C := prod.lift (prod.lift (x a) (y b)) prod.snd
    let D (M : C.left.Modules) : Q.left.Modules :=
      (((tensorPullback (r false false).left).obj M ⊗
        (tensorPullback (r true true).left).obj M) ⊗
        dual ((tensorPullback (r false true).left).obj M)) ⊗
        dual ((tensorPullback (r true false).left).obj M)
    ∀ (A : C.left.Modules), A.IsInvertible →
      ∃ (n : ℕ), 1 ≤ n ∧ ∃ (N : P.left.Modules), N.IsInvertible ∧
        Nonempty (D (A.tensorPow n) ≅ (tensorPullback (prod.fst : Q ⟶ P).left).obj N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
