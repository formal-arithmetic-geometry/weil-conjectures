/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise
public import WeilConjectures.EtaleCohomology.PoincareDuality.Weil

/-!

# Frobenius: equivariance, similitude, reciprocity

Every ingredient of the Poincaré pairing — the mixed-support cup product, the evaluation and
the orientation — is equivariant for the geometric Frobenius, so the pairing itself is a
morphism of Weil objects. Read on the twisted pairing this says that `β_K` is *invariant*:

`⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`.

The Tate twist carries the factor `q^{-d}`, so the untwisted, line-valued pairing is a
*similitude* of factor `q^d`:

`⟨F_{c,K} x, F_{K^∨} y⟩_i = q^d ⟨x, y⟩_i`.

Since the untwisted pairing is perfect, `F_{K^∨}` is conjugate to `q^d (F_{c,K}^{-1})^t`; the
characteristic polynomial being invariant under transposition, the eigenvalues of `F` on
`H^{2d-i}(X, K^∨)` are the `q^d / α` for `α` an eigenvalue of `F_c` on `H^i_c(X, K)`, with
multiplicity. That last step is pure linear algebra and is already available as
`LinearMap.charpoly_roots_of_similitude` of `WeilConjectures.ZetaLinearAlgebra.Pairing`, which
is why it is not restated here: the theorem below records the similitude and the perfectness
that feed it.

No clause uses properness of `X₀`.

## Main results

- `AlgebraicGeometry.ProEtale.frobenius_poincarePairing`.

-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {k₀ : Type u} [Field k₀] [Finite k₀] {d : ℕ}

/-- Blueprint `sk-thm-frobenius`: Frobenius: equivariance, similitudine, reciprocity.

For a strict Weil complex `K` perfect over `Λ_X` (and with no properness assumption on `X₀`):

1. the twisted degreewise pairing is Frobenius invariant,
   `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`;
2. the untwisted, line-valued pairing is a similitude of factor `q^d`,
   `⟨F_{c,K} x, F_{K^∨} y⟩_i = q^d ⟨x, y⟩_i`;
3. the untwisted pairing is perfect, so `F_{K^∨}` is conjugate to `q^d (F_{c,K}^{-1})^t` and
   the eigenvalues of `F` on `H^{2d-i}(X, K^∨)` are the `q^d / α` for the eigenvalues `α` of
   `F_c` on `H^i_c(X, K)`, with multiplicity. -/
theorem frobenius_poincarePairing (T : PoincareDualitySetting k₀ d)
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k₀ k] [Algebra.IsAlgebraic k₀ k]
    [HasCompactification (T.structureMorphism k)]
    (γ : ((tateTwist A (T.geometricFibre k) (d : ℤ)).obj (𝟙_ _))⟦(2 * d : ℤ)⟧ ≅
      dualizingComplex A (T.structureMorphism k))
    (K : WeilComplex A (T.geometricFrobenius k)) (hK : IsPerfect A K.obj) (i : ℤ) :
    tensorHom
        (K.compactlySupportedCohomologyFrobenius (T.structureMorphism k) (specFrobenius k₀ k)
          (T.geometricFrobenius_comp_structureMorphism k) i)
        ((K.dual.twist (d : ℤ)).cohomologyFrobenius (2 * d - i)) ≫
          degreewisePoincarePairing A (T.structureMorphism k) d γ K.obj i =
        degreewisePoincarePairing A (T.structureMorphism k) d γ K.obj i ∧
      tensorHom
        (K.compactlySupportedCohomologyFrobenius (T.structureMorphism k) (specFrobenius k₀ k)
          (T.geometricFrobenius_comp_structureMorphism k) i)
        (K.dual.cohomologyFrobenius (2 * d - i)) ≫
          untwistedDegreewisePoincarePairing A (T.structureMorphism k) d γ K.obj i =
        ((Nat.card k₀ ^ d : ℤ)) •
          untwistedDegreewisePoincarePairing A (T.structureMorphism k) d γ K.obj i ∧
      MonoidalClosed.IsPerfectPairing
        (untwistedDegreewisePoincarePairing A (T.structureMorphism k) d γ K.obj i) :=
  sorry

end ProEtale

end AlgebraicGeometry
