/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Finite.Isotypic

/-!

# The Artin–Schreier sheaf

Let `k` be a finite field with `q` elements and let `Ψ` be an additive character of `k` with
values in a coefficient ring `Λ` in which `q` is invertible. The Artin–Schreier map
`AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `x ↦ x^q - x`, is a finite étale torsor under `k` acting by the
translations `σ_a : x ↦ x + a`. The *Artin–Schreier sheaf* `ℒ_Ψ := e_Ψ (AS_q)_* Λ` on `𝔸¹_k`
is the `Ψ`-isotypic component of the pushforward of the constant sheaf, cut out by the
idempotent `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a`. For a `k`-scheme `X` and a global function
`f ∈ Γ(X, 𝒪_X)`, viewed as a morphism `f : X ⟶ 𝔸¹_k`, the Artin–Schreier sheaf of `f` is the
pullback `ℒ_{Ψ, f} := f^* ℒ_Ψ`. It is a lisse sheaf of rank one; it turns addition of
functions into tensor product of sheaves, and multiplication of characters likewise. The
classical case is `k = ℤ/p`.

## Main definitions

- `AlgebraicGeometry.Etale.artinSchreierTranslationAction`: the action of `σ_a` on
  `(AS_q)_* Λ`.
- `AlgebraicGeometry.Etale.artinSchreierIdempotent`: the idempotent endomorphism
  `e_Ψ = q⁻¹ ∑_a Ψ(-a) σ_a` of `(AS_q)_* Λ`.
- `AlgebraicGeometry.Etale.artinSchreierSheaf`: the Artin–Schreier sheaf `ℒ_Ψ` on `𝔸¹_k`, the
  image of `e_Ψ`.
- `AlgebraicGeometry.Etale.artinSchreierSheafOf`: the Artin–Schreier sheaf `ℒ_{Ψ, f} = f^* ℒ_Ψ`
  of a global function `f` on a `k`-scheme, with its pullback compatibility
  `AlgebraicGeometry.Etale.artinSchreierSheafOfPullbackIso`.
- `AlgebraicGeometry.Etale.artinSchreierSheafZMod`: the case `k = ℤ/p`, for a scheme of
  characteristic `p`, with its pullback compatibility
  `AlgebraicGeometry.Etale.artinSchreierSheafZModPullbackIso`.

## Main statements

- `AlgebraicGeometry.Etale.isIdempotentElem_artinSchreierIdempotent`: `e_Ψ` is idempotent.
- `AlgebraicGeometry.Etale.exists_eq_artinSchreierTranslation_of_comp_artinSchreierMap`: the
  automorphisms of the Artin–Schreier covering are the translations.
- `AlgebraicGeometry.Etale.artinSchreierSheafUpperStarIso`: `AS_q^* ℒ_Ψ ≅ Λ`, so that `ℒ_Ψ` is
  lisse of rank one (`AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`).
- `AlgebraicGeometry.Etale.artinSchreierPushforwardIsoBiproduct`: for a primitive `Ψ` with
  values in a domain, the decomposition `(AS_q)_* Λ ≅ ⨁_{b ∈ k} ℒ_{Ψ(b ·)}` given by the
  orthogonal idempotents `e_{Ψ(b ·)}`.
- `AlgebraicGeometry.Etale.isConstructibleSheaf_artinSchreierSheafOf`: over a finite `Λ`,
  `ℒ_{Ψ, f}` is constructible.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_zero`: the rigidification
  `Λ ≅ 0^* ℒ_Ψ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_add`:
  `m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` on `𝔸²_k`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one`: `ℒ_1 ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_mul`: `ℒ_Ψ ⊗ ℒ_{Ψ'} ≅ ℒ_{Ψ Ψ'}`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`: `[c]^* ℒ_Ψ ≅ ℒ_{Ψ(c ·)}` for
  `c ∈ kˣ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg`: the two inversion formulas
  `ℒ_Ψ ⊗ ℒ_{Ψ⁻¹} ≅ Λ` and `ℒ_Ψ ⊗ (-1)^* ℒ_Ψ ≅ Λ`, proved from the previous three.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_add`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_zero`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_mul` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_one`: for functions `f, g` on
  `X`, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`, `ℒ_{Ψ, 0} ≅ Λ`, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`
  and `ℒ_{1, f} ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg`,
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg_inv`: the inverse of
  `ℒ_{Ψ, f}` is both `ℒ_{Ψ, -f}` and `ℒ_{Ψ⁻¹, f}`, and `ℒ_{Ψ, -f} ≅ ℒ_{Ψ⁻¹, f}`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `sk-lem-as-properties` also contains the trace function of `ℒ_{Ψ, a x}`
(`AlgebraicGeometry.WeilSheaf.traceFunction_artinSchreier`, stated for the `ℓ`-adic Weil sheaf
`AlgebraicGeometry.artinSchreier`, where trace functions are defined) and the cohomology of the
affine line with coefficients in `ℒ_{Ψ, a x}`
(`WeilConjectures.FourierTransform.ArtinSchreierCohomology`). The orthogonality
`e_χ e_{χ'} = 0` and completeness `∑_χ e_χ = 1` of the character projectors fail for a general
`Λ` (the first when `Λ` has zero divisors, the second when `Λ` lacks the `p`-th roots of unity);
the isotypic decomposition is stated for a primitive character with values in a domain.

## Implementation notes

`q` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines `ℒ_Ψ` is
`q⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `(AS_q)_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

The field `k` lives in the universe `u` of the schemes, so that `𝔸¹_k = 𝔸(PUnit; Spec k)` is
a scheme in that universe; the case `k = ℤ/p` uses `ULift (ZMod p)`.

The constant sheaf `Λ` is the monoidal unit `𝟙_`, and its pullback `g^* Λ ≅ Λ` is the unit
isomorphism `Functor.Monoidal.εIso` of the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar`. The action of `σ_a` on `(AS_q)_* Λ` is the
general `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver` for the endomorphism `σ_a`
of `𝔸¹_k` over `AS_q`, so the group law of the action reduces to that of the translations.

The proofs go through the trivialization `AS_q^* ℒ_Ψ ≅ Λ`, the adjoint of the inclusion
`ℒ_Ψ ⟶ (AS_q)_* Λ`, which is checked on stalks: at a geometric point `t` of the source, the
stalk of `(AS_q)_* Λ` at `t ≫ AS_q` is the product of copies of `Λ` indexed by the geometric
fibre, a `k`-torsor (`AlgebraicGeometry.Etale.exists_eq_comp_artinSchreierTranslation`), and a
`Ψ`-isotypic germ is determined by its value at `t`. Since `AS_q` is surjective, `AS_q^*`
reflects isomorphisms, so a morphism into `ℒ_χ` whose adjoint is an isomorphism is itself
one; this gives `zero`, `one` and `mul`. For `smul`, the scaling `[c]` is an automorphism of
`𝔸¹_k` commuting with `AS_q`, so `[c]^* ≅ [c⁻¹]_*` carries the splitting of `e_Ψ` to a splitting
of the conjugate idempotent, which is `e_{Ψ(c ·)}`. For `add`, the three sheaves `m^* ℒ_Ψ`,
`u₁^* ℒ_Ψ` and `u₂^* ℒ_Ψ` on `𝔸²_k` are trivialized by `AS_q × AS_q`, on which `k × k` acts by
the translations; so `m^* ℒ_Ψ` and `u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` are both the isotypic component of
`(AS_q × AS_q)_* Λ` for the character `(a, b) ↦ Ψ(a) Ψ(b)`
(`AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`).

The isomorphisms `zero`, `add`, `one`, `mul` and `smul` are stated as `Nonempty` theorems
rather than as `def`s, to keep the statements uniform. All of them should become `def`s: the
Fourier inversion and base change arguments need the specific rigidification
`ε_Ψ : Λ ≅ 0^* ℒ_Ψ` and the unique `m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` restricting to it, with
their coherences.

The statements for `ℒ_{Ψ, f}` are proved as pullbacks of the universal statements on `𝔸¹_k`
and `𝔸²_k`: `zero` and `one` along `g^* Λ ≅ Λ`, and `add` and `mul` along
`g^* (A ⊗ B) ≅ g^* A ⊗ g^* B` from the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar`. For `add` the pullback is along the pair
`(f, g) : X ⟶ 𝔸²_k`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Etale

/-- The affine line `𝔸¹_k` over a field `k`. -/
local notation "𝔸¹[" k "]" => 𝔸(PUnit; Spec (CommRingCat.of k))

/-- The Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, `x ↦ x ^ q - x`, where `q = #k`. -/
local notation "AS[" k "]" =>
  AffineSpace.artinSchreierMap PUnit (Spec (CommRingCat.of k)) (Fintype.card k)

set_option quotPrecheck false in
/-- The pushforward `(AS_q)_* Λ` of the constant sheaf along the Artin–Schreier map. -/
local notation "𝒫[" Λ ", " k "]" => (AS[k])_*[ModuleCat Λ].obj (𝟙_ _)

variable {Λ : Type (u + 1)} [CommRing Λ]

section Translation

variable (k : Type u) [Field k]

variable {k}

variable [Fintype k]

@[deprecated (since := "2026-10-08")]
alias exists_comp_artinSchreierMap_eq := AffineSpace.exists_comp_artinSchreierMap_eq

@[deprecated (since := "2026-10-08")]
alias surjective_artinSchreierMap := AffineSpace.surjective_artinSchreierMap

end Translation

section Construction

variable (Λ) (k : Type u) [Field k] [Fintype k]

variable {Λ k} [Invertible (Fintype.card k : Λ)]

end Construction

section ZMod

end ZMod

section Trivialization

/-! ### The Artin–Schreier sheaf becomes constant on the covering

The adjoint `AS_q^* ℒ_Ψ ⟶ Λ` of the inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` is an isomorphism. On the
stalk at a geometric point `t` of the source this is the restriction to `t` of the
`Ψ`-isotypic germs of functions on the geometric fibre through `t`, which is a `k`-torsor: a
`Ψ`-isotypic germ is determined by its value at `t`, and every value occurs. -/

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ 𝔸¹[k])

end Trivialization

section Properties

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]

section Add

/-! ### Additivity

On `𝔸²_k` the three sheaves `m^* ℒ_Ψ`, `u₁^* ℒ_Ψ` and `u₂^* ℒ_Ψ` are trivialized by the covering
`AS_q × AS_q : 𝔸²_k ⟶ 𝔸²_k`, on which `k × k` acts by the translations `σ_a × σ_b`, through
the characters `Ψ(a + b)`, `Ψ(a)` and `Ψ(b)`. Hence `m^* ℒ_Ψ` and `u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ` are both
the isotypic component of `(AS_q × AS_q)_* Λ` for the character `(a, b) ↦ Ψ(a) Ψ(b)`
(`AlgebraicGeometry.Etale.nonempty_iso_of_isotypic`). -/

set_option quotPrecheck false in
/-- The affine plane `𝔸²_k = 𝔸¹_k ×_k 𝔸¹_k`. -/
local notation "𝔸²[" k "]" => pullback (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k))

variable {W Y : Scheme.{u}} (π : W ⟶ Y) (v : Y ⟶ 𝔸¹[k]) (p : W ⟶ 𝔸¹[k])
  (h : p ≫ AS[k] = π ≫ v) (Ψ : AddChar k Λ)

end Add

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

end Properties

end AlgebraicGeometry.Etale
