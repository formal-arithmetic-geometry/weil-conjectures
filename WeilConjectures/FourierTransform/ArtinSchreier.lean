/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.ConstructibleSheaf.TensorUnit
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

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
  characteristic `p`.

## Main statements

- `AlgebraicGeometry.Etale.isIdempotentElem_artinSchreierIdempotent`: `e_Ψ` is idempotent.
- `AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`: `ℒ_Ψ` is lisse.
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
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_inv`: the inverse of `ℒ_{Ψ, f}` is
  both `ℒ_{Ψ, -f}` and `ℒ_{Ψ⁻¹, f}`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `sk-lem-as-properties` also contains the decomposition `(AS_q)_* Λ ≅ ⨁_χ ℒ_χ`
of the pushforward, the trace function of `ℒ_{Ψ, a f}` and the cohomology of the affine line
with coefficients in `ℒ_{Ψ, a x}`. Those are deferred: they are the inputs to the *proofs* of
the statements of this block. The orthogonality `e_χ e_{χ'} = 0` and completeness
`∑_χ e_χ = 1` of the character projectors are not stated: they fail for a general `Λ` (the
first when `Λ` has zero divisors, the second when `Λ` lacks the `p`-th roots of unity).

## Implementation notes

`q` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines `ℒ_Ψ` is
`q⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `(AS_q)_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

The field `k` lives in the universe `u` of the schemes, so that `𝔸¹_k = 𝔸(PUnit; Spec k)` is
a scheme in that universe; the case `k = ℤ/p` uses `ULift (ZMod p)`.

The constant sheaf `Λ` is the monoidal unit `𝟙_`, which is definitionally `constantSheaf`
applied to `ModuleCat.of Λ Λ`; its pullback is
`AlgebraicGeometry.Etale.upperStarTensorUnitIso`. The action of `σ_a` on `(AS_q)_* Λ` is the
general `AlgebraicGeometry.Etale.lowerStarConstantSheafEndOfOver` for the endomorphism `σ_a`
of `𝔸¹_k` over `AS_q`, so the group law of the action reduces to that of the translations.

The isomorphisms `zero`, `add`, `one`, `mul` and `smul` are stated as `Nonempty` theorems
rather than as `def`s because they are not yet constructed, and the repository does not allow
a data `def` with a `sorry` body. Once constructed they should become `def`s: the Fourier
inversion and base change arguments need the specific rigidification
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

/-- The translation `σ_a : x ↦ x + a` of the affine line `𝔸¹_k` by `a ∈ k`. -/
def artinSchreierTranslation (a : k) : 𝔸¹[k] ⟶ 𝔸¹[k] :=
  AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k)).inv.hom a

@[simp]
lemma artinSchreierTranslation_zero : artinSchreierTranslation k 0 = 𝟙 _ := by
  rw [artinSchreierTranslation, map_zero]
  exact AffineSpace.translation_zero

lemma artinSchreierTranslation_add (a b : k) :
    artinSchreierTranslation k (a + b) =
      artinSchreierTranslation k a ≫ artinSchreierTranslation k b := by
  simp only [artinSchreierTranslation, map_add]
  exact AffineSpace.translation_add _ _

@[reassoc (attr := simp)]
lemma artinSchreierTranslation_comp_artinSchreierMap [Fintype k] (a : k) :
    artinSchreierTranslation k a ≫ AS[k] = AS[k] :=
  AffineSpace.translation_comp_artinSchreierMap_of_finiteField k _ fun _ ↦ a

end Translation

section Construction

variable (Λ) (k : Type u) [Field k] [Fintype k]

/-- The action of the translation `σ_a : x ↦ x + a` of `𝔸¹_k` on the pushforward `(AS_q)_* Λ`,
pulling back sections along `σ_a`; it uses `σ_a ≫ AS_q = AS_q`:

```
(AS_q)_* Λ --(AS_q)_* η--> (AS_q)_* (σ_a)_* (σ_a)^* Λ ≅ (AS_q)_* (σ_a)_* Λ
    ≅ (σ_a ≫ AS_q)_* Λ = (AS_q)_* Λ
```
-/
def artinSchreierTranslationAction (a : k) : 𝒫[Λ, k] ⟶ 𝒫[Λ, k] :=
  lowerStarConstantSheafEndOfOver (AS[k]) (artinSchreierTranslation k a)
    (artinSchreierTranslation_comp_artinSchreierMap k a)

/-- The translation by `0` acts trivially on `(AS_q)_* Λ`. -/
@[simp]
lemma artinSchreierTranslationAction_zero : artinSchreierTranslationAction Λ k 0 = 𝟙 _ :=
  lowerStarConstantSheafEndOfOver_of_eq_id _ _ (artinSchreierTranslation_zero k) _

/-- The translations act on `(AS_q)_* Λ` through the additive group of `k`:
`σ_{a + b} = σ_a ≫ σ_b`. -/
@[reassoc]
lemma artinSchreierTranslationAction_add (a b : k) :
    artinSchreierTranslationAction Λ k (a + b) =
      artinSchreierTranslationAction Λ k a ≫ artinSchreierTranslationAction Λ k b :=
  lowerStarConstantSheafEndOfOver_of_eq_comp _ _ _ _
    (by rw [add_comm, artinSchreierTranslation_add]) _ _ _

variable {Λ k} [Invertible (Fintype.card k : Λ)]

/-- The endomorphism `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a` of `(AS_q)_* Λ` cutting out the
`Ψ`-isotypic component, where `q = #k`. -/
def artinSchreierIdempotent (Ψ : AddChar k Λ) : 𝒫[Λ, k] ⟶ 𝒫[Λ, k] :=
  ∑ a : k, (⅟(Fintype.card k : Λ) * Ψ (-a)) • artinSchreierTranslationAction Λ k a

/-- Each `σ_b` acts on the image of `e_Ψ` by the scalar `Ψ(b)`: `e_Ψ ≫ σ_b = Ψ(b) • e_Ψ`,

```
(AS_q)_* Λ ---e_Ψ---> (AS_q)_* Λ
    |                     |
  Ψ(b) •                  σ_b
    v                     v
(AS_q)_* Λ ---e_Ψ---> (AS_q)_* Λ
```
-/
lemma artinSchreierIdempotent_comp_artinSchreierTranslationAction (Ψ : AddChar k Λ) (b : k) :
    artinSchreierIdempotent Ψ ≫ artinSchreierTranslationAction Λ k b =
      Ψ b • artinSchreierIdempotent Ψ := by
  simp only [artinSchreierIdempotent, Preadditive.sum_comp, Linear.smul_comp,
    ← artinSchreierTranslationAction_add, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addRight b) _ _ fun a ↦ ?_
  simp only [Equiv.coe_addRight, neg_add_rev]
  congr 1
  have h : Ψ b * Ψ (-b) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [AddChar.map_add_eq_mul]
  linear_combination (-(⅟(Fintype.card k : Λ) * Ψ (-a))) * h

/-- `e_Ψ` is an idempotent. -/
lemma isIdempotentElem_artinSchreierIdempotent (Ψ : AddChar k Λ) :
    IsIdempotentElem (M := End 𝒫[Λ, k]) (artinSchreierIdempotent Ψ) := by
  change artinSchreierIdempotent Ψ ≫ artinSchreierIdempotent Ψ = artinSchreierIdempotent Ψ
  conv_lhs => arg 2; rw [artinSchreierIdempotent]
  simp only [Preadditive.comp_sum, Linear.comp_smul,
    artinSchreierIdempotent_comp_artinSchreierTranslationAction, smul_smul, ← Finset.sum_smul]
  conv_rhs => rw [← one_smul Λ (artinSchreierIdempotent Ψ)]
  congr 1
  simp only [mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_invOf_self]

/-- The *Artin–Schreier sheaf* `ℒ_Ψ` on `𝔸¹_k`: the image of the idempotent `e_Ψ` on
`(AS_q)_* Λ`, that is, the `Ψ`-isotypic component of the pushforward of the constant sheaf
along the Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`.
(sketch blueprint: `sk-def-as`) -/
def artinSchreierSheaf (Ψ : AddChar k Λ) :
    Sheaf (Scheme.smallEtaleTopology 𝔸¹[k]) (ModuleCat Λ) :=
  image (artinSchreierIdempotent Ψ)

/-- The inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` and the projection `r_Ψ : (AS_q)_* Λ ⟶ ℒ_Ψ`,
`image.ι` and `factorThruImage` of `e_Ψ`, satisfy `s_Ψ ≫ r_Ψ = 𝟙`; their composite the other
way round is `e_Ψ` (`CategoryTheory.Limits.image.fac`). -/
@[reassoc (attr := simp)]
lemma image_ι_comp_factorThruImage_artinSchreierIdempotent (Ψ : AddChar k Λ) :
    image.ι (artinSchreierIdempotent Ψ) ≫ factorThruImage (artinSchreierIdempotent Ψ) =
      𝟙 _ := by
  rw [← cancel_mono (image.ι _), ← cancel_epi (factorThruImage _)]
  simp only [Category.assoc, image.fac_assoc, image.fac, Category.id_comp]
  exact isIdempotentElem_artinSchreierIdempotent Ψ

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f} := f^* ℒ_Ψ` of a global function `f` on a `k`-scheme
`X`, where `f` is viewed as a morphism `X ⟶ 𝔸¹_k`.
(sketch blueprint: `sk-def-as`) -/
def artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) : Sheaf X.smallEtaleTopology (ModuleCat Λ) :=
  (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)^*[ModuleCat Λ].obj
    (artinSchreierSheaf Ψ)

/-- The Artin–Schreier sheaf is compatible with pullback: for a `k`-morphism `g : X' ⟶ X`,
`g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`, since the function `g^* f` is the composite

```
X' --g--> X --f--> 𝔸¹_k
```
-/
def artinSchreierSheafOfPullbackIso {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] (g : X' ⟶ X) [g.IsOver (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat Λ].obj (artinSchreierSheafOf X Ψ f) ≅
      artinSchreierSheafOf X' Ψ (g.appTop f) :=
  ((upperStarComp _ g _ _
    (by rw [AffineSpace.comp_homOfVector, comp_over]; rfl)).app (artinSchreierSheaf Ψ)).symm

end Construction

section ZMod

/-- A scheme `X` of characteristic `p` is a scheme over `𝔽_p`, through the ring map
`ℤ/p ⟶ Γ(X, 𝒪_X)`. -/
@[instance_reducible]
def _root_.AlgebraicGeometry.Scheme.overSpecZModOfCharP (X : Scheme.{u}) (p : ℕ)
    [CharP Γ(X, ⊤) p] : X.Over (Spec (.of (ULift.{u} (ZMod p)))) :=
  ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    ((ZMod.castHom dvd_rfl Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom))⟩

/-- If `p` is invertible in `Λ`, so is the number of elements of `ULift (ZMod p)`. -/
instance {p : ℕ} [NeZero p] [Invertible (p : Λ)] :
    Invertible (Fintype.card (ULift.{u} (ZMod p)) : Λ) :=
  ‹Invertible (p : Λ)›.copy _ (by rw [Fintype.card_ulift, ZMod.card])

/-- For a scheme `X` of characteristic `p`, the Artin–Schreier sheaf `ℒ_{Ψ, f}` of a global
function `f` and an additive character `Ψ` of `ℤ/p`, where `X` is viewed as a scheme over
`𝔽_p` by `AlgebraicGeometry.Scheme.overSpecZModOfCharP`. -/
def artinSchreierSheafZMod {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat Λ) :=
  letI := X.overSpecZModOfCharP p
  artinSchreierSheafOf X (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f

end ZMod

section Properties

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]

/-- The Artin–Schreier sheaf is lisse.
(sketch blueprint: `sk-lem-as-properties`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar k Λ) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf Ψ) :=
  -- `AS_q` is finite étale (`AffineSpace.isFinite_artinSchreierMap`,
  -- `AffineSpace.etale_artinSchreierMap`) and a `k`-torsor
  -- (`AffineSpace.isIso_artinSchreierTorsorMap`), so `(AS_q)_* Λ` is locally the regular
  -- representation `Λ[k]`, and `e_Ψ` cuts out a free summand of rank one
  sorry

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f}` is lisse, as the pullback of a lisse sheaf. -/
instance isLocallyConstantSheaf_artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X Ψ f) :=
  Scheme.IsLocallyConstantSheaf.upperStar _ _

/-- The Artin–Schreier sheaf is rigidified along the zero section `0 : Spec k ⟶ 𝔸¹_k`:
`Λ ≅ 0^* ℒ_Ψ`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_zero (Ψ : AddChar k Λ) :
    Nonempty (𝟙_ _ ≅ (AffineSpace.zeroSection PUnit (Spec (.of k)))^*[ModuleCat Λ].obj
      (artinSchreierSheaf Ψ)) :=
  -- the fibre of `AS_q` over `0` is `∐_{a ∈ k} Spec k`, so `0^* (AS_q)_* Λ ≅ Λ^k`, and `e_Ψ`
  -- cuts out the line spanned by the character vector `(Ψ(a))_a`
  sorry

/-- The Artin–Schreier sheaf turns addition into tensor product: on `𝔸²_k = 𝔸¹_k ×_k 𝔸¹_k`,
with the addition `m` and the two projections `u₁, u₂`,

```
         𝔸²_k
       /  |   \
   u₁ /   | m  \ u₂
     v    v     v
 𝔸¹_k   𝔸¹_k   𝔸¹_k
```

`m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_add (Ψ : AddChar k Λ) :
    Nonempty ((AffineSpace.add PUnit (Spec (.of k)))^*[ModuleCat Λ].obj
        (artinSchreierSheaf Ψ) ≅
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat Λ].obj
          (artinSchreierSheaf Ψ) ⊗
        (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat Λ].obj
          (artinSchreierSheaf Ψ)) :=
  sorry

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf `Λ`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_one :
    Nonempty (artinSchreierSheaf (1 : AddChar k Λ) ≅ 𝟙_ _) :=
  -- the `1`-isotypic component of `(AS_q)_* Λ` is the sheaf of `k`-invariants, which is `Λ`
  -- because `AS_q` is a `k`-torsor
  sorry

/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_Ψ ⊗ ℒ_{Ψ'} ≅ ℒ_{Ψ Ψ'}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_mul (Ψ Ψ' : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗ artinSchreierSheaf Ψ' ≅ artinSchreierSheaf (Ψ * Ψ')) :=
  -- both sides are isotypic components of the pushforward along the same covering
  sorry

/-- The pullback of the Artin–Schreier sheaf along the scaling `[c] : x ↦ c x` by a unit
`c ∈ kˣ` is the Artin–Schreier sheaf of the character `Ψ(c ·)`: `[c]^* ℒ_Ψ ≅ ℒ_{Ψ(c ·)}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_smul (Ψ : AddChar k Λ) (c : kˣ) :
    Nonempty ((AffineSpace.smul PUnit (Spec (.of k))
        ((Scheme.ΓSpecIso (.of k)).inv.hom c))^*[ModuleCat Λ].obj (artinSchreierSheaf Ψ) ≅
      artinSchreierSheaf (Ψ.mulShift c)) :=
  -- `[c]` commutes with `AS_q` since `c ^ q = c`, and it conjugates `σ_a` to `σ_{c a}`; so the
  -- base change of `AS_q` along `[c]` is `AS_q` itself, and base change takes `e_Ψ` to
  -- `e_{Ψ(c ·)}`
  sorry

/-- The inverse of `ℒ_Ψ` is `ℒ_{Ψ⁻¹}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_inv (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗ artinSchreierSheaf Ψ⁻¹ ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul Ψ Ψ⁻¹
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
  exact ⟨e ≪≫ eqToIso (congrArg artinSchreierSheaf (mul_inv_cancel Ψ)) ≪≫ e'⟩

/-- The inverse of `ℒ_Ψ` is also `(-1)^* ℒ_Ψ`, the pullback along the reflection `x ↦ -x`,
since `(-1)^* ℒ_Ψ ≅ ℒ_{Ψ⁻¹}` by `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_smul`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_neg (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗
        (AffineSpace.neg PUnit (Spec (.of k)))^*[ModuleCat Λ].obj (artinSchreierSheaf Ψ) ≅
      𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_smul Ψ (-1)
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheaf_inv Ψ
  rw [Units.val_neg, Units.val_one, map_neg, map_one, AffineSpace.smul_neg_one,
    ← AddChar.inv_mulShift] at e
  exact ⟨whiskerLeftIso _ e ≪≫ e'⟩

variable (X : Scheme.{u}) [X.Over (Spec (.of k))]

/-- The Artin–Schreier sheaf of the zero function is the constant sheaf: `ℒ_{Ψ, 0} ≅ Λ`, the
pullback along `X ⟶ Spec k` of the rigidification `Λ ≅ 0^* ℒ_Ψ`, since the function `0` is the
composite

```
X ----> Spec k --0--> 𝔸¹_k
```

(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_zero (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheafOf X Ψ 0 ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_zero Ψ
  exact ⟨(upperStarComp _ (X ↘ Spec (.of k)) (AffineSpace.zeroSection PUnit _) _ (by
      rw [AffineSpace.zeroSection, AffineSpace.comp_homOfVector, Category.comp_id]
      congr 1; ext; simp)).app (artinSchreierSheaf Ψ) ≪≫
    (X ↘ Spec (.of k))^*[ModuleCat Λ].mapIso e.symm ≪≫ upperStarTensorUnitIso Λ _⟩

/-- The Artin–Schreier sheaf turns addition of functions into tensor product of sheaves,
`ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_add (Ψ : AddChar k Λ) (f g : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ g ≅
      artinSchreierSheafOf X Ψ (f + g)) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_add Ψ
  -- the pair `(f, g) : X ⟶ 𝔸²_k`, through which `f`, `g` and `f + g` factor
  obtain ⟨h, hf, hg, hm⟩ : ∃ h : X ⟶ pullback (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)),
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f) = h ≫ pullback.fst _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) = h ≫ pullback.snd _ _ ∧
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f + g) =
        h ≫ AffineSpace.add PUnit (Spec (.of k)) := by
    refine ⟨pullback.lift (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)
      (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ g) (by simp),
      (pullback.lift_fst _ _ _).symm, (pullback.lift_snd _ _ _).symm, ?_⟩
    rw [AffineSpace.add, AffineSpace.comp_homOfVector]
    simp only [pullback.lift_fst_assoc, AffineSpace.homOfVector_over]
    congr 1; ext
    simp only [Function.comp_apply, map_add, ← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop, pullback.lift_fst, pullback.lift_snd,
      AffineSpace.homOfVector_appTop_coord]
  exact ⟨tensorIso ((upperStarComp (ModuleCat Λ) h _ _ hf).app (artinSchreierSheaf Ψ))
      ((upperStarComp (ModuleCat Λ) h _ _ hg).app (artinSchreierSheaf Ψ)) ≪≫
    (Functor.Monoidal.μIso (h)^*[ModuleCat Λ] _ _) ≪≫ (h)^*[ModuleCat Λ].mapIso e.symm ≪≫
    ((upperStarComp (ModuleCat Λ) h _ _ hm).app (artinSchreierSheaf Ψ)).symm⟩

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf: `ℒ_{1, f} ≅ Λ`,
the pullback of `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one` along `f`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_one (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X (1 : AddChar k Λ) f ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
  exact ⟨Functor.mapIso _ e ≪≫ upperStarTensorUnitIso Λ _⟩

/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_mul (Ψ Ψ' : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ' f ≅
      artinSchreierSheafOf X (Ψ * Ψ') f) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul Ψ Ψ'
  exact ⟨Functor.Monoidal.μIso _ _ _ ≪≫ Functor.mapIso _ e⟩

/-- The inverse of `ℒ_{Ψ, f}` is `ℒ_{Ψ, -f}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_neg (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ (-f) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_add X Ψ f (-f)
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheafOf_zero X Ψ
  exact ⟨e ≪≫ eqToIso (congrArg (artinSchreierSheafOf X Ψ) (add_neg_cancel f)) ≪≫ e'⟩

/-- The inverse of `ℒ_{Ψ, f}` is also `ℒ_{Ψ⁻¹, f}`; together with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheafOf_neg` this identifies
`ℒ_{Ψ, -f}` with `ℒ_{Ψ⁻¹, f}`, as used for the kernel of the inverse Fourier transform.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheafOf_inv (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafOf X Ψ f ⊗ artinSchreierSheafOf X Ψ⁻¹ f ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_mul X Ψ Ψ⁻¹ f
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheafOf_one X (Λ := Λ) (k := k) f
  exact ⟨e ≪≫ eqToIso (congrArg (artinSchreierSheafOf X · f) (mul_inv_cancel Ψ)) ≪≫ e'⟩

end Properties

end AlgebraicGeometry.Etale
