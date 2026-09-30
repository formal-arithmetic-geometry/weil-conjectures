/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

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

- `AlgebraicGeometry.Etale.artinSchreierActionPushforward`: the action of `σ_a` on
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
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_inv`: the two inversion formulas
  `ℒ_Ψ ⊗ (-1)^* ℒ_Ψ ≅ Λ` and `ℒ_Ψ ⊗ ℒ_{Ψ⁻¹} ≅ Λ`.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `sk-lem-as-properties` also contains the decomposition `(AS_q)_* Λ ≅ ⨁_χ ℒ_χ`
of the pushforward, the trace function of `ℒ_{Ψ, a f}` and the cohomology of the affine line
with coefficients in `ℒ_{Ψ, a x}`. Those are deferred: they are the inputs to the *proofs* of
the statements of this block.

## Implementation notes

`q` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines `ℒ_Ψ` is
`q⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `(AS_q)_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

The field `k` lives in the universe `u` of the schemes, so that `𝔸¹_k = 𝔸(PUnit; Spec k)` is
a scheme in that universe; the case `k = ℤ/p` uses `ULift (ZMod p)`.

The action of `σ_a` on `(AS_q)_* Λ` is `(AS_q)_*` of the unit
`Λ ⟶ (σ_a)_* (σ_a)^* Λ ≅ (σ_a)_* Λ` of the adjunction `σ_a^* ⊣ (σ_a)_*`, followed by
`(AS_q)_* (σ_a)_* = (σ_a ≫ AS_q)_* = (AS_q)_*`. The constant sheaf `Λ` is
`AlgebraicGeometry.Scheme.constantSheafSelf` rather than the monoidal unit, since the pullback
of constant sheaves `AlgebraicGeometry.Scheme.upperStarConstantSheafIso` is stated for
`constantSheaf`.

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

variable {Λ : Type (u + 1)} [CommRing Λ]

section Construction

variable (Λ) (k : Type u) [Field k] [Fintype k]

/-- The action of the translation `σ_a : x ↦ x + a` of `𝔸¹_k` on the pushforward `(AS_q)_* Λ`:
`(AS_q)_*` of the unit `Λ ⟶ (σ_a)_* (σ_a)^* Λ ≅ (σ_a)_* Λ`, followed by
`(AS_q)_* (σ_a)_* ≅ (σ_a ≫ AS_q)_* = (AS_q)_*`. -/
def artinSchreierActionPushforward (a : k) :
    (AS[k])_*[ModuleCat.{u + 1} Λ].obj (Scheme.constantSheafSelf Λ _) ⟶
      (AS[k])_*[ModuleCat.{u + 1} Λ].obj (Scheme.constantSheafSelf Λ _) :=
  (AS[k])_*[ModuleCat.{u + 1} Λ].map
      ((upperStarLowerStarAdjunction _
          (AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k)).inv.hom a)).unit.app _ ≫
        (AffineSpace.translation fun _ ↦
            (Scheme.ΓSpecIso (.of k)).inv.hom a)_*[ModuleCat.{u + 1} Λ].map
          ((Scheme.upperStarConstantSheafIso _
            (AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k)).inv.hom a)).hom.app
              (ModuleCat.of Λ Λ))) ≫
    (lowerStarComp _ (AffineSpace.translation fun _ ↦ (Scheme.ΓSpecIso (.of k)).inv.hom a)
      (AS[k]) (AS[k])
      (AffineSpace.translation_comp_artinSchreierMap_card k _ fun _ ↦ a).symm).hom.app _

/-- The translation by `0` acts trivially on `(AS_q)_* Λ`. -/
lemma artinSchreierActionPushforward_zero :
    artinSchreierActionPushforward Λ k 0 = 𝟙 _ :=
  sorry

/-- The translations act on `(AS_q)_* Λ` through the additive group of `k`: `σ_a σ_b = σ_{a+b}`. -/
@[reassoc]
lemma artinSchreierActionPushforward_comp (a b : k) :
    artinSchreierActionPushforward Λ k a ≫ artinSchreierActionPushforward Λ k b =
      artinSchreierActionPushforward Λ k (a + b) :=
  sorry

variable {Λ k} [Invertible (Fintype.card k : Λ)]

/-- The endomorphism `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a` of `(AS_q)_* Λ` cutting out the
`Ψ`-isotypic component, where `q = #k`. -/
def artinSchreierIdempotent (Ψ : AddChar k Λ) :
    (AS[k])_*[ModuleCat.{u + 1} Λ].obj (Scheme.constantSheafSelf Λ _) ⟶
      (AS[k])_*[ModuleCat.{u + 1} Λ].obj (Scheme.constantSheafSelf Λ _) :=
  ∑ a : k, (AS[k])_*[ModuleCat.{u + 1} Λ].map
      ((constantSheaf _ _).map
        (ModuleCat.ofHom ((⅟(Fintype.card k : Λ) * Ψ (-a)) • LinearMap.id))) ≫
    artinSchreierActionPushforward Λ k a

/-- `e_Ψ` is an idempotent. -/
lemma isIdempotentElem_artinSchreierIdempotent (Ψ : AddChar k Λ) :
    IsIdempotentElem (M := End ((AS[k])_*[ModuleCat.{u + 1} Λ].obj (Scheme.constantSheafSelf Λ _)))
      (artinSchreierIdempotent Ψ) :=
  -- expand `e_Ψ ≫ e_Ψ` with `artinSchreierActionPushforward_comp` and reindex the double sum
  -- by `a + b`; the inner sum is `∑_b Ψ(-b) Ψ(b) = q`
  sorry

/-- Each `σ_b` acts on the image of `e_Ψ` by the scalar `Ψ(b)`: `σ_b e_Ψ = Ψ(b) e_Ψ`. -/
lemma artinSchreierIdempotent_comp_artinSchreierActionPushforward (Ψ : AddChar k Λ) (b : k) :
    artinSchreierIdempotent Ψ ≫ artinSchreierActionPushforward Λ k b =
      (AS[k])_*[ModuleCat.{u + 1} Λ].map
          ((constantSheaf _ _).map (ModuleCat.ofHom (Ψ b • LinearMap.id))) ≫
        artinSchreierIdempotent Ψ :=
  -- reindex the sum by `a + b` using `artinSchreierActionPushforward_comp`
  sorry

/-- The *Artin–Schreier sheaf* `ℒ_Ψ` on `𝔸¹_k`: the image of the idempotent `e_Ψ` on
`(AS_q)_* Λ`, that is, the `Ψ`-isotypic component of the pushforward of the constant sheaf
along the Artin–Schreier map `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`.
(sketch blueprint: `sk-def-as`) -/
def artinSchreierSheaf (Ψ : AddChar k Λ) :
    Sheaf (Scheme.smallEtaleTopology 𝔸¹[k]) (ModuleCat.{u + 1} Λ) :=
  image (artinSchreierIdempotent Ψ)

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f} := f^* ℒ_Ψ` of a global function `f` on a `k`-scheme
`X`, where `f` is viewed as a morphism `X ⟶ 𝔸¹_k`.
(sketch blueprint: `sk-def-as`) -/
def artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (AffineSpace.homOfVector (X ↘ Spec (.of k)) fun _ ↦ f)^*[ModuleCat.{u + 1} Λ].obj
    (artinSchreierSheaf Ψ)

/-- The Artin–Schreier sheaf is compatible with pullback: for a `k`-morphism `g : X' ⟶ X`,
`g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`. -/
def artinSchreierSheafOfPullbackIso {X X' : Scheme.{u}} [X.Over (Spec (.of k))]
    [X'.Over (Spec (.of k))] (g : X' ⟶ X) [g.IsOver (Spec (.of k))] (Ψ : AddChar k Λ)
    (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheafOf X Ψ f) ≅
      artinSchreierSheafOf X' Ψ (g.appTop f) :=
  -- the function `g^* f`, as a morphism `X' ⟶ 𝔸¹_k`, is the composite of `g` and `f`
  ((upperStarComp _ g _ _
    (AffineSpace.hom_ext (by simp) fun _ ↦ by simp)).app (artinSchreierSheaf Ψ)).symm

/-- For a scheme `X` of characteristic `p`, the Artin–Schreier sheaf `ℒ_{Ψ, f}` of a global
function `f` and an additive character `Ψ` of `ℤ/p`, where `X` is viewed as a scheme over
`𝔽_p`. -/
def artinSchreierSheafZMod {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  letI : X.Over (Spec (.of (ULift.{u} (ZMod p)))) :=
    ⟨X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      ((ZMod.castHom dvd_rfl Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom))⟩
  letI : Invertible (Fintype.card (ULift.{u} (ZMod p)) : Λ) :=
    ‹Invertible (p : Λ)›.copy _ (by simp)
  artinSchreierSheafOf X (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f

end Construction

section Properties

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]

/-- The Artin–Schreier sheaf is lisse.
(sketch blueprint: `sk-lem-as-properties`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar k Λ) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf Ψ) :=
  -- `AS_q` is finite étale (`AffineSpace.isFinite_artinSchreierMap`,
  -- `AffineSpace.etale_artinSchreierMap`) and a `k`-torsor
  -- (`AffineSpace.isIso_sigmaDesc_translation_artinSchreierMap`), so `(AS_q)_* Λ` is locally
  -- the regular representation `Λ[k]`, and `e_Ψ` cuts out a free summand of rank one
  sorry

instance isLocallyConstantSheaf_artinSchreierSheafOf (X : Scheme.{u}) [X.Over (Spec (.of k))]
    (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheafOf X Ψ f) :=
  Scheme.IsLocallyConstantSheaf.upperStar _ _

/-- The Artin–Schreier sheaf is rigidified along the zero section `0 : Spec k ⟶ 𝔸¹_k`:
`Λ ≅ 0^* ℒ_Ψ`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_zero (Ψ : AddChar k Λ) :
    Nonempty (𝟙_ _ ≅ (AffineSpace.zeroSection PUnit (Spec (.of k)))^*[ModuleCat.{u + 1} Λ].obj
      (artinSchreierSheaf Ψ)) :=
  sorry

/-- The Artin–Schreier sheaf turns addition into tensor product: on `𝔸²_k = 𝔸¹_k ×_k 𝔸¹_k`,
with the addition `m` and the two projections `u₁, u₂`, `m^* ℒ_Ψ ≅ u₁^* ℒ_Ψ ⊗ u₂^* ℒ_Ψ`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_add (Ψ : AddChar k Λ) :
    Nonempty ((AffineSpace.add PUnit (Spec (.of k)))^*[ModuleCat.{u + 1} Λ].obj
        (artinSchreierSheaf Ψ) ≅
      (pullback.fst (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat.{u + 1} Λ].obj
          (artinSchreierSheaf Ψ) ⊗
        (pullback.snd (𝔸¹[k] ↘ Spec (.of k)) (𝔸¹[k] ↘ Spec (.of k)))^*[ModuleCat.{u + 1} Λ].obj
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

/-- The inverse of `ℒ_Ψ` is `(-1)^* ℒ_Ψ`, the pullback along the reflection `x ↦ -x`. -/
theorem nonempty_iso_artinSchreierSheaf_neg (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗
        (AffineSpace.neg PUnit (Spec (.of k)))^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf Ψ) ≅
      𝟙_ _) :=
  -- pull back `nonempty_iso_artinSchreierSheaf_add` along `(1, -1) : 𝔸¹_k ⟶ 𝔸²_k` and use
  -- `nonempty_iso_artinSchreierSheaf_zero`; this needs the compatibility of pullback with tensor
  -- products
  sorry

/-- The inverse of `ℒ_Ψ` is also `ℒ_{Ψ⁻¹}`; combined with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg` this is the identification
`(-1)^* ℒ_Ψ ≅ ℒ_{Ψ⁻¹}` used for the kernel of the Fourier transform attached to the inverse
character. -/
theorem nonempty_iso_artinSchreierSheaf_inv (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf Ψ ⊗ artinSchreierSheaf Ψ⁻¹ ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul Ψ Ψ⁻¹
  obtain ⟨e'⟩ := nonempty_iso_artinSchreierSheaf_one (k := k) (Λ := Λ)
  exact ⟨e ≪≫ eqToIso (by rw [mul_inv_cancel]) ≪≫ e'⟩

end Properties

end AlgebraicGeometry.Etale
