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
public import WeilConjectures.CategoryTheory.Sites.Point.Linear
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ConstantSheafEnd
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Finite.ConstantSheafEnd

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

The constant sheaf `Λ` is the monoidal unit `𝟙_`, and its pullback `g^* Λ ≅ Λ` is the unit
isomorphism `Functor.Monoidal.εIso` of the strong monoidal structure
`AlgebraicGeometry.Etale.monoidal_upperStar`. The action of `σ_a` on `(AS_q)_* Λ` is the
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

variable {k}

lemma artinSchreierTranslation_appTop_coord (a : k) :
    (artinSchreierTranslation k a).appTop (AffineSpace.coord _ PUnit.unit) =
      AffineSpace.coord _ PUnit.unit +
        (𝔸¹[k] ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv.hom a) :=
  AffineSpace.translation_appTop_coord _ _

instance (a : k) : IsIso (artinSchreierTranslation k a) :=
  ⟨artinSchreierTranslation k (-a), by
    rw [← artinSchreierTranslation_add, add_neg_cancel, artinSchreierTranslation_zero],
    by rw [← artinSchreierTranslation_add, neg_add_cancel, artinSchreierTranslation_zero]⟩

/-- A translation `σ_a` fixing a morphism `s : T ⟶ 𝔸¹_k` with nonzero ring of functions on `T`
is the identity: `a = 0`. -/
lemma eq_zero_of_comp_artinSchreierTranslation_eq {T : Scheme.{u}} [Nontrivial Γ(T, ⊤)]
    (s : T ⟶ 𝔸¹[k]) (a : k) (h : s ≫ artinSchreierTranslation k a = s) : a = 0 := by
  let ψ : k →+* Γ(T, ⊤) :=
    (s ≫ 𝔸¹[k] ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hc := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    artinSchreierTranslation_appTop_coord, map_add, add_eq_left] at hc
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hc
  exact ψ.injective (hc.trans (map_zero ψ).symm)

/-- The translations act faithfully on `𝔸¹_k`: `a ↦ σ_a` is injective. -/
lemma artinSchreierTranslation_injective : Function.Injective (artinSchreierTranslation k) := by
  intro a b h
  have := eq_zero_of_comp_artinSchreierTranslation_eq (𝟙 𝔸¹[k]) (a - b) (by
    rw [Category.id_comp, sub_eq_add_neg, artinSchreierTranslation_add, h,
      ← artinSchreierTranslation_add, add_neg_cancel, artinSchreierTranslation_zero])
  exact sub_eq_zero.mp this

variable [Fintype k]

/-- Two morphisms `s, t : T ⟶ 𝔸¹_k` with the same image under `AS_q`, from a scheme `T` whose
ring of functions is a domain, differ by a translation: `t = s ≫ σ_a` for some `a ∈ k`. The
difference `d` of their coordinates satisfies `d ^ q = d`, so it is a root of
`X ^ q - X = ∏_{a ∈ k} (X - a)`. -/
lemma exists_eq_comp_artinSchreierTranslation {T : Scheme.{u}} [IsDomain Γ(T, ⊤)]
    (s t : T ⟶ 𝔸¹[k]) (h : s ≫ AS[k] = t ≫ AS[k]) :
    ∃ a : k, t = s ≫ artinSchreierTranslation k a := by
  let ψ : k →+* Γ(T, ⊤) :=
    (s ≫ 𝔸¹[k] ↘ Spec (.of k)).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hover : s ≫ 𝔸¹[k] ↘ Spec (.of k) = t ≫ 𝔸¹[k] ↘ Spec (.of k) := by
    rw [← AffineSpace.artinSchreierMap_over, reassoc_of% h]
  have hc := congrArg (fun g ↦ g.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow] at hc
  have hd := FiniteField.sub_pow_card_eq_of_pow_card_sub_eq ψ hc
  obtain ⟨a, -, ha⟩ :=
    Finset.prod_eq_zero_iff.mp (FiniteField.prod_sub_eq_zero_of_pow_card_eq ψ hd)
  refine ⟨a, AffineSpace.hom_ext ?_ fun _ ↦ ?_⟩
  · rw [Category.assoc, artinSchreierTranslation, AffineSpace.translation_over, hover]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, artinSchreierTranslation_appTop_coord,
      map_add, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    change _ = s.appTop (AffineSpace.coord _ PUnit.unit) + ψ a
    linear_combination ha

/-- **The automorphisms of the Artin–Schreier covering are the translations.** Every
endomorphism `g` of `𝔸¹_k` over the Artin–Schreier map `AS_q`, that is with `g ≫ AS_q = AS_q`,
is a translation `σ_a`, and `a` is unique by
`AlgebraicGeometry.Etale.artinSchreierTranslation_injective`. Together with the finiteness
(`AlgebraicGeometry.AffineSpace.isFinite_artinSchreierMap`), the étaleness
(`AlgebraicGeometry.Etale.etale_artinSchreierMap`), the surjectivity
(`AlgebraicGeometry.Etale.surjective_artinSchreierMap`) and the torsor structure
(`AlgebraicGeometry.AffineSpace.isIso_artinSchreierTorsorMap`) of `AS_q`, this is the
Artin–Schreier covering lemma for the universal covering `AS_q : 𝔸¹_k ⟶ 𝔸¹_k`, whose source is
connected; the covering of a function `f` is its base change along `f`.
(blueprint: `lem-fd-as-cover`) -/
theorem exists_eq_artinSchreierTranslation_of_comp_artinSchreierMap (g : 𝔸¹[k] ⟶ 𝔸¹[k])
    (hg : g ≫ AS[k] = AS[k]) : ∃ a : k, g = artinSchreierTranslation k a := by
  obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslation (𝟙 _) g (by rw [hg, Category.id_comp])
  exact ⟨a, ha.trans (Category.id_comp _)⟩

/-- Every geometric point of `𝔸¹_k` lifts along the Artin–Schreier map `AS_q`: the equation
`T ^ q - T = c` has a root in an algebraically closed field. -/
lemma exists_comp_artinSchreierMap_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ 𝔸¹[k]) : ∃ t : Spec (.of Ω) ⟶ 𝔸¹[k], t ≫ AS[k] = y := by
  set c := (Scheme.ΓSpecIso (.of Ω)).hom.hom
    (y.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
  have hlt : (Polynomial.X : Polynomial Ω).degree <
      ((Polynomial.X : Polynomial Ω) ^ Fintype.card k).degree := by
    rw [Polynomial.degree_X, Polynomial.degree_X_pow]
    exact_mod_cast Fintype.one_lt_card
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_root (Polynomial.X ^ Fintype.card k - Polynomial.X -
    Polynomial.C c) (by
      rw [Polynomial.degree_sub_C (by
        rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
        exact_mod_cast Fintype.card_pos)]
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt, Polynomial.degree_X_pow]
      exact_mod_cast Fintype.card_ne_zero)
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hd
  refine ⟨AffineSpace.homOfVector (y ≫ 𝔸¹[k] ↘ Spec (.of k))
    fun _ ↦ (Scheme.ΓSpecIso (.of Ω)).inv.hom d, AffineSpace.hom_ext ?_ fun _ ↦ ?_⟩
  · rw [Category.assoc, AffineSpace.artinSchreierMap_over, AffineSpace.homOfVector_over]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
      AffineSpace.homOfVector_appTop_coord, ← map_pow, ← map_sub, sub_eq_zero.mp hd]
    exact (Scheme.ΓSpecIso (.of Ω)).hom_inv_id_apply _

/-- The Artin–Schreier map `AS_q` is surjective. -/
lemma surjective_artinSchreierMap : Function.Surjective (AS[k]).base := by
  intro x
  obtain ⟨t, ht⟩ := exists_comp_artinSchreierMap_eq (𝔸¹[k].algClosurePoint x)
  refine ⟨t.base default, ?_⟩
  simpa using congrArg (fun g ↦ g.base default) ht

/-- The Artin–Schreier map `AS_q` is étale, `q` vanishing in `k`. -/
lemma etale_artinSchreierMap : Etale AS[k] :=
  AffineSpace.etale_artinSchreierMap PUnit (Spec (.of k)) (by
    rw [← map_natCast (Scheme.ΓSpecIso (.of k)).inv.hom, FiniteField.cast_card_eq_zero,
      map_zero])

instance : IsFinite AS[k] :=
  AffineSpace.isFinite_artinSchreierMap _ _ Fintype.one_lt_card.ne'

/-- The origin is fixed by the Artin–Schreier map: `0 ^ q - 0 = 0`. -/
lemma zeroSection_comp_artinSchreierMap :
    AffineSpace.zeroSection PUnit (Spec (.of k)) ≫ AS[k] =
      AffineSpace.zeroSection PUnit (Spec (.of k)) :=
  AffineSpace.hom_ext (by simp) fun _ ↦ by
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
      AffineSpace.zeroSection_appTop_coord, zero_pow Fintype.card_ne_zero, sub_zero]

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

/-- The unit `ε : Λ ⟶ (AS_q)_* Λ`, the constant functions, is invariant under the translations:
`ε ≫ σ_a = ε`. -/
@[reassoc (attr := simp)]
lemma ε_lowerStar_comp_artinSchreierTranslationAction (a : k) :
    Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
        artinSchreierTranslationAction Λ k a =
      Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] := by
  rw [artinSchreierTranslationAction, lowerStarConstantSheafEndOfOver_eq]
  conv_rhs => rw [ε_lowerStar_comp (artinSchreierTranslation k a) AS[k] AS[k]
      (artinSchreierTranslation_comp_artinSchreierMap k a).symm]

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
(sketch blueprint: `sk-def-as`; blueprint: `def-fd-artin-schreier-sheaf`) -/
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

/-- Each `σ_b` acts on `ℒ_Ψ ⊆ (AS_q)_* Λ` by the scalar `Ψ(b)`: `s_Ψ ≫ σ_b = Ψ(b) • s_Ψ`. -/
lemma image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction
    (Ψ : AddChar k Λ) (b : k) :
    image.ι (artinSchreierIdempotent Ψ) ≫ artinSchreierTranslationAction Λ k b =
      Ψ b • image.ι (artinSchreierIdempotent Ψ) := by
  rw [← cancel_epi (factorThruImage (artinSchreierIdempotent Ψ)), image.fac_assoc,
    Linear.comp_smul, image.fac, artinSchreierIdempotent_comp_artinSchreierTranslationAction]

/-- The Artin–Schreier sheaf `ℒ_{Ψ, f} := f^* ℒ_Ψ` of a global function `f` on a `k`-scheme
`X`, where `f` is viewed as a morphism `X ⟶ 𝔸¹_k`. The variants `ℒ_{ψ⁻¹, f}` and
`ℒ_{ψ(a f)}` of the blueprint are `artinSchreierSheafOf X Ψ⁻¹ f` and
`artinSchreierSheafOf X Ψ (a • f)`.
(sketch blueprint: `sk-def-as`; blueprint: `def-fd-artin-schreier-sheaf`) -/
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
instance invertible_card_ulift_zmod {p : ℕ} [NeZero p] [Invertible (p : Λ)] :
    Invertible (Fintype.card (ULift.{u} (ZMod p)) : Λ) :=
  ‹Invertible (p : Λ)›.copy _ (by rw [Fintype.card_ulift, ZMod.card])

/-- For a scheme `X` of characteristic `p`, the Artin–Schreier sheaf `ℒ_{Ψ, f}` of a global
function `f` and an additive character `Ψ` of `ℤ/p`, where `X` is viewed as a scheme over
`𝔽_p` by `AlgebraicGeometry.Scheme.overSpecZModOfCharP`. This is the construction of the
blueprint definition `def-fd-artin-schreier-sheaf` (sketch blueprint: `sk-def-as`): the
`Ψ`-isotypic part, for a character `Ψ` of `𝔽_p`, of the Artin–Schreier covering
`T ^ p - T = f`. -/
def artinSchreierSheafZMod {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)] (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat Λ) :=
  letI := X.overSpecZModOfCharP p
  artinSchreierSheafOf X (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f

end ZMod

section Trivialization

/-! ### The Artin–Schreier sheaf becomes constant on the covering

The adjoint `AS_q^* ℒ_Ψ ⟶ Λ` of the inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` is an isomorphism. On the
stalk at a geometric point `t` of the source this is the restriction to `t` of the
`Ψ`-isotypic germs of functions on the geometric fibre through `t`, which is a `k`-torsor: a
`Ψ`-isotypic germ is determined by its value at `t`, and every value occurs. -/

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ 𝔸¹[k])

omit [Invertible (Fintype.card k : Λ)] in
/-- On the stalk at `y`, `σ_a` followed by the restriction to a point `t` of the geometric fibre
factors through the restriction to `t ≫ σ_a`. -/
lemma exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict (a : k)
    (t t' : Scheme.Hom.GeometricFiber AS[k] y) (h : t'.1 = t.1 ≫ artinSchreierTranslation k a) :
    ∃ θ, (Scheme.pointSmallEtale y).sheafFiber.map (artinSchreierTranslationAction Λ k a) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t (𝟙_ _) =
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t' (𝟙_ _) ≫ θ := by
  obtain ⟨t', ht'⟩ := t'
  subst h
  exact ⟨_, Etale.sheafFiber_map_lowerStarConstantSheafEndOfOver_stalkRestrict _ _ _ y t⟩

/-- At a geometric point `y` of `𝔸¹_k` and a geometric point `s` of `𝔸¹_k` over `y`, the
inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` followed by the restriction of germs to `s` is an
isomorphism `(ℒ_Ψ)_y ≅ Λ_s`. -/
theorem isIso_sheafFiber_map_image_ι_comp_stalkRestrict (Ψ : AddChar k Λ)
    (s : Scheme.Hom.GeometricFiber AS[k] y) :
    IsIso ((Scheme.pointSmallEtale y).sheafFiber.map (image.ι (artinSchreierIdempotent Ψ)) ≫
      Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y s (𝟙_ _)) := by
  classical
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have := (Scheme.pointSmallEtale y).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  set ρ := fun t : Scheme.Hom.GeometricFiber AS[k] y ↦
    Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] y t (𝟙_ _) with hρ
  set ι := image.ι (artinSchreierIdempotent Ψ)
  set r := factorThruImage (artinSchreierIdempotent Ψ)
  have hι (b : k) : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map (artinSchreierTranslationAction Λ k b) =
        Ψ b • (Scheme.pointSmallEtale y).sheafFiber.map ι := by
    rw [← CategoryTheory.Functor.map_comp,
      image_ι_artinSchreierIdempotent_comp_artinSchreierTranslationAction,
      GrothendieckTopology.Point.sheafFiber_map_smul]
  have hιr : (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
      (Scheme.pointSmallEtale y).sheafFiber.map r = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, image_ι_comp_factorThruImage_artinSchreierIdempotent,
      CategoryTheory.Functor.map_id]
  -- a germ in `ℒ_Ψ` vanishing at `s` vanishes at every point `s ≫ σ_a` of the fibre
  have hmono : Mono ((Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ s) := by
    refine Preadditive.mono_of_cancel_zero _ fun {Z} u hu ↦ ?_
    have h1 : u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι = 0 := by
      rw [← cancel_mono (Pi.lift ρ), zero_comp]
      refine Pi.hom_ext _ _ fun t ↦ ?_
      rw [Category.assoc, Pi.lift_π, zero_comp]
      obtain ⟨a, ha⟩ := exists_eq_comp_artinSchreierTranslation s.1 t.1 (by rw [s.2, t.2])
      obtain ⟨θ, hθ⟩ := exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict
        (Λ := Λ) y (-a) t s (by rw [ha, Category.assoc, ← artinSchreierTranslation_add,
          add_neg_cancel, artinSchreierTranslation_zero, Category.comp_id])
      have h2 : Ψ (-a) • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) = 0 := by
        rw [← Linear.comp_smul, ← Linear.smul_comp, ← hι, Category.assoc, hθ]
        simp only [← Category.assoc] at hu ⊢
        rw [hu, zero_comp]
      have h3 : Ψ a • Ψ (-a) • (u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t) =
          u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ t := by
        rw [smul_smul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
          one_smul]
      rw [Category.assoc, ← h3, h2, smul_zero]
    calc u = u ≫ (Scheme.pointSmallEtale y).sheafFiber.map ι ≫
          (Scheme.pointSmallEtale y).sheafFiber.map r := by rw [hιr, Category.comp_id]
      _ = 0 := by rw [← Category.assoc, h1, zero_comp]
  -- `q • e_Ψ` applied to the germ supported at `s` with value `λ` has value `λ` at `s`
  have hepi : IsSplitEpi ((Scheme.pointSmallEtale y).sheafFiber.map ι ≫ ρ s) := by
    let j : (Scheme.pointSmallEtale s.1).sheafFiber.obj (𝟙_ (Sheaf 𝔸¹[k].smallEtaleTopology
        (ModuleCat.{u + 1} Λ))) ⟶ (Scheme.pointSmallEtale y).sheafFiber.obj 𝒫[Λ, k] :=
      Pi.lift (fun t ↦ if h : t = s then eqToHom (by rw [h]) else 0) ≫ inv (Pi.lift ρ)
    have hj (t) : j ≫ ρ t = if h : t = s then eqToHom (by rw [h]) else 0 := by
      have : inv (Pi.lift ρ) ≫ ρ t = Pi.π _ t := by rw [IsIso.inv_comp_eq, Pi.lift_π]
      simp only [j, Category.assoc]
      rw [this, Pi.lift_π]
    refine ⟨⟨(Fintype.card k : Λ) • (j ≫ (Scheme.pointSmallEtale y).sheafFiber.map r), ?_⟩⟩
    rw [Linear.smul_comp, Category.assoc,
      ← Category.assoc ((Scheme.pointSmallEtale y).sheafFiber.map r),
      ← CategoryTheory.Functor.map_comp, image.fac, artinSchreierIdempotent, Functor.map_sum]
    simp only [GrothendieckTopology.Point.sheafFiber_map_smul, Preadditive.sum_comp,
      Preadditive.comp_sum, Linear.smul_comp, Linear.comp_smul]
    rw [Finset.sum_eq_single (0 : k)]
    · rw [artinSchreierTranslationAction_zero, CategoryTheory.Functor.map_id, Category.id_comp]
      erw [hj s]
      rw [dif_pos rfl, eqToHom_refl, neg_zero, AddChar.map_zero_eq_one, mul_one, smul_smul,
        mul_invOf_self, one_smul]
    · intro a _ ha
      obtain ⟨θ, hθ⟩ := exists_sheafFiber_map_artinSchreierTranslationAction_comp_stalkRestrict
        (Λ := Λ) y a s ⟨s.1 ≫ artinSchreierTranslation k a, by
          rw [Category.assoc, artinSchreierTranslation_comp_artinSchreierMap, s.2]⟩ rfl
      have hne : (⟨s.1 ≫ artinSchreierTranslation k a, by
          rw [Category.assoc, artinSchreierTranslation_comp_artinSchreierMap, s.2]⟩ :
            Scheme.Hom.GeometricFiber AS[k] y) ≠ s := fun h ↦
        ha (eq_zero_of_comp_artinSchreierTranslation_eq s.1 a (congrArg Subtype.val h))
      erw [hθ, ← Category.assoc, hj, dif_neg hne]
      rw [zero_comp, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  exact isIso_of_mono_of_isSplitEpi _

/-- The adjoint `AS_q^* ℒ_Ψ ⟶ Λ` of the inclusion `s_Ψ : ℒ_Ψ ⟶ (AS_q)_* Λ` is an isomorphism,
checked on the stalks at the geometric points of the source. -/
instance isIso_upperStar_map_image_ι_comp_counit (Ψ : AddChar k Λ) :
    IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _)) := by
  refine Scheme.isIso_of_isIso_sheafFiber_map _ fun s ↦ ?_
  rw [Scheme.uliftPointSmallEtale, NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale _).uliftSheafFiberIso (ModuleCat.{u + 1} Λ))]
  set s' := 𝔸¹[k].algClosurePoint s
  have h1 := Etale.stalkRestrict_eq_counit (ModuleCat.{u + 1} Λ) AS[k] s' (𝟙_ _)
  have h2 := (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) AS[k] s').inv.naturality
    (image.ι (artinSchreierIdempotent Ψ))
  have h3 := isIso_sheafFiber_map_image_ι_comp_stalkRestrict (s' ≫ AS[k]) Ψ ⟨s', rfl⟩
  have h4 : (Scheme.pointSmallEtale s').sheafFiber.map
      ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _)) =
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) AS[k] s').hom.app _ ≫
        ((Scheme.pointSmallEtale (s' ≫ AS[k])).sheafFiber.map
          (image.ι (artinSchreierIdempotent Ψ)) ≫
        Etale.stalkRestrict (ModuleCat.{u + 1} Λ) AS[k] (s' ≫ AS[k]) ⟨s', rfl⟩ (𝟙_ _)) := by
    rw [h1, CategoryTheory.Functor.map_comp,
      ← Category.assoc ((Scheme.pointSmallEtale _).sheafFiber.map _), h2]
    simp
  rw [h4]
  infer_instance

/-- **The Artin–Schreier sheaf is trivialized by the Artin–Schreier covering**:
`AS_q^* ℒ_Ψ ≅ Λ`, the adjoint of the inclusion `ℒ_Ψ ⟶ (AS_q)_* Λ`. In particular `ℒ_Ψ` is lisse
of rank one: it becomes the constant sheaf `Λ` on the finite étale covering `AS_q`.
(blueprint: `lem-fd-as-characters`, rank one) -/
def artinSchreierSheafUpperStarIso (Ψ : AddChar k Λ) :
    (AS[k])^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf Ψ) ≅ 𝟙_ _ :=
  asIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _))

@[simp]
lemma artinSchreierSheafUpperStarIso_hom (Ψ : AddChar k Λ) :
    (artinSchreierSheafUpperStarIso Ψ).hom =
      (AS[k])^*[ModuleCat.{u + 1} Λ].map (image.ι (artinSchreierIdempotent Ψ)) ≫
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) AS[k]).counit.app (𝟙_ _) :=
  rfl

omit [Invertible (Fintype.card k : Λ)] in
variable (Λ) in
/-- A morphism of étale sheaves on `𝔸¹_k` is an isomorphism as soon as its pullback along the
surjective Artin–Schreier map is. -/
lemma isIso_of_isIso_upperStar_map_artinSchreierMap
    {F G : Sheaf 𝔸¹[k].smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : F ⟶ G)
    [IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map φ)] : IsIso φ :=
  have := Etale.reflectsIsomorphisms_upperStar_of_surjective Λ AS[k] surjective_artinSchreierMap
  isIso_of_reflects_iso φ (AS[k])^*[ModuleCat.{u + 1} Λ]

end Trivialization

section Properties

variable {k : Type u} [Field k] [Fintype k] [Invertible (Fintype.card k : Λ)]

/-- The Artin–Schreier sheaf is lisse: it is trivialized by the finite étale surjective
covering `AS_q` (`AlgebraicGeometry.Etale.artinSchreierSheafUpperStarIso`).
(sketch blueprint: `sk-lem-as-properties`; blueprint: `lem-fd-as-lisse`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar k Λ) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf Ψ) := by
  have := etale_artinSchreierMap (k := k)
  refine ⟨⟨⟨.singleton AS[k] ((Scheme.singleton_mem_precoverage_iff (P := @Etale) _).2
    ⟨surjective_artinSchreierMap, inferInstance⟩), fun _ ↦ ?_⟩⟩⟩
  rw [Scheme.isConstant_over_iff_upperStar]
  exact Sheaf.isConstant_of_iso _ (X := 𝟙_ (ModuleCat.{u + 1} Λ))
    (artinSchreierSheafUpperStarIso Ψ ≪≫
      Functor.Monoidal.εIso (presheafToSheaf _ (ModuleCat.{u + 1} Λ)))

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
  -- the zero section factors through `AS_q`, which trivializes `ℒ_Ψ`
  ⟨Functor.Monoidal.εIso _ ≪≫
    (AffineSpace.zeroSection PUnit (Spec (.of k)))^*[ModuleCat Λ].mapIso
      (artinSchreierSheafUpperStarIso Ψ).symm ≪≫
    ((upperStarComp _ _ _ _ zeroSection_comp_artinSchreierMap.symm).app _).symm⟩

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
    Nonempty (artinSchreierSheaf (1 : AddChar k Λ) ≅ 𝟙_ _) := by
  -- the constant functions `ε : Λ ⟶ (AS_q)_* Λ` are invariant, so they land in `ℒ_1`, and the
  -- adjoint of the resulting map `Λ ⟶ ℒ_1` is the isomorphism `AS_q^* Λ ≅ Λ`
  have hε : Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
      artinSchreierIdempotent (1 : AddChar k Λ) =
        Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] := by
    simp only [artinSchreierIdempotent, Preadditive.comp_sum, Linear.comp_smul,
      ε_lowerStar_comp_artinSchreierTranslationAction, AddChar.one_apply, mul_one,
      Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul Λ, smul_smul,
      mul_invOf_self, one_smul]
  set v := Functor.LaxMonoidal.ε (AS[k])_*[ModuleCat.{u + 1} Λ] ≫
    factorThruImage (artinSchreierIdempotent (1 : AddChar k Λ))
  have hv : (AS[k])^*[ModuleCat.{u + 1} Λ].map v ≫ (artinSchreierSheafUpperStarIso 1).hom =
      Functor.OplaxMonoidal.η (AS[k])^*[ModuleCat.{u + 1} Λ] := by
    rw [artinSchreierSheafUpperStarIso_hom, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, Category.assoc, image.fac, hε,
      Adjunction.map_ε_comp_counit_app_unit]
  have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v) := by
    have : IsIso ((AS[k])^*[ModuleCat.{u + 1} Λ].map v ≫
        (artinSchreierSheafUpperStarIso 1).hom) := by
      rw [hv]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (artinSchreierSheafUpperStarIso 1).hom
  have := isIso_of_isIso_upperStar_map_artinSchreierMap Λ v
  exact ⟨(asIso v).symm⟩

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
    (X ↘ Spec (.of k))^*[ModuleCat Λ].mapIso e.symm ≪≫ (Functor.Monoidal.εIso _).symm⟩

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
  exact ⟨Functor.mapIso _ e ≪≫ (Functor.Monoidal.εIso _).symm⟩

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
