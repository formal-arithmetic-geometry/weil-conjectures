/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Finite.BaseChange

/-!

# The Artin–Schreier sheaf

Let `k` be a finite field with `q` elements, let `X` be a scheme over `k`, let `Ψ` be an
additive character of `k` with values in a coefficient ring `Λ` in which `q` is invertible and
let `f ∈ Γ(X, 𝒪_X)`. The *Artin–Schreier covering* attached to `f` is the finite étale
`k`-torsor `π : Y = Spec_X 𝒪_X[T]/(T^q - T - f) ⟶ X`, and the *Artin–Schreier sheaf*
`ℒ_{Ψ, f} := e_Ψ π_* Λ` is the `Ψ`-isotypic component of its pushforward, cut out by the
idempotent `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a`. It is a lisse sheaf of rank one, that is, an
invertible object of the category of étale sheaves; it turns addition of functions into
tensor product of sheaves, and multiplication of characters likewise. The classical case is
`k = ℤ/p`.

## Main definitions

- `AlgebraicGeometry.Scheme.artinSchreierCover`: the Artin–Schreier covering `Y` of `X`, the
  pullback of the Artin–Schreier map `T ↦ T^q - T` of the affine line along `f : X ⟶ 𝔸¹_k`,
  with its projection `AlgebraicGeometry.Scheme.artinSchreierCoverπ` and the action
  `AlgebraicGeometry.Scheme.artinSchreierAction` of `a ∈ k` by `T ↦ T + a`.
- `AlgebraicGeometry.Etale.artinSchreierIdempotent`: the endomorphism
  `e_Ψ = q⁻¹ ∑_a Ψ(-a) σ_a` of `π_* Λ`.
- `AlgebraicGeometry.Etale.artinSchreierSheaf`: the Artin–Schreier sheaf `ℒ_{Ψ, f}`, the image
  of `e_Ψ`.
- `AlgebraicGeometry.Etale.artinSchreierSheafPullbackIso`: for a `k`-morphism `g : X' ⟶ X`,
  `g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`.

## Main statements

- `AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf`: `ℒ_{Ψ, f}` is lisse.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_add`:
  `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_zero`: `ℒ_{Ψ, 0} ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_mul`:
  `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_one`: `ℒ_{1, f} ≅ Λ`.
- `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg` and
  `AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_inv`: the two inversion formulas
  `ℒ_{Ψ, f} ⊗ ℒ_{Ψ, -f} ≅ Λ` and `ℒ_{Ψ, f} ⊗ ℒ_{Ψ⁻¹, f} ≅ Λ`, corollaries of the four
  statements above.

## Blueprint

The `sk-*` labels quoted below are block names of the *sketch* blueprint, a separate
repository; they are not labels of `blueprint/src` and so are not checked by the build.

The subsection `sk-lem-as-properties` also contains the decomposition `π_* Λ ≅ ⨁_χ ℒ_χ` of the
pushforward, the trace function of `ℒ_{Ψ, a f}` and the cohomology of the affine line with
coefficients in `ℒ_{Ψ, a x}`. Those are deferred: they are the inputs to the *proofs* of the
statements of this block.

## Implementation notes

`q` is required to be invertible in `Λ` throughout: the idempotent `e_Ψ` that defines
`ℒ_{Ψ, f}` is `q⁻¹ ∑_a Ψ(-a) σ_a`, and without it the pushforward `π_* Λ` has no isotypic
decomposition — for `Λ = ℤ/p` every statement below is false.

The action of `σ_a` on `π_* Λ` is `π_*` of the unit `Λ ⟶ (σ_a)_* (σ_a)^* Λ ≅ (σ_a)_* Λ` of the
adjunction `σ_a^* ⊣ (σ_a)_*`, followed by `π_* (σ_a)_* = (σ_a ≫ π)_* = π_*`. The constant sheaf
`Λ` is written `(constantSheaf _ _).obj (ModuleCat.of Λ Λ)` rather than as the monoidal unit,
since the pullback of constant sheaves `AlgebraicGeometry.Scheme.upperStarConstantSheafIso` is
stated for `constantSheaf`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

/-- Over a scheme `X` over a finite field `k`, translation by `a ∈ k` leaves the Artin–Schreier
map `T ↦ T ^ #k - T` of the affine line `𝔸¹_X` invariant, since `a ^ #k = a`. -/
@[reassoc (attr := simp)]
lemma AffineSpace.translation_algebraMap_comp_artinSchreierMap (k : Type*) [Field k] [Fintype k]
    (X : Scheme.{u}) [Algebra k Γ(X, ⊤)] (a : k) :
    AffineSpace.translation (fun _ : PUnit.{u + 1} ↦ algebraMap k Γ(X, ⊤) a) ≫
      AffineSpace.artinSchreierMap PUnit.{u + 1} X (Fintype.card k) =
      AffineSpace.artinSchreierMap PUnit.{u + 1} X (Fintype.card k) := by
  obtain ⟨m, hp, hm⟩ := FiniteField.card k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hp⟩
  rw [hm]
  refine AffineSpace.translation_comp_artinSchreierMap ?_ _ _ fun _ ↦ ?_
  · rw [← map_natCast (algebraMap k Γ(X, ⊤)), ringChar.Nat.cast_ringChar, map_zero]
  · rw [← map_pow, ← hm, FiniteField.pow_card]

namespace Scheme

section Cover

variable (k : Type*) [Field k] [Fintype k] (X : Scheme.{u})

/-- A global function `f` on a scheme `X`, as a section `X ⟶ 𝔸¹_X` of the affine line. -/
def artinSchreierCoverMap (f : Γ(X, ⊤)) : X ⟶ 𝔸(PUnit.{u + 1}; X) :=
  AffineSpace.homOfVector (𝟙 X) fun _ ↦ f

/-- The *Artin–Schreier covering* `Y = Spec_X 𝒪_X[T]/(T^q - T - f)` of `X` attached to a global
function `f`, where `q = #k`: the pullback of the Artin–Schreier map `T ↦ T^q - T` of `𝔸¹_X`
along the section `f : X ⟶ 𝔸¹_X`. -/
def artinSchreierCover (f : Γ(X, ⊤)) : Scheme.{u} :=
  pullback (X.artinSchreierCoverMap f)
    (AffineSpace.artinSchreierMap PUnit.{u + 1} X (Fintype.card k))

/-- The projection `π : Y ⟶ X` of the Artin–Schreier covering. -/
def artinSchreierCoverπ (f : Γ(X, ⊤)) : X.artinSchreierCover k f ⟶ X :=
  pullback.fst _ _

/-- The Artin–Schreier covering is finite, being a base change of the finite map
`T ↦ T^q - T`. -/
instance isFinite_artinSchreierCoverπ (f : Γ(X, ⊤)) : IsFinite (X.artinSchreierCoverπ k f) :=
  have := AffineSpace.isFinite_artinSchreierMap X (Fintype.one_lt_card (α := k))
  isFinite_of_isPullback (IsPullback.of_hasPullback _ _).flip

variable {k X} {X' : Scheme.{u}} (g : X' ⟶ X)

@[reassoc]
lemma artinSchreierCoverMap_comp_map (f : Γ(X, ⊤)) :
    X'.artinSchreierCoverMap (g.appTop f) ≫ AffineSpace.map PUnit.{u + 1} g =
      g ≫ X.artinSchreierCoverMap f := by
  refine AffineSpace.hom_ext (by simp [artinSchreierCoverMap]) fun _ ↦ ?_
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord,
    artinSchreierCoverMap, AffineSpace.homOfVector_appTop_coord]

/-- For a morphism `g : X' ⟶ X`, the morphism from the Artin–Schreier covering of `g^* f` to that
of `f` over `g`. -/
def artinSchreierCoverMapOfHom (f : Γ(X, ⊤)) :
    X'.artinSchreierCover k (g.appTop f) ⟶ X.artinSchreierCover k f :=
  pullback.map _ _ _ _ g (AffineSpace.map _ g) (AffineSpace.map _ g)
    (artinSchreierCoverMap_comp_map g f) (AffineSpace.map_comp_artinSchreierMap g _).symm

omit [Field k] in
/-- The Artin–Schreier covering of `g^* f` is the base change along `g` of that of `f`. -/
lemma isPullback_artinSchreierCoverMapOfHom (f : Γ(X, ⊤)) :
    IsPullback (artinSchreierCoverMapOfHom (k := k) g f) (X'.artinSchreierCoverπ k (g.appTop f))
      (X.artinSchreierCoverπ k f) g := by
  have e : artinSchreierCoverMapOfHom (k := k) g f ≫ pullback.snd (X.artinSchreierCoverMap f)
      (AffineSpace.artinSchreierMap PUnit.{u + 1} X (Fintype.card k)) =
      pullback.snd (X'.artinSchreierCoverMap (g.appTop f))
        (AffineSpace.artinSchreierMap PUnit.{u + 1} X' (Fintype.card k)) ≫
        AffineSpace.map _ g :=
    pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback _ _).flip
  rw [e, ← artinSchreierCoverMap_comp_map]
  exact (IsPullback.of_hasPullback _ _).flip.paste_horiz
    (AffineSpace.isPullback_map_artinSchreierMap g _)

variable (k X)

variable [Algebra k Γ(X, ⊤)]

/-- The action `σ_a : T ↦ T + a` of `a ∈ k` on the Artin–Schreier covering, the base change of
the translation by `a` of `𝔸¹_X`, which leaves `T ↦ T^q - T` invariant. -/
def artinSchreierAction (f : Γ(X, ⊤)) (a : k) :
    X.artinSchreierCover k f ⟶ X.artinSchreierCover k f :=
  pullback.map _ _ _ _ (𝟙 X) (AffineSpace.translation fun _ ↦ algebraMap k Γ(X, ⊤) a) (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma artinSchreierAction_π (f : Γ(X, ⊤)) (a : k) :
    X.artinSchreierAction k f a ≫ X.artinSchreierCoverπ k f = X.artinSchreierCoverπ k f :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

end Cover

end Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ]

variable (Λ) in
/-- The constant sheaf `Λ` on the small étale site of `Y`. -/
abbrev constantSheafUnit (Y : Scheme.{u}) : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (constantSheaf _ _).obj (ModuleCat.of Λ Λ)

section Construction

variable (k : Type*) [Field k] [Fintype k] (X : Scheme.{u}) [Algebra k Γ(X, ⊤)]

/-- The action of `σ_a` on the pushforward `π_* Λ` along the Artin–Schreier covering: `π_*` of
the unit `Λ ⟶ (σ_a)_* (σ_a)^* Λ ≅ (σ_a)_* Λ`, followed by `π_* (σ_a)_* ≅ (σ_a ≫ π)_* = π_*`. -/
def artinSchreierActionPushforward (f : Γ(X, ⊤)) (a : k) :
    (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].obj (constantSheafUnit Λ _) ⟶
      (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].obj (constantSheafUnit Λ _) :=
  (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].map
      ((Etale.upperStarLowerStarAdjunction _ (X.artinSchreierAction k f a)).unit.app _ ≫
        (X.artinSchreierAction k f a)_*[ModuleCat.{u + 1} Λ].map
          ((Scheme.upperStarConstantSheafIso _ (X.artinSchreierAction k f a)).hom.app
            (ModuleCat.of Λ Λ))) ≫
    (Etale.lowerStarComp _ (X.artinSchreierAction k f a) (X.artinSchreierCoverπ k f)
      (X.artinSchreierCoverπ k f) (by simp)).hom.app _

variable [Invertible (Fintype.card k : Λ)]

/-- The idempotent `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a` of `π_* Λ` cutting out the `Ψ`-isotypic
component, where `π` is the Artin–Schreier covering of `f` and `q = #k`. -/
def artinSchreierIdempotent (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].obj (constantSheafUnit Λ _) ⟶
      (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].obj (constantSheafUnit Λ _) :=
  ∑ a : k, (X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].map
      ((constantSheaf _ _).map
        (ModuleCat.ofHom ((⅟(Fintype.card k : Λ) * Ψ (-a)) • LinearMap.id))) ≫
    artinSchreierActionPushforward k X f a

/-- For a scheme `X` over a finite field `k` with `q` elements and a global function
`f ∈ Γ(X, 𝒪_X)`, the Artin–Schreier covering `π : Y = Spec_X 𝒪_X[T]/(T^q - T - f) ⟶ X` is
finite étale of degree `q` with automorphism group `k` acting by `σ_a : T ↦ T + a`. The
*Artin–Schreier sheaf* `ℒ_{Ψ, f}` is the `Ψ`-isotypic component `e_Ψ π_* Λ` of the pushforward
of the constant sheaf, where `e_Ψ = q⁻¹ ∑_{a ∈ k} Ψ(-a) σ_a`; equivalently, the subsheaf on
which each `σ_a` acts by `Ψ(a)`. It is defined as the image of `e_Ψ`.
(sketch blueprint: `sk-def-as`) -/
def artinSchreierSheaf (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  Limits.image (artinSchreierIdempotent k X Ψ f)

end Construction

section Pullback

variable (k : Type*) [Field k] [Fintype k] {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- For a morphism `g : X' ⟶ X`, the finite base change isomorphism
`g^* π_* Λ ≅ π'_* g'^* Λ ≅ π'_* Λ` between the pushforwards of the constant sheaf along the
Artin–Schreier coverings of `f` and of `g^* f`. -/
def artinSchreierPushforwardPullbackIso (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat.{u + 1} Λ].obj
        ((X.artinSchreierCoverπ k f)_*[ModuleCat.{u + 1} Λ].obj (constantSheafUnit Λ _)) ≅
      (X'.artinSchreierCoverπ k (g.appTop f))_*[ModuleCat.{u + 1} Λ].obj
        (constantSheafUnit Λ _) :=
  have := Etale.isIso_baseChangeMap_of_isFinite (ModuleCat.{u + 1} Λ)
    (Scheme.isPullback_artinSchreierCoverMapOfHom (k := k) g f)
  (asIso (Etale.baseChangeMap _
      (Scheme.isPullback_artinSchreierCoverMapOfHom (k := k) g f).toCommSq)).app _ ≪≫
    (X'.artinSchreierCoverπ k (g.appTop f))_*[ModuleCat.{u + 1} Λ].mapIso
      ((Scheme.upperStarConstantSheafIso _ _).app (ModuleCat.of Λ Λ))

variable {k} [Algebra k Γ(X, ⊤)] [Algebra k Γ(X', ⊤)]
  (hg : g.appTop.hom.comp (algebraMap k Γ(X, ⊤)) = algebraMap k Γ(X', ⊤))
  [Invertible (Fintype.card k : Λ)]

include hg in
/-- For a `k`-morphism `g`, the base change isomorphism `g^* π_* Λ ≅ π'_* Λ` intertwines the
idempotents `g^* e_Ψ` and `e_Ψ`: it intertwines the actions of `σ_a` on both sides. -/
lemma artinSchreierPushforwardPullbackIso_hom_comp (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat.{u + 1} Λ].map (artinSchreierIdempotent k X Ψ f) ≫
        (artinSchreierPushforwardPullbackIso k g f).hom =
      (artinSchreierPushforwardPullbackIso k g f).hom ≫
        artinSchreierIdempotent k X' Ψ (g.appTop f) :=
  sorry

/-- The Artin–Schreier sheaf is compatible with pullback: for a `k`-morphism `g : X' ⟶ X`,
`g^* ℒ_{Ψ, f} ≅ ℒ_{Ψ, g^* f}`. The Artin–Schreier covering of `g^* f` is the base change of that
of `f`, the finite base change map `g^* π_* ⟶ π'_* g'^*` is an isomorphism intertwining the
idempotents, and the exact functor `g^*` preserves images. -/
def artinSchreierSheafPullbackIso (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    (g)^*[ModuleCat.{u + 1} Λ].obj (artinSchreierSheaf k X Ψ f) ≅
      artinSchreierSheaf k X' Ψ (g.appTop f) :=
  (PreservesImage.iso _ _).symm ≪≫
    image.compIso _ (artinSchreierPushforwardPullbackIso k g f).hom ≪≫
    image.eqToIso (artinSchreierPushforwardPullbackIso_hom_comp g hg Ψ f) ≪≫
    @asIso _ _ _ _ _ (image.isIso_precomp_iso _ _)

end Pullback

section Properties

variable (k : Type*) [Field k] [Fintype k] {Λ : Type (u + 1)} [CommRing Λ]
  [Invertible (Fintype.card k : Λ)] (X : Scheme.{u}) [Algebra k Γ(X, ⊤)]

/-- The Artin–Schreier sheaf of the zero function is the constant sheaf `Λ`. Together with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_add` this says that `ℒ_{Ψ, f}` is an
invertible object of the category of étale sheaves — a lisse sheaf of rank one — with
inverse `ℒ_{Ψ, -f}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_zero (Ψ : AddChar k Λ) :
    Nonempty (artinSchreierSheaf k X Ψ 0 ≅ 𝟙_ _) :=
  sorry

/-- The Artin–Schreier sheaf of the trivial character is the constant sheaf `Λ`: the
`1`-isotypic component of `π_* Λ` is the sheaf of `k`-invariants, which is `Λ` because `π`
is a `k`-torsor.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_one (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheaf k X (1 : AddChar k Λ) f ≅ 𝟙_ _) :=
  sorry

variable {X}

/-- The Artin–Schreier sheaf is lisse: the covering is finite étale of degree `q`, so its
pushforward decomposes as `π_* Λ ≅ ⨁_{χ} ℒ_χ` over the characters of `k`, each summand
being locally constant of rank one.
(sketch blueprint: `sk-lem-as-properties`) -/
instance isLocallyConstantSheaf_artinSchreierSheaf (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Scheme.IsLocallyConstantSheaf (artinSchreierSheaf k X Ψ f) :=
  sorry

/-- The Artin–Schreier sheaf turns addition of functions into tensor product of sheaves,
`ℒ_{Ψ, f} ⊗ ℒ_{Ψ, g} ≅ ℒ_{Ψ, f + g}`.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_add (Ψ : AddChar k Λ) (f g : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheaf k X Ψ f ⊗ artinSchreierSheaf k X Ψ g ≅
      artinSchreierSheaf k X Ψ (f + g)) :=
  sorry

/-- The Artin–Schreier sheaf turns multiplication of characters into tensor product of
sheaves, `ℒ_{Ψ, f} ⊗ ℒ_{Ψ', f} ≅ ℒ_{Ψ Ψ', f}`: both sides are isotypic components of the
pushforward along the same covering.
(sketch blueprint: `sk-lem-as-properties`) -/
theorem nonempty_iso_artinSchreierSheaf_mul (Ψ Ψ' : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheaf k X Ψ f ⊗ artinSchreierSheaf k X Ψ' f ≅
      artinSchreierSheaf k X (Ψ * Ψ') f) :=
  sorry

/-- The inverse of `ℒ_{Ψ, f}` is `ℒ_{Ψ, -f}`. -/
theorem nonempty_iso_artinSchreierSheaf_neg (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheaf k X Ψ f ⊗ artinSchreierSheaf k X Ψ (-f) ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_add k Ψ f (-f)
  obtain ⟨e₀⟩ := nonempty_iso_artinSchreierSheaf_zero k X Ψ
  exact ⟨e ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫ e₀⟩

/-- The inverse of `ℒ_{Ψ, f}` is also `ℒ_{Ψ⁻¹, f}`; combined with
`AlgebraicGeometry.Etale.nonempty_iso_artinSchreierSheaf_neg` this is the identification
`ℒ_{Ψ, -f} ≅ ℒ_{Ψ⁻¹, f}` used for the kernel of the Fourier transform attached to the
inverse character. -/
theorem nonempty_iso_artinSchreierSheaf_inv (Ψ : AddChar k Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheaf k X Ψ f ⊗ artinSchreierSheaf k X Ψ⁻¹ f ≅ 𝟙_ _) := by
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheaf_mul k Ψ Ψ⁻¹ f
  obtain ⟨e₁⟩ := nonempty_iso_artinSchreierSheaf_one k X (Λ := Λ) f
  exact ⟨e ≪≫ eqToIso (by rw [mul_inv_cancel]) ≪≫ e₁⟩

end Properties

end Etale

end AlgebraicGeometry
