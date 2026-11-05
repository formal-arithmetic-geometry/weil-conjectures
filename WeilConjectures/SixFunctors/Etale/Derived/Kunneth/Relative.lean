/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
public import WeilConjectures.SixFunctors.Etale.Derived.Supports
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap

/-!

# The relative product theorem on the étale site

The ordinary Künneth formula with an identity factor, the relative product theorem for `Rf_!`
and its variants for complexes supported on closed subschemes, for the external product
`AlgebraicGeometry.Etale.externalProduct`.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedLowerStar`
  (`sk-lem-sf-kunneth-star`, `lem-trf-ordinary-kunneth`): `Rf_* M ⊠ Q ≅ R(f × id_Z)_* (M ⊠ Q)`
  over a field, for a finite coefficient ring of invertible exponent.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct`
  (`sk-thm-sf-kunneth-relative`): `R(f ×_B g)_! (K ⊠ M) ≅ Rf_! K ⊗ᴸ Rg_! M`.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_externalProduct`:
  `L(i ×_B j)^* (K ⊠ L) ≅ Li^* K ⊠ Lj^* L`.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_closedImmersion`:
  `(i ×_B j)_* (i ×_B j)^* (K ⊠ L) ≅ i_* i^* K ⊠ j_* j^* L` for closed immersions `i`, `j`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_externalProduct_closedImmersion`
  (`sk-thm-sf-kunneth-relative`): the relative product theorem for complexes supported on closed
  subschemes.
- `AlgebraicGeometry.Etale.nonempty_iso_compactlySupported_externalProduct_closedImmersion`
  (`sk-thm-sf-kunneth-relative`): the Künneth formula for `RΓ_c(Z × W, -)` over a field.

See `WeilConjectures.SixFunctors.Etale.Derived.Kunneth` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {B X Y : Scheme.{u}}

/-- The square
```
  X ×_B Z --f × 𝟙--> Y ×_B Z
     |                  |
    pr                 pr
     v                  v
     X -------f-------> Y
```
is cartesian. -/
lemma isPullback_mapOverBaseRight_fst {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y) :
    IsPullback (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c) (pullback.fst b c)
      f :=
  .of_right (h₁₂ := pullback.snd b c) (h₂₂ := b) (v₁₃ := c)
    (by simpa using (IsPullback.of_hasPullback (f ≫ b) c).flip)
    (pullback.mapOverBaseRight_fst f b c) (IsPullback.of_hasPullback b c).flip

/-- The comparison map `Rf_* M ⊠ Q ⟶ R(f × 𝟙_Z)_* (M ⊠ Q)` of the ordinary Künneth formula
with an identity factor (`sk-lem-sf-kunneth-star`, `lem-trf-ordinary-kunneth`), for
`f : X ⟶ Y`, `b : Y ⟶ B`, `c : Z ⟶ B`, `M ∈ D(X_ét)` and `Q ∈ D(Z_ét)`.

Writing `p_Y, p'_Z` for the projections of `Y ×_B Z` and `p_X, p_Z` for those of `X ×_B Z`,
it is the composite

`p_Y^* Rf_* M ⊗ᴸ p'_Z^* Q ≅ p'_Z^* Q ⊗ᴸ p_Y^* Rf_* M
  ⟶ R(f × 𝟙)_* ((f × 𝟙)^* p'_Z^* Q ⊗ᴸ p_X^* M) ≅ R(f × 𝟙)_* (p_X^* M ⊗ᴸ p_Z^* Q)`

of the braiding of `⊗ᴸ` (`AlgebraicGeometry.Etale.derivedTensorBraiding`),
the base change map `AlgebraicGeometry.Etale.tensorBaseChangeMap` of `lem-kun-0f1n` for the
cartesian square `AlgebraicGeometry.Etale.isPullback_mapOverBaseRight_fst`, and the
composition isomorphism `(f × 𝟙)^* p'_Z^* ≅ p_Z^*` followed by the braiding again. -/
noncomputable def externalProductRightDerivedLowerStarMap [UpperStarPreservesFlat A]
    {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A)) :
    externalProduct A b c ((R((f)_*[A])).obj M) Q ⟶
      (R((pullback.mapOverBaseRight f b c)_*[A])).obj (externalProduct A (f ≫ b) c M Q) :=
  ((derivedTensorBraiding A (pullback b c)).hom.app _).app _ ≫
    tensorBaseChangeMap A (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c)
      (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w
      ((L((pullback.snd b c)^*[A])).obj Q) M ≫
    (R((pullback.mapOverBaseRight f b c)_*[A])).map
      (((derivedTensor A (pullback (f ≫ b) c)).map
          ((leftDerivedUpperStarComp A (pullback.mapOverBaseRight f b c) (pullback.snd b c)
            (pullback.snd (f ≫ b) c) (by simp)).inv.app Q)).app _ ≫
        ((derivedTensorBraiding A (pullback (f ≫ b) c)).hom.app _).app _)

/-- The comparison map `Rf_* M ⊠ Q ⟶ R(f × 𝟙_Z)_* (M ⊠ Q)` is an isomorphism as soon as the
base change map of `lem-kun-0f1n` it is built from is one. -/
lemma isIso_externalProductRightDerivedLowerStarMap [UpperStarPreservesFlat A]
    {Z : Scheme.{u}} (b : Y ⟶ B) (c : Z ⟶ B) (f : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology A))
    [IsIso (tensorBaseChangeMap A (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c)
      (pullback.fst b c) f (isPullback_mapOverBaseRight_fst b c f).w
      ((L((pullback.snd b c)^*[A])).obj Q) M)] :
    IsIso (externalProductRightDerivedLowerStarMap A b c f M Q) := by
  rw [externalProductRightDerivedLowerStarMap]
  infer_instance

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- Blueprint `sk-lem-sf-kunneth-star` (detailed node `lem-trf-ordinary-kunneth`): Ordinary
Künneth with an identity factor.

Let `k` be a field, `Λ` a finite coefficient ring whose exponent is invertible in `k` (for
instance the finite stage `A_{E,n}`), and let `f : X ⟶ Y` be a morphism of separated
finite-type `k`-schemes, where `Y` has structure morphism `b` and `X` is viewed over `k`
through `f ≫ b`. Let `c : Z ⟶ Spec k` be a further separated finite-type `k`-scheme, so that
`f` induces `f × 𝟙_Z` across the square

```
  X ×_k Z --f × 𝟙--> Y ×_k Z --pr--> Y
     |                  |            |
     |                  |            f
     v                  v            v
     Z ------c------> Spec k <--b--- Y
```

For `M` in `Dctf(X, Λ)` and `Q` in `Dctf(Z, Λ)` the canonical comparison

`Rf_* M ⊠ Q ⟶ R(f × id_Z)_* (M ⊠ Q)`

is an isomorphism. Here both external products are taken over `Spec k`. The hypotheses that `M`
and `Q` lie in `Dctf` are those of the blueprint; the proof (through
`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap`) does not use them.

The base has to be a field and the exponent of `Λ` invertible: over the base `𝔸¹_k`, with
`Z` the origin and `f` the inclusion of `𝔾_m`, the right-hand side vanishes while the
left-hand side is the stalk of `Rf_* Λ` at the origin; and for `Λ = 𝔽_p` in characteristic
`p` the Artin–Schreier cohomology of the affine line already defeats the formula. -/
theorem nonempty_iso_externalProduct_rightDerivedLowerStar (Λ : Type (u + 1)) [CommRing Λ]
    [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))] {Z : Scheme.{u}}
    (b : Y ⟶ Spec (.of k)) (c : Z ⟶ Spec (.of k)) (f : X ⟶ Y)
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {Q : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hM : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (_hQ : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z Q) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) b c
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj M) Q ≅
      (R((pullback.mapOverBaseRight f b c)_*[ModuleCat.{u + 1} Λ])).obj
        (externalProduct (ModuleCat.{u + 1} Λ) (f ≫ b) c M Q)) := by
  have := isIso_tensorBaseChangeMap Λ c b (f ≫ b) (pullback.snd b c) (pullback.fst b c)
    (pullback.mapOverBaseRight f b c) (pullback.fst (f ≫ b) c) f rfl
    (IsPullback.of_hasPullback b c).flip (isPullback_mapOverBaseRight_fst b c f) Q M
  have := isIso_externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f M Q
  exact ⟨asIso (externalProductRightDerivedLowerStarMap (ModuleCat.{u + 1} Λ) b c f M Q)⟩

end Etale

end AlgebraicGeometry
