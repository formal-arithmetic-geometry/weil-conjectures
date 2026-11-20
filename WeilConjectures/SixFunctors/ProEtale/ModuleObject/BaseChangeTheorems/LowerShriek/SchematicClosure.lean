/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!

# Passing to the schematic closure

Let `j : X ⟶ X̄` be an open immersion of separated `k`-schemes of finite type and let
`i : Z ⟶ X̄` be the schematic closure of `X` (the scheme-theoretic image of `j`), with
`j_Z : X ⟶ Z` the induced open immersion. Since `i` is a monomorphism, `X = i⁻¹(X)`, so the
square of `j_Z`, `j` and `i` is cartesian, and `i` is proper. The pushforward comparison of
`CompactificationIndependence` then gives, for bounded constructible `E`- and `ℚ̄_ℓ`-sheaves,

* `j_! K ≅ i_* j_{Z,!} K`, and
* `Rp_* j_! K ≅ R(i ≫ p)_* j_{Z,!} K` for every `p : X̄ ⟶ Y`.

This is blueprint `lemma-passing-schematic-closure`.

## Main definitions

- `AlgebraicGeometry.overImageι`, `AlgebraicGeometry.overToImage`: the scheme-theoretic image of
  a morphism of `S`-schemes, as morphisms of `Over S`.
- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekSchematicClosureIso`:
  `j_! ≅ j_{Z,!} ⋙ i_*` (blueprint `lemma-passing-schematic-closure--1`).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekSchematicClosureIso`:
  `j_! ⋙ Rp_* ≅ j_{Z,!} ⋙ R(i ≫ p)_*` (blueprint `lemma-passing-schematic-closure--2`).

Both come with `ContinuousMapRingObj` versions for the coefficient ring `E̲`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-! ### The scheme-theoretic image in the category over a scheme -/

section Over

variable {S : Scheme.{u}} {X Z : Over S} (j : X ⟶ Z)

/-- The scheme-theoretic image of a morphism `j : X ⟶ Z` of `S`-schemes, as an object of
`Over S`. -/
noncomputable def overImageObj : Over S :=
  Over.mk (j.left.imageι ≫ Z.hom)

/-- The closed immersion of the scheme-theoretic image of a morphism `j : X ⟶ Z` of
`S`-schemes, as a morphism of `Over S`. -/
noncomputable def overImageι : overImageObj j ⟶ Z :=
  Over.homMk j.left.imageι rfl

/-- The morphism from `X` to the scheme-theoretic image of a morphism `j : X ⟶ Z` of
`S`-schemes, as a morphism of `Over S`. -/
noncomputable def overToImage : X ⟶ overImageObj j :=
  Over.homMk j.left.toImage (by simp [overImageObj])

@[simp] lemma overImageι_left : (overImageι j).left = j.left.imageι := rfl

@[simp] lemma overToImage_left : (overToImage j).left = j.left.toImage := rfl

@[reassoc (attr := simp)]
lemma overToImage_overImageι : overToImage j ≫ overImageι j = j := by
  ext1
  simp

instance : IsClosedImmersion (overImageι j).left :=
  inferInstanceAs (IsClosedImmersion j.left.imageι)

instance : Mono (overImageι j) :=
  (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono j.left.imageι))

instance [LocallyOfFiniteType Z.hom] : LocallyOfFiniteType (overImageObj j).hom :=
  inferInstanceAs (LocallyOfFiniteType (j.left.imageι ≫ Z.hom))

instance [QuasiCompact Z.hom] : QuasiCompact (overImageObj j).hom :=
  inferInstanceAs (QuasiCompact (j.left.imageι ≫ Z.hom))

instance [IsSeparated Z.hom] : IsSeparated (overImageObj j).hom :=
  inferInstanceAs (IsSeparated (j.left.imageι ≫ Z.hom))

/-- An open immersion `j : X ⟶ Z` of `S`-schemes with `X` quasi-compact and `Z` quasi-separated
over `S` is an open immersion into the scheme-theoretic image of `j`. -/
instance [IsOpenImmersion j.left] [QuasiCompact X.hom] [QuasiSeparated Z.hom] :
    IsOpenImmersion (overToImage j).left := by
  have : QuasiCompact (j.left ≫ Z.hom) := by rw [Over.w j]; infer_instance
  have : QuasiCompact j.left := .of_comp j.left Z.hom
  exact inferInstanceAs (IsOpenImmersion j.left.toImage)

/-- The square of `overToImage j`, `j` and the closed immersion `overImageι j` of the
scheme-theoretic image is cartesian: `overImageι j` is a monomorphism. -/
lemma isPullback_overToImage_overImageι :
    IsPullback (𝟙 X) (overToImage j) j (overImageι j) where
  w := by simp
  isLimit' := ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.fst) (fun s ↦ by simp)
    (fun s ↦ by rw [← cancel_mono (overImageι j)]; simp [s.condition])
    (fun s m h₁ _ ↦ by simpa using h₁)⟩

end Over

namespace ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X X' Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (j : X ⟶ X') [IsOpenImmersion j.left]

/-- **Passing to the schematic closure** (blueprint `lemma-passing-schematic-closure--1`,
`ℚ̄_ℓ`-coefficient): for an open immersion `j : X ⟶ X̄`, the schematic closure
`i : Z ⟶ X̄` of `X` and the induced open immersion `j_Z : X ⟶ Z`, there is a canonical
isomorphism `j_! ≅ j_{Z,!} ⋙ i_*` on bounded constructible complexes. It is the pushforward
comparison of the cartesian square `isPullback_overToImage_overImageι`, an isomorphism since `i`
is proper. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekSchematicClosureIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overToImage j) ⋙ boundedConstructibleLowerStar ℓ (overImageι j) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    ℓ (isPullback_overToImage_overImageι j)
  asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ
    (isPullback_overToImage_overImageι j))

/-- **Passing to the schematic closure** (blueprint `lemma-passing-schematic-closure--2`,
`ℚ̄_ℓ`-coefficient): for an open immersion `j : X ⟶ X̄`, a morphism `p : X̄ ⟶ Y`, the
schematic closure `i : Z ⟶ X̄` of `X` and the induced open immersion `j_Z : X ⟶ Z`, there is a
canonical isomorphism `j_! ⋙ Rp_* ≅ j_{Z,!} ⋙ R(i ≫ p)_*` on bounded constructible complexes. -/
noncomputable def boundedConstructibleLowerShriekSchematicClosureIso (p : X' ⟶ Y) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleLowerStar ℓ p ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
        (overToImage j) ⋙ boundedConstructibleLowerStar ℓ (overImageι j ≫ p) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl
    ℓ (isPullback_overToImage_overImageι j)
  boundedConstructibleLowerShriekRefinementIso ℓ (isPullback_overToImage_overImageι j) rfl

namespace ContinuousMapRingObj

/-- **Passing to the schematic closure** (blueprint `lemma-passing-schematic-closure--1`,
`E`-coefficient): for an open immersion `j : X ⟶ X̄`, the schematic closure `i : Z ⟶ X̄` of
`X` and the induced open immersion `j_Z : X ⟶ Z`, there is a canonical isomorphism
`j_! ≅ j_{Z,!} ⋙ i_*` on bounded constructible complexes. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekSchematicClosureIso :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
        (overToImage j) ⋙ boundedConstructibleLowerStar ℓ E (overImageι j) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_overToImage_overImageι j)
  asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_overToImage_overImageι j))

/-- **Passing to the schematic closure** (blueprint `lemma-passing-schematic-closure--2`,
`E`-coefficient): for an open immersion `j : X ⟶ X̄`, a morphism `p : X̄ ⟶ Y`, the schematic
closure `i : Z ⟶ X̄` of `X` and the induced open immersion `j_Z : X ⟶ Z`, there is a canonical
isomorphism `j_! ⋙ Rp_* ≅ j_{Z,!} ⋙ R(i ≫ p)_*` on bounded constructible complexes. -/
noncomputable def boundedConstructibleLowerShriekSchematicClosureIso (p : X' ⟶ Y) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleLowerStar ℓ E p ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ
        (overToImage j) ⋙ boundedConstructibleLowerStar ℓ E (overImageι j ≫ p) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_overToImage_overImageι j)
  boundedConstructibleLowerShriekRefinementIso ℓ E (isPullback_overToImage_overImageι j) rfl

end ContinuousMapRingObj

end ProEtale.CondensedRing

end AlgebraicGeometry
