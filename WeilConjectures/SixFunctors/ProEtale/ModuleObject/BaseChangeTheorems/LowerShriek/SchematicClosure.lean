/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence

/-!
# Passing to the schematic closure in a compactification

Let `X ⟶[j] X' ⟶[p] S` be a compactification and let `i : Z ⟶ X'` be the schematic closure
of `X`, with `j_Z : X ⟶ Z` the induced open immersion, so that `j = j_Z ≫ i`. For bounded
constructible `E`- and `ℚ̄_ℓ`-sheaves this file gives the canonical identifications
`j_! ≅ j_{Z,!} ⋙ Ri_*` and `j_! ⋙ Rp_* ≅ j_{Z,!} ⋙ R(i ≫ p)_*`
(blueprint `lemma-passing-schematic-closure`).

Only the facts that `i` is a closed immersion and `j = j_Z ≫ i` are used, so the statements
are made for any closed immersion `i` through which `j` factors, the schematic closure being
one of them. The square with top `𝟙 X` is then cartesian since `i` is a monomorphism, and `i`
is proper, so the identifications are the refinement comparisons of
`ProEtale.CondensedRing.isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward`
and `ProEtale.CondensedRing.boundedConstructibleLowerShriekRefinementIso` along `i`.

## Main definitions

- `ProEtale.CondensedRing.boundedConstructibleOpenImmersionLowerShriekClosureIso`:
  `j_! ≅ j_{Z,!} ⋙ Ri_*` (blueprint `lemma-passing-schematic-closure--1`).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekClosureIso`:
  `j_! ⋙ Rp_* ≅ j_{Z,!} ⋙ R(i ≫ p)_*` (blueprint `lemma-passing-schematic-closure--2`).

Both come with `E`-coefficient versions in the namespace
`ProEtale.CondensedRing.ContinuousMapRingObj`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-- For a closed immersion `i : Z ⟶ X'` and `j = jZ ≫ i`, the square with top `𝟙 X`, left
`jZ`, right `j` and bottom `i` is cartesian, since `i` is a monomorphism. -/
lemma isPullback_id_of_isClosedImmersion {S : Scheme.{u}} {X Z X' : Over S} {j : X ⟶ X'}
    {jZ : X ⟶ Z} {i : Z ⟶ X'} [IsClosedImmersion i.left] (w : jZ ≫ i = j) :
    IsPullback (𝟙 X) jZ j i := by
  subst w
  refine IsPullback.of_map (Over.forget _) (by simp) ?_
  simpa using (IsPullback.of_id_fst (f := jZ.left)).paste_vert (IsKernelPair.id_of_mono i.left)

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Z X' S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
  {j : X ⟶ X'} {jZ : X ⟶ Z} {i : Z ⟶ X'} [IsOpenImmersion j.left] [IsOpenImmersion jZ.left]
  [IsClosedImmersion i.left]

/-- **Passing to the schematic closure, extension by zero** (blueprint
`lemma-passing-schematic-closure--1`), for bounded constructible `ℚ̄_ℓ`-sheaves: for a closed
immersion `i : Z ⟶ X'` (e.g. the schematic closure of `X` in `X'`) and open immersions
`jZ : X ⟶ Z`, `j : X ⟶ X'` with `jZ ≫ i = j`, the canonical isomorphism
`j_! ≅ jZ_! ⋙ Ri_*`, the pushforward comparison along `i`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekClosureIso (w : jZ ≫ i = j) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ jZ ⋙
        boundedConstructibleLowerStar ℓ i :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    (isPullback_id_of_isClosedImmersion w)
  asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ
    (isPullback_id_of_isClosedImmersion w))

/-- **Passing to the schematic closure, compactly supported pushforward** (blueprint
`lemma-passing-schematic-closure--2`), for bounded constructible `ℚ̄_ℓ`-sheaves: for a closed
immersion `i : Z ⟶ X'` (e.g. the schematic closure of `X` in `X'`), open immersions
`jZ : X ⟶ Z`, `j : X ⟶ X'` with `jZ ≫ i = j` and any `p : X' ⟶ S`, the canonical isomorphism
`j_! ⋙ Rp_* ≅ jZ_! ⋙ R(i ≫ p)_*`. -/
noncomputable def boundedConstructibleLowerShriekClosureIso (w : jZ ≫ i = j) (p : X' ⟶ S) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j ⋙
        boundedConstructibleLowerStar ℓ p ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ jZ ⋙
        boundedConstructibleLowerStar ℓ (i ≫ p) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ
    (isPullback_id_of_isClosedImmersion w)
  boundedConstructibleLowerShriekRefinementIso ℓ (isPullback_id_of_isClosedImmersion w) rfl

namespace ContinuousMapRingObj

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

/-- **Passing to the schematic closure, extension by zero** (blueprint
`lemma-passing-schematic-closure--1`), for bounded constructible `E`-sheaves: for a closed
immersion `i : Z ⟶ X'` (e.g. the schematic closure of `X` in `X'`) and open immersions
`jZ : X ⟶ Z`, `j : X ⟶ X'` with `jZ ≫ i = j`, the canonical isomorphism
`j_! ≅ jZ_! ⋙ Ri_*`, the pushforward comparison along `i`. -/
noncomputable def boundedConstructibleOpenImmersionLowerShriekClosureIso (w : jZ ≫ i = j) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ jZ ⋙
        boundedConstructibleLowerStar ℓ E i :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_id_of_isClosedImmersion w)
  asIso (boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_id_of_isClosedImmersion w))

/-- **Passing to the schematic closure, compactly supported pushforward** (blueprint
`lemma-passing-schematic-closure--2`), for bounded constructible `E`-sheaves: for a closed
immersion `i : Z ⟶ X'` (e.g. the schematic closure of `X` in `X'`), open immersions
`jZ : X ⟶ Z`, `j : X ⟶ X'` with `jZ ≫ i = j` and any `p : X' ⟶ S`, the canonical isomorphism
`j_! ⋙ Rp_* ≅ jZ_! ⋙ R(i ≫ p)_*`. -/
noncomputable def boundedConstructibleLowerShriekClosureIso (w : jZ ≫ i = j) (p : X' ⟶ S) :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ j ⋙
        boundedConstructibleLowerStar ℓ E p ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.continuousMapRingObj E) ℓ jZ ⋙
        boundedConstructibleLowerStar ℓ E (i ≫ p) :=
  have := isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E
    (isPullback_id_of_isClosedImmersion w)
  boundedConstructibleLowerShriekRefinementIso ℓ E (isPullback_id_of_isClosedImmersion w) rfl

end ContinuousMapRingObj

end AlgebraicGeometry.ProEtale.CondensedRing
