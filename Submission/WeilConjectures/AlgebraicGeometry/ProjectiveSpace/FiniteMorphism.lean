/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Finite morphisms and projective morphisms

A projective morphism is presented, as in the blueprint's H-projective convention
(`def-pc-projective-morphism`), by a closed immersion `i : X ⟶ ℙ(n; S)` over `S` with a finite
type `n` of homogeneous coordinates.

* A projective morphism whose geometric fibres are finite sets is finite
  (`lem-fin-projective-finite-fibres`).
* A projective family over a Noetherian domain whose generic fibre has dimension `≤ 0` is finite
  over a nonempty open of the base (`lem-fin-projective-generically-finite`).
* A scheme finite over a projective scheme over an affine base is projective over that base
  (`lem-fin-finite-over-projective`).

The first two are consequences of Zariski's main theorem in the form
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton` (a proper
morphism is finite over a neighbourhood of every point with finite fibre), rather than of the
Serre-vanishing argument of the blueprint. The third embeds `Y` by the pullback of `𝒪(1)` along
the finite morphism, whose coordinate sections have affine non-vanishing loci covering `Y`.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.isFinite_of_finite_pullback`
- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_morphismRestrict_of_generic_fibre`
- `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u} [Finite n]


/-- Blueprint `lem-fin-finite-over-projective`: Finite covers of projective schemes are
projective.

Let `S` be affine, `f : T ⟶ S` projective, i.e. `f = π ∘ i` for a closed immersion
`i : T ⟶ ℙ(n; S)`, and `h : Y ⟶ T` finite. Then `h ≫ f` is projective: there is a closed
immersion `j : Y ⟶ ℙ(m; S)` over `S` for a finite type `m`.

The blueprint assumes `S` Noetherian and argues over an affine open of `S`; with the
H-projective convention (a closed immersion into `ℙ(m; S)` itself) the global statement needs
the base to be affine, and Noetherianity is not used. -/
theorem exists_isClosedImmersion_of_isFinite {S T Y : Scheme.{u}} [IsAffine S] (f : T ⟶ S)
    (i : T ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (h : Y ⟶ T)
    [IsFinite h] :
    ∃ (m : Type u) (_ : Finite m) (j : Y ⟶ ℙ(m; S)),
      IsClosedImmersion j ∧ j ≫ ℙ(m; S) ↘ S = h ≫ f := by
  subst hi
  have hs (j : n) : IsAffineOpen
      (Scheme.Modules.Hom.zeroLocus (coordinateSection n S j)).support.compl := by
    rw [compl_support_zeroLocus_coordinateSection]
    exact isAffineOpen_standardOpen n S j
  have hcov : ⨆ j, (Scheme.Modules.Hom.zeroLocus (coordinateSection n S j)).support.compl =
      ⊤ := by
    simp_rw [compl_support_zeroLocus_coordinateSection]
    exact iSup_standardOpen n S
  obtain ⟨L, hL, s, hs', hcov'⟩ :=
    Scheme.Modules.exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom (h ≫ i)
      (twist n S 1) (coordinateSection n S) hs hcov
  obtain ⟨m, hm, j, hj, hjS⟩ :=
    exists_isImmersion_projectiveSpace_of_isAffineOpen (h ≫ i ≫ ℙ(n; S) ↘ S) L s hs' hcov'
  refine ⟨m, hm, j, ?_, by simpa using hjS⟩
  have : IsProper (j ≫ ℙ(m; S) ↘ S) := hjS ▸ inferInstance
  have : IsProper j := IsProper.of_comp j (ℙ(m; S) ↘ S)
  exact (IsClosedImmersion.iff_isProper_and_mono j).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProjectiveSpace
