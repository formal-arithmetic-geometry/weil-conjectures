/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-!
# Bounded complexes of finite free modules and their perfect locus

A bounded complex `P` of finite free `𝒪_Y`-modules represents a perfect object of the derived
category of `Y`. For integers `i r : ℕ` there is an open subscheme `U` of `Y` such that a morphism
`g : Y' ⟶ Y` factors through `U` if and only if `g^* P` has cohomology a finite locally free
module of rank `r` placed in degree `i`
(`AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex.exists_opens_range_subset_iff`).

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.IsFiniteFreeComplex`: bounded complexes of finite free
  modules.
- `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`: a family of modules is that of
  a finite locally free module of rank `r` placed in degree `i`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- `IsFiniteFreeComplex P d` says that the cochain complex `P` of `𝒪_X`-modules is a **bounded
complex of finite free modules in degrees `[0, d]`**: it vanishes outside `[0, d]`, and each
`P.X n` is isomorphic to a free module `𝒪_X^r` of finite rank. -/
structure IsFiniteFreeComplex (P : CochainComplex X.Modules ℤ) (d : ℕ) : Prop where
  isStrictlyGE : P.IsStrictlyGE 0
  isStrictlyLE : P.IsStrictlyLE d
  exists_iso_free (n : ℤ) :
    ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)))

/-- `IsFiniteLocallyFreeInDegree M i r` says that the family `M = (M q)_{q : ℕ}` of `𝒪_X`-modules,
thought of as the cohomology sheaves `H^q(E)` of an object `E` of the derived category of
`𝒪_X`-modules, is that of a **finite locally free module of rank `r` placed in degree `i`**:
`M q = 0` for `q ≠ i`, and `M i` is finite locally free of rank `r`.

For an object `E` represented by a complex this is the same as `E ≅ ℰ[-i]` with `ℰ` finite
locally free of rank `r`: a complex whose cohomology is concentrated in degree `i` is
quasi-isomorphic to its `i`-th cohomology placed in degree `i`. There is no derived category of
`X.Modules` with derived pushforward available, so the condition is stated on the cohomology
sheaves. The case `i = 0`, `r = 1` is an *invertible module placed in degree `0`*
(`isFiniteLocallyFreeInDegree_zero_one_iff`).

(blueprint: `def-pc-invertible-in-degree-zero`) -/
structure IsFiniteLocallyFreeInDegree (M : ℕ → X.Modules) (i r : ℕ) : Prop where
  isZero (q : ℕ) (hq : q ≠ i) : IsZero (M q)
  isFiniteLocallyFreeOfRank : (M i).IsFiniteLocallyFreeOfRank r

/-- A family of modules is that of an invertible module placed in degree `0` if and only if it
vanishes in nonzero degrees and is invertible in degree `0`.

(blueprint: `def-pc-invertible-in-degree-zero`) -/
theorem isFiniteLocallyFreeInDegree_zero_one_iff (M : ℕ → X.Modules) :
    IsFiniteLocallyFreeInDegree M 0 1 ↔
      (∀ q ≠ 0, IsZero (M q)) ∧ SheafOfModules.IsInvertible (R := X.ringCatSheaf) (M 0) :=
  ⟨fun h ↦ ⟨h.isZero, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).2
      h.isFiniteLocallyFreeOfRank⟩,
    fun h ↦ ⟨h.1, (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one (M 0)).1 h.2⟩⟩

/-- **The perfect locus of a bounded complex of finite free modules.** Let `P` be a bounded complex
of finite free `𝒪_Y`-modules, representing a perfect object `E` of the derived category of `Y`, and
fix `i r : ℕ`. There is an open subscheme `U` of `Y` such that a morphism `g : Y' ⟶ Y` factors
through `U` if and only if `L g^* E = g^* P` is a finite locally free module of rank `r` placed in
degree `i` (`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeInDegree`).

The pullback `g^* P` computes `L g^* E` because the terms of `P` are free. The proof splits
contractible summands off `P` over the local rings of `Y`, until every differential has entries in
the maximal ideal; the remaining complex is then `𝒪^r[-i]` near every point whose derived fibre has
cohomology `κ(y)^r` concentrated in degree `i`, and `U` is the set of such points. The converse
direction uses that extension of fields is faithfully flat.

(blueprint: `lem-pc-perfect-locus`) -/
theorem IsFiniteFreeComplex.exists_opens_range_subset_iff {Y : Scheme.{u}}
    {P : CochainComplex Y.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d) (i r : ℕ) :
    ∃ U : Y.Opens, ∀ {Y' : Scheme.{u}} (g : Y' ⟶ Y), Set.range g.base ⊆ U ↔
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r :=
  sorry

end AlgebraicGeometry.Scheme.Modules
