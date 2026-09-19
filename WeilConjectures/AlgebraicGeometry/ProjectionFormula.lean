/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Degree
public import WeilConjectures.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Modules.GenericRank
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Exact

/-!
# The generic rank and the projection formula for intersection numbers

Let `Y` be an integral scheme of dimension `d`, proper over a field `k` and carrying an ample
invertible sheaf, and let `L₁, …, L_d` be invertible sheaves on `Y`. The top intersection number
`(L₁ ⋯ L_d · F)` of `L₁, …, L_d` with coefficients in a coherent sheaf `F` sees `F` only through
its *generic rank* `r = dim_{κ(η)} F_η`:

`(L₁ ⋯ L_d · F) = r · (L₁ ⋯ L_d)`.

For a finite morphism `f : X ⟶ Y` and a coherent sheaf `F` on `X`, the invariance of the Euler
characteristic along a finite morphism and the projection formula for the direct image give the
projection formula for intersection numbers:

`(f^* L₁ ⋯ f^* L_d · F)_X = (L₁ ⋯ L_d · f_* F)_Y`.

Taking `F = 𝒪_X` and combining the two, the right-hand side is `deg f · (L₁ ⋯ L_d)_Y`, where
`deg f` is `AlgebraicGeometry.Scheme.Hom.degree`, the generic rank of `f_* 𝒪_X`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_eq_genericRank_mul`:
  **`prop:deg-intersection-rank`**, the top intersection number sees only the generic rank.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_pullback_eq_intersectionNumber_pushforward`:
  the sheaf-theoretic projection formula, `(f^* L₁ ⋯ f^* L_d · F)_X = (L₁ ⋯ L_d · f_* F)_Y`.
* `AlgebraicGeometry.Scheme.Modules.intersectionNumber_pullback_eq_degree_mul`:
  **`prop:deg-projection-formula`**, the projection formula for a finite morphism.

## Implementation notes

The dimension of `Y` enters as the hypothesis `topologicalKrullDim Y = d`, and properness and
ampleness as the hypotheses of Snapper's theorem — `Y` proper over `k` with an ample invertible
sheaf `A`, and `k` infinite — in place of the blueprint's "projective over an algebraically
closed field". The blueprint's `(L₁ ⋯ L_d)` is the case `F = 𝟙_ Y.Modules` of the intersection
number, the tensor unit of `Y.Modules` being the structure sheaf.

The proof of `intersectionNumber_eq_genericRank_mul` runs the blueprint's two inductions — the
one computing the intersection number and the one computing the generic rank — as a single
induction along the dévissage `AlgebraicGeometry.Scheme.Modules.exists_devissage`, whose graded
pieces are handled by
`intersectionNumber_eq_genericRank_mul_of_isPushforwardIdealSheaf`. There the dichotomy of the
blueprint — either `dim Z_j < d` or `Z_j = Y` — is run on the generic rank instead of on the
dimension: a graded piece `ι_* 𝓘` of generic rank zero has both sides zero, and a graded piece
of non-zero generic rank has the generic point of `Y` in the image of `ι`, whence `ι` is a
surjective closed immersion onto a reduced scheme, hence an isomorphism, and `ι_* 𝓘` is a
subsheaf of `𝒪_Y` of generic rank one.

That last step is taken through `genericRank_le_of_mono` and not through
`AlgebraicGeometry.Scheme.IdealSheafData.genericRank_toModules`, although the blueprint reads
the piece as a non-zero ideal sheaf on `Y`: the ideal sheaf `𝓘` lives on `Z`, and comparing its
generic rank with that of `ι_* 𝓘` would need the invariance of the generic rank along an
isomorphism of schemes, which the project does not have. The monomorphism `ι_* 𝓘 ⟶ 𝒪_Y` is
available directly on `Y` and gives the bound in one line.

The projection formula is proved for any finite `f`, surjectivity not being needed: without it
`deg f` is zero and both sides vanish. No hypothesis on the dimension of `X` is used either.

## References

* S. L. Kleiman, *Toward a numerical theory of ampleness*, Ann. of Math. (2) **84** (1966),
  293–344, §1.
* The blueprint chapter on the degree of an isogeny, section `sec:deg-intersection`:
  `prop:deg-intersection-rank` and `prop:deg-projection-formula`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

section IntersectionRank

variable (k : Type u) [Field k] {Y : Scheme.{u}} [Y.Over (Spec (.of k))] [Infinite k]
  [IsProper (Y ↘ Spec (.of k))] [IsIntegral Y] {A : Y.Modules} (hA : A.Invertible)
  (hAa : A.IsAmple) {d : ℕ} (hd : topologicalKrullDim Y = (d : WithBot ℕ∞))

/-- **The identity `(L₁ ⋯ L_d · F) = rk F · (L₁ ⋯ L_d)` is stable under extensions**: if the two
outer terms of a short exact sequence of coherent sheaves satisfy it, so does the middle term.
Both sides are additive along a short exact sequence — the intersection number by
`intersectionNumber_add_intersectionNumber` and the generic rank by `genericRank_add`. -/
theorem intersectionNumber_eq_genericRank_mul_of_shortExact {S : ShortComplex Y.Modules}
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent]
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible)
    (h₁ : intersectionNumber k S.X₁ L hL
      = (genericRank S.X₁ : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL)
    (h₃ : intersectionNumber k S.X₃ L hL
      = (genericRank S.X₃ : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL) :
    intersectionNumber k S.X₂ L hL
      = (genericRank S.X₂ : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  rw [← intersectionNumber_add_intersectionNumber k hS L hL, h₁, h₃, hS.genericRank_add]
  push_cast
  ring

include hA hAa hd

/-- **A coherent sheaf whose generic rank vanishes has vanishing top intersection number**: its
support is then a proper closed subset of `Y`, hence of dimension `< d`. -/
theorem intersectionNumber_eq_zero_of_genericRank_eq_zero (F : Y.Modules) [F.IsCoherent]
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) (hr : genericRank F = 0) :
    intersectionNumber k F L hL = 0 := by
  have hcpt : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  refine intersectionNumber_eq_zero_of_supportDim_lt k hA hAa F L hL ?_
  have hns : genericPoint Y ∉ F.support := (genericRank_eq_zero_iff F).1 hr
  rw [supportDim_def, ← hd]
  exact topologicalKrullDim_lt_of_ne_univ (Y ↘ Spec (.of k)) (isClosed_support F)
    fun h ↦ hns (h ▸ Set.mem_univ _)

/-- **A subsheaf of the same generic rank has the same top intersection number**: the quotient
has generic rank zero, so its own intersection number vanishes. -/
theorem intersectionNumber_eq_of_mono_of_genericRank_eq {G H : Y.Modules} [G.IsCoherent]
    [H.IsCoherent] (u : G ⟶ H) [Mono u] (hrk : genericRank G = genericRank H)
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k G L hL = intersectionNumber k H L hL := by
  have hcohc : (cokernel u).IsCoherent := isCoherent_cokernel u inferInstance inferInstance
  have hSE := ShortComplex.shortExact_mk_cokernelπ u
  have hrk' : genericRank H = genericRank G + genericRank (cokernel u) := hSE.genericRank_add
  have hz : genericRank (cokernel u) = 0 := by omega
  have h0 := intersectionNumber_eq_zero_of_genericRank_eq_zero k hA hAa hd (cokernel u) L hL hz
  have hadd : intersectionNumber k G L hL + intersectionNumber k (cokernel u) L hL
      = intersectionNumber k H L hL := intersectionNumber_add_intersectionNumber k hSE L hL
  omega

/-- **The top intersection number of a graded piece of the dévissage.** -/
theorem intersectionNumber_eq_genericRank_mul_of_isPushforwardIdealSheaf (P : Y.Modules)
    [P.IsCoherent] (hP : IsPushforwardIdealSheaf P) (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k P L hL
      = (genericRank P : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  obtain ⟨Z, ι, hι, hZ, I, hI, ⟨e⟩⟩ := hP
  -- the dichotomy of the blueprint, run on the generic rank of `P` rather than on `dim Z`: a
  -- piece of generic rank zero misses the generic point of `Y`, and a piece of non-zero generic
  -- rank forces `ι` to be an isomorphism
  by_cases hr : genericRank P = 0
  · rw [hr, intersectionNumber_eq_zero_of_genericRank_eq_zero k hA hAa hd P L hL hr]
    simp
  have hmem : genericPoint Y ∈ Set.range ι.base := by
    by_contra hn
    have hss : Subsingleton (((pushforward ι).obj I.toModules).presheaf.stalk (genericPoint Y)) :=
      subsingleton_stalk_pushforward_of_notMem_range ι I.toModules
        ι.isClosedEmbedding.isClosed_range hn
    exact hr ((genericRank_congr e).trans (genericRank_eq_zero_of_subsingleton hss))
  have hrange : Set.range ι.base = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← genericPoint_closure Y]
    exact ι.isClosedEmbedding.isClosed_range.closure_subset_iff.2 (by simpa using hmem)
  have hsurj : Surjective ι := ⟨Set.range_eq_univ.1 hrange⟩
  have hiso : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  -- `P` is now a subsheaf of `𝒪_Y`, so its generic rank is at most that of `𝒪_Y`, namely `1`
  set u : P ⟶ 𝟙_ Y.Modules := e.hom ≫ (pushforward ι).map I.toModulesι ≫
    (pushforwardStructureModulesIso ι).hom ≫ (tensorUnitIsoUnit Y).inv with hu
  have hmono : Mono u := by
    rw [hu]
    infer_instance
  have hle : genericRank P ≤ 1 := by
    simpa [genericRank_tensorUnit] using genericRank_le_of_mono u
  have hP1 : genericRank P = 1 := le_antisymm hle (Nat.one_le_iff_ne_zero.2 hr)
  rw [hP1, Nat.cast_one, one_mul]
  exact intersectionNumber_eq_of_mono_of_genericRank_eq k hA hAa hd u
    (by rw [hP1, genericRank_tensorUnit]) L hL

/-- **The top intersection number sees only the generic rank** (`prop:deg-intersection-rank`).

For `Y` an integral scheme of dimension `d`, proper over the field `k` and carrying an ample
invertible sheaf, for `L₁, …, L_d` invertible and `F` coherent of generic rank `r`,

`(L₁ ⋯ L_d · F) = r · (L₁ ⋯ L_d)`. -/
theorem intersectionNumber_eq_genericRank_mul (F : Y.Modules) [F.IsCoherent]
    (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F L hL
      = (genericRank F : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType (Y ↘ Spec (.of k))
  obtain ⟨t, G, φ, hG0, ⟨eF⟩, hstep⟩ := exists_devissage F
  have key : ∀ j : Fin (t + 1), (G j).IsCoherent ∧
      intersectionNumber k (G j) L hL
        = (genericRank (G j) : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
    refine Fin.induction ⟨isCoherent_of_isZero hG0, ?_⟩ ?_
    · rw [intersectionNumber_eq_zero_of_isZero k hG0, genericRank_eq_zero_of_isZero hG0]
      simp
    · rintro j ⟨hcoh, ih⟩
      obtain ⟨hcohs, hmono, hpush⟩ := hstep j
      have hcohc : (cokernel (φ j)).IsCoherent :=
        isCoherent_cokernel (φ j) inferInstance hcohs
      refine ⟨hcohs, intersectionNumber_eq_genericRank_mul_of_shortExact k hA hAa hd
        (ShortComplex.shortExact_mk_cokernelπ (φ j)) L hL ih ?_⟩
      exact intersectionNumber_eq_genericRank_mul_of_isPushforwardIdealSheaf k hA hAa hd
        (cokernel (φ j)) hpush L hL
  obtain ⟨-, hlast⟩ := key (Fin.last t)
  rw [← intersectionNumber_congr_coeff k eF L hL, hlast, genericRank_congr eF]

end IntersectionRank

section ProjectionFormula

variable (k : Type u) [Field k] {X Y : Scheme.{u}} [X.Over (Spec (.of k))]
  [Y.Over (Spec (.of k))] (f : X ⟶ Y) [IsFinite f] [f.IsOver (Spec (.of k))]

/-- **The sheaf-theoretic projection formula for intersection numbers**:

```text
  (f^* L₁ ⋯ f^* L_d · F)_X = (L₁ ⋯ L_d · f_* F)_Y.
```

Term by term, the two alternating sums are the two sides of

```text
  χ(X, F ⊗ f^* (⨂_{j ∈ S} L_j)) = χ(Y, f_* F ⊗ ⨂_{j ∈ S} L_j),
```

which is `eulerChar_tensorObj_pullback`, once the inverse image of the twisting factor is
identified with the twisting factor of the inverse images by
`AlgebraicGeometry.Scheme.Pic.mk_zpowProd_pullback`. -/
theorem intersectionNumber_pullback_eq_intersectionNumber_pushforward (F : X.Modules)
    [F.IsCoherent] {d : ℕ} (L : Fin d → Y.Modules) (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k F (fun j ↦ (pullback f).obj (L j)) (fun j ↦ (hL j).pullback f)
      = intersectionNumber k ((pushforward f).obj F) L hL := by
  simp only [intersectionNumber]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  congr 1
  obtain ⟨eZ⟩ := Pic.mk_eq_mk_iff.1
    (Pic.mk_zpowProd_pullback f L hL fun j ↦ if j ∈ S then 1 else 0)
  have hN := invertible_zpowProd L hL fun j ↦ if j ∈ S then 1 else 0
  have : (F ⊗ (pullback f).obj (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0)).IsCoherent :=
    isCoherent_tensorObj_of_invertible F (hN.pullback f)
  have hNl : (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0).IsLocallyFree := hN.isLocallyFree
  have hNf : (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0).IsFiniteType := hN.isFiniteType
  calc eulerChar k (tensorZPow F (fun j ↦ (pullback f).obj (L j))
          (fun j ↦ (hL j).pullback f) fun j ↦ if j ∈ S then 1 else 0)
      = eulerChar k (F ⊗
          (pullback f).obj (zpowProd L hL fun j ↦ if j ∈ S then 1 else 0)) :=
        eulerChar_congr k (tensorIso (Iso.refl _) eZ)
    _ = eulerChar k ((pushforward f).obj F ⊗
          zpowProd L hL fun j ↦ if j ∈ S then 1 else 0) :=
        eulerChar_tensorObj_pullback k f F _
    _ = eulerChar k (tensorZPow ((pushforward f).obj F) L hL
          fun j ↦ if j ∈ S then 1 else 0) := rfl

/-- **The projection formula for intersection numbers** (`prop:deg-projection-formula`).

For a finite morphism `f : X ⟶ Y` of schemes over `k` with `Y` integral of dimension `d`, proper
over `k` and carrying an ample invertible sheaf, and for `L₁, …, L_d` invertible on `Y`,

`(f^* L₁ ⋯ f^* L_d)_X = deg f · (L₁ ⋯ L_d)_Y`,

where `deg f` is the generic rank of `f_* 𝒪_X` and, on both sides, the intersection number with
no coefficient sheaf is the one with coefficients in the tensor unit, that is in the structure
sheaf. -/
theorem intersectionNumber_pullback_eq_degree_mul [Infinite k] [IsProper (Y ↘ Spec (.of k))]
    [IsIntegral Y] {A : Y.Modules} (hA : A.Invertible) (hAa : A.IsAmple)
    {d : ℕ} (hd : topologicalKrullDim Y = (d : WithBot ℕ∞)) (L : Fin d → Y.Modules)
    (hL : ∀ j, (L j).Invertible) :
    intersectionNumber k (𝟙_ X.Modules) (fun j ↦ (pullback f).obj (L j))
        (fun j ↦ (hL j).pullback f)
      = (f.degree : ℤ) * intersectionNumber k (𝟙_ Y.Modules) L hL := by
  have hc : ((pushforward f).obj X.structureModules).IsCoherent :=
    isCoherent_pushforward_of_isFinite f X.structureModules
  rw [intersectionNumber_congr_coeff k (tensorUnitIsoUnit X) _ _,
    intersectionNumber_pullback_eq_intersectionNumber_pushforward k f X.structureModules L hL]
  exact intersectionNumber_eq_genericRank_mul k hA hAa hd _ L hL

end ProjectionFormula

end AlgebraicGeometry.Scheme.Modules
