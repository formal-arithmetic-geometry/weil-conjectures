/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Normal.Basic
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.Mathlib.RingTheory.LaurentSeries

/-!
# Local boundary duality on a curve, and ramification at infinity

Let `j : U₀ ↪ C₀` be a dense open immersion of smooth curves and `F` a lisse Weil sheaf on
`U₀`. At a missing closed point `s` the two boundary modules `(j_*F^∨)_s̄` and `(R¹j_*F)_s̄`
are dual to one another, up to a Tate twist: the duality `𝔻_Z A(F) ≃ A(F^∨)(1)[1]` for the
boundary complex `A(F) = i^*Rj_*F` on the finite complement, obtained from Verdier exchange
and smooth curve duality, reads in degree `-1` as a perfect pairing into `ℚ̄_ℓ(-1)`.

The open–closed triangle `j_!F → j_*F → i_*i^*j_*F` also gives the boundary sequence
`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`, since the cohomology of the finite
boundary `Z` is concentrated in degree zero.

The file also records the second half of the same blueprint subsection: a nonzero linear
Artin–Schreier sheaf `ℒ_{ψ(a x)}` is ramified at infinity, because in `t = 1/x` the
Artin–Schreier cover `u^q - u = a/t` of `k((t))` is totally ramified of degree `q` with Galois
group `k₀`, on which a nontrivial `ψ` is nontrivial. This is what excludes linear characters in
the nonexceptionality test of `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension`.

## Main statements

- `AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`: the local boundary
  pairing.
- `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`: the boundary sequence
  in degrees zero and one.
- `AlgebraicGeometry.not_isUnramifiedAtInfinity_artinSchreier`: inertia at infinity acts on
  `ℒ_{ψ(a x)}` through a nontrivial character for `a ≠ 0`.

## Implementation notes

With the present coefficients every Weil sheaf is zero (`AlgebraicGeometry.WeilSheaf`), so the
statements about Weil sheaves in this file are proved by vanishing. For the same reason
`AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity` holds for every Weil sheaf, so ramification
at infinity of `ℒ_{ψ(a x)}` is stated for the Artin–Schreier extension of the local field
`k((t))` at infinity, which is where the inertia group acts.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/--
For a dense open immersion `j : U₀ ↪ C₀` of smooth curves, a lisse Weil sheaf `F` on `U₀` and a
closed point `s` of `C₀` outside `U₀`, there is a Frobenius-equivariant perfect pairing
`(j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ → ℚ̄_ℓ(-1)`:

```
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
       │           │                  │
  Frob │      Frob │                  │ q_s
       ▼           ▼                  ▼
  (j_*F^∨)_s̄ ⊗ (R¹j_*F)_s̄ ──────▶ ℚ̄_ℓ(-1)
```

It is exhibited as a linear isomorphism of `(j_*F^∨)_s̄` onto the `ℚ̄_ℓ`-dual of `(R¹j_*F)_s̄`
which intertwines the two local Frobenius actions up to the factor `q_s` coming from the Tate
twist. (blueprint: `sk-i-dl-a1-local`)
-/
theorem exists_linearEquiv_dual_stalk_higherDirectImage
    {U C : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j]
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (s : C.finitePoints)
    (hsU : s.1 ∉ Set.range j.base) :
    ∃ e : (((WeilSheaf.directImage j).obj F.dual).stalk s).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (((WeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier,
      ∀ a b, e ((((WeilSheaf.directImage j).obj F.dual).stalk s).frobenius a)
          ((((WeilSheaf.higherDirectImage j 1).obj F).stalk s).frobenius b) =
        (((C ↘ Spec (CommRingCat.of k₀)).residueCard s.1 : PadicAlgCl l)) * e a b := by
  -- both stalks are zero, see `WeilSheaf.isZero_stalkObj`
  have : Subsingleton (((WeilSheaf.directImage j).obj F.dual).stalk s).carrier :=
    WeilSheaf.subsingleton_stalkAt_carrier _ _ _ _
  have : Subsingleton (((WeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier :=
    WeilSheaf.subsingleton_stalkAt_carrier _ _ _ _
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun a b ↦ ?_⟩
  simp [Subsingleton.elim b 0]

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Boundary localization sequence for a curve.* Let `j : U₀ ↪ C₀` be a dense open immersion
of smooth curves, `i : Z₀ ↪ C₀` the closed complement and `F` a lisse Weil sheaf on `U₀`. The
open–closed triangle `j_!F → j_*F → i_*i^*j_*F →` gives a long exact sequence of compactly
supported cohomology, and since the boundary `Z₀` is finite its cohomology is concentrated in
degree zero (`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`).
Hence there are Frobenius-equivariant maps forming an exact sequence

`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`,

and a Frobenius-equivariant injection `H_c^0(U, F) ↪ H_c^0(C, j_*F)`.

The provisional Weil complexes are not triangulated, so the maps are only asserted to exist;
with the present coefficients all the groups vanish.
(blueprint: `prop-a1-curve-boundary-sequence`) -/
theorem exists_exact_compactlySupportedCohomology_boundary
    {U C Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    [IsDominant j] (i : Z ⟶ C) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    [SmoothOfRelativeDimension 1 (C ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (C ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))] [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] [IsFinite (Z ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) :
    -- `j_*F` on `C` and the boundary sheaf `i^*j_*F` on `Z`
    let A := (WeilSheaf.directImage j).obj F
    let B := (WeilSheaf.upperStar i).obj A
    (∃ (δ : (B.compactlySupportedCohomology 0).carrier →ₗ[PadicAlgCl l]
          (F.compactlySupportedCohomology 1).carrier)
        (g : (F.compactlySupportedCohomology 1).carrier →ₗ[PadicAlgCl l]
          (A.compactlySupportedCohomology 1).carrier),
        Function.Exact δ g ∧ Function.Surjective g ∧
          (∀ x, δ ((B.compactlySupportedCohomology 0).frobenius x) =
            (F.compactlySupportedCohomology 1).frobenius (δ x)) ∧
          ∀ x, g ((F.compactlySupportedCohomology 1).frobenius x) =
            (A.compactlySupportedCohomology 1).frobenius (g x)) ∧
      ∃ h : (F.compactlySupportedCohomology 0).carrier →ₗ[PadicAlgCl l]
          (A.compactlySupportedCohomology 0).carrier,
        Function.Injective h ∧ ∀ x, h ((F.compactlySupportedCohomology 0).frobenius x) =
          (A.compactlySupportedCohomology 0).frobenius (h x) := by
  intro A B
  -- all the groups are zero, see `WeilComplex.subsingleton_compactlySupportedCohomology_carrier`
  have hU := (WeilSheaf.toComplex.obj F).subsingleton_compactlySupportedCohomology_carrier
  have hC := (WeilSheaf.toComplex.obj A).subsingleton_compactlySupportedCohomology_carrier
  have : Subsingleton (F.compactlySupportedCohomology 0).carrier := hU 0
  have : Subsingleton (F.compactlySupportedCohomology 1).carrier := hU 1
  have : Subsingleton (A.compactlySupportedCohomology 0).carrier := hC 0
  have : Subsingleton (A.compactlySupportedCohomology 1).carrier := hC 1
  refine ⟨⟨0, 0, fun y ↦ ?_, fun y ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩, 0, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩
  simp [Subsingleton.elim y 0]

omit [Fact (ringChar k₀ ≠ l)] in
/-- *Linear Artin–Schreier sheaves are ramified at infinity.* Let `ψ` be a nontrivial additive
character of `k₀`, `a ∈ k₀ˣ` and `q = #k₀`. In the coordinate `t = 1 / x` at `∞ ∈ ℙ¹`, the
Artin–Schreier cover `u^q - u = a x` defining `ℒ_{ψ(a x)}` becomes `u^q - u = a / t` over the
local field `K = k((t))`, for a field `k` over `k₀` (for the geometric statement, an algebraic
closure of `k₀`, in which case `Gal(K̄/K)` is the inertia group `I_∞`). Given a root `u` in an
algebraic closure `L` of `K`, an element `σ ∈ Gal(L/K)` acts on the roots `u + c`, `c ∈ k₀`, by
the translation `σ u = u + κ(σ)`, hence on the geometric generic stalk of `ℒ_{ψ(a x)}` by the
scalar `ψ(±κ(σ))`. Since `uᑫ - u - a / t` is irreducible over `K`
(`LaurentSeries.irreducible_X_pow_sub_X_sub_C_single`), `κ` is onto `k₀`, so some `σ` acts
through `ψ(c) ≠ 1`: inertia at infinity acts nontrivially.

This statement replaces `¬ (artinSchreier ψ a).IsUnramifiedAtInfinity (𝟙 (affineLine k₀))`,
which is false with the present coefficients: every Weil sheaf is zero, so every Weil sheaf on
`𝔸¹` extends to a lisse Weil sheaf on `ℙ¹`.
(blueprint: `lem-a1-artin-schreier-ramified-infinity`, `sk-i-dl-a1-local`) -/
theorem not_isUnramifiedAtInfinity_artinSchreier (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {a : k₀} (ha : a ≠ 0) (k : Type*) [Field k] [Algebra k₀ k] (L : Type*) [Field L]
    [Algebra (LaurentSeries k) L] [IsAlgClosure (LaurentSeries k) L] {u : L}
    (hu : u ^ Nat.card k₀ - u =
      algebraMap (LaurentSeries k) L (HahnSeries.single (-1) (algebraMap k₀ k a))) :
    ∃ (σ : L ≃ₐ[LaurentSeries k] L) (c : k₀),
      σ u = u + algebraMap (LaurentSeries k) L (HahnSeries.C (algebraMap k₀ k c)) ∧ ψ c ≠ 1 := by
  set K := LaurentSeries k
  have := Fintype.ofFinite k₀
  obtain ⟨c, hc⟩ := AddChar.ne_one_iff.1 hψ
  set ι : k₀ →+* L := (algebraMap K L).comp (HahnSeries.C.comp (algebraMap k₀ k))
  set q := Nat.card k₀
  have hq : 2 ≤ q := Finite.one_lt_card
  set s : K := HahnSeries.single (-1 : ℤ) (algebraMap k₀ k a)
  set f : K[X] := X ^ q - X - C s
  have hfirr : Irreducible f := LaurentSeries.irreducible_X_pow_sub_X_sub_C_single hq
    ((map_ne_zero_iff _ (algebraMap k₀ k).injective).2 ha)
  have hfmon : f.Monic := by
    unfold f
    rw [sub_sub]
    exact monic_X_pow_sub (by compute_degree; exact_mod_cast (by omega : 1 < q))
  -- `u + ι c` is again a root of `f`, as `c ^ q = c`
  obtain ⟨p, hp⟩ := CharP.exists k₀
  have : Fact p.Prime := ⟨CharP.char_is_prime k₀ p⟩
  have : CharP L p := charP_of_injective_ringHom ι.injective p
  obtain ⟨m, -, hm⟩ := FiniteField.card k₀ p
  have hqc : q = Fintype.card k₀ := Nat.card_eq_fintype_card
  have hroot : (u + ι c) ^ q - (u + ι c) = algebraMap K L s := by
    rw [hqc, hm, add_pow_char_pow, ← hm, ← map_pow, FiniteField.pow_card, ← hqc, ← hu]
    ring
  have hmin : ∀ x : L, x ^ q - x = algebraMap K L s → f = minpoly K x := fun x hx ↦
    minpoly.eq_of_irreducible_of_monic hfirr (by simp [f, hx]) hfmon
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit L).1 ((hmin _ hroot).symm.trans (hmin _ hu))
  exact ⟨σ, c, hσ, hc⟩

end AlgebraicGeometry
