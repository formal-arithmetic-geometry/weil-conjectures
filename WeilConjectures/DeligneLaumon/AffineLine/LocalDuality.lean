/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.OpenClosedTriangle
public import WeilConjectures.WeilSheaf.UpperStarLowerStar
public import WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Trace

/-!
# Local boundary duality on a curve

Let `j : U₀ ↪ C₀` be a dense open immersion of smooth curves and `F` a lisse Weil sheaf on
`U₀`. At a missing closed point `s` the two boundary modules `(j_*F^∨)_s̄` and `(R¹j_*F)_s̄`
are dual to one another, up to a Tate twist: the duality `𝔻_Z A(F) ≃ A(F^∨)(1)[1]` for the
boundary complex `A(F) = i^*Rj_*F` on the finite complement, obtained from Verdier exchange
and smooth curve duality, reads in degree `-1` as a perfect pairing into `ℚ̄_ℓ(-1)`.

The open–closed triangle `j_!F → j_*F → i_*i^*j_*F` also gives the boundary sequence
`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`, since the cohomology of the finite
boundary `Z` is concentrated in degree zero.

The second half of the same blueprint subsection, that a nonzero linear Artin–Schreier sheaf
`ℒ_{ψ(a x)}` is ramified at infinity, is stated for the Artin–Schreier extension of the local
field `k((t))` at infinity, where the inertia group acts:
`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`. It is not stated for
`AlgebraicGeometry.WeilSheaf.IsUnramifiedAtInfinity`, which is not yet the inertia condition of
the blueprint.

## Main statements

- `AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`: the local boundary
  pairing.
- `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`: the boundary sequence
  in degrees zero and one.

## TODO

- Prove the local boundary pairing and the boundary sequence, which are stated with `sorry`,
  once the category is redefined (`sk-d-real-weil`).
- The maps `g` and `h` of `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`
  should be the maps induced by the canonical arrow `WeilSheaf.extensionByZeroToDirectImage j`
  from `j_!F` to `j_*F`. This needs the identification `H_c(U, F) ≅ H_c(C, j_!F)` and the
  functoriality of `compactlySupportedCohomology`; once they exist, the existential statement
  should be replaced by one about these maps. The map `δ` needs a triangulated structure on
  Weil complexes.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

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
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (C ↘ Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l U) (hF : F.IsLisse) (s : C.finitePoints)
    (hsU : s.1 ∉ Set.range j.base) :
    ∃ e : (((WeilSheaf.directImage j).obj (F.dual hF)).stalk s).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (((WeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier,
      ∀ a b, e ((((WeilSheaf.directImage j).obj (F.dual hF)).stalk s).frobenius a)
          ((((WeilSheaf.higherDirectImage j 1).obj F).stalk s).frobenius b) =
        (((C ↘ Spec (CommRingCat.of k₀)).residueCard s.1 : PadicAlgCl l)) * e a b := by
  sorry

set_option maxHeartbeats 1600000 in
-- the cohomology of the three terms of the triangle unfolds through the Weil structures
/-- *Boundary localization sequence for a curve.* Let `j : U₀ ↪ C₀` be a dense open immersion
of smooth curves, `i : Z₀ ↪ C₀` the closed complement and `F` a lisse Weil sheaf on `U₀`. The
open–closed triangle `j_!F → j_*F → i_*i^*j_*F →` gives a long exact sequence of compactly
supported cohomology, and since the boundary `Z₀` is finite its cohomology is concentrated in
degree zero (`AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`).
Hence there are Frobenius-equivariant maps forming an exact sequence

`H_c^0(Z, i^*j_*F) → H_c^1(U, F) → H_c^1(C, j_*F) → 0`,

and a Frobenius-equivariant injection `H_c^0(U, F) ↪ H_c^0(C, j_*F)`.
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
  have : IsSeparated (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  have : QuasiCompact (Z ↘ Spec (CommRingCat.of k₀)) := inferInstance
  -- the open–closed triangle `RΓ_c(U, j^*K) → RΓ_c(C, K) → RΓ_c(Z, i^*K) →` for `K = j_*F`
  obtain ⟨α, β, γ, hT⟩ := WeilComplex.exists_distTriang_derivedLowerShriek_openClosed j i hij
    (WeilSheaf.toComplex.obj A)
  set T := Triangle.mk α β γ
  -- identification of the outer terms
  have hA : A = (WeilSheaf.lowerStar j).obj F := rfl
  let eU : (WeilComplex.upperStar j).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj F :=
    (WeilSheaf.toComplexCompUpperStarIso j).app A ≪≫
      WeilSheaf.toComplex.mapIso (hA ▸ WeilSheaf.upperStarDirectImageIso j F)
  let eZ : (WeilComplex.upperStar i).obj (WeilSheaf.toComplex.obj A) ≅
      WeilSheaf.toComplex.obj B :=
    (WeilSheaf.toComplexCompUpperStarIso i).app A
  let EU (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (U ↘ Spec (CommRingCat.of k₀))).mapIso eU) r
  let EZ (r : ℤ) := WeilComplex.cohomologyEquivOfIso
    ((WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).mapIso eZ) r
  -- the boundary has no cohomology outside degree `0`
  have hZ (r : ℤ) (hr : r ≠ 0) : Subsingleton (T.obj₃.cohomologyFrobeniusModule r).carrier := by
    have h := WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite B hr
    exact ⟨fun a b ↦ (EZ r).toLinearEquiv.injective (h.elim _ _)⟩

  refine ⟨⟨(EU 1).toLinearEquiv.toLinearMap ∘ₗ WeilComplex.cohomologyδ T 0 1 rfl ∘ₗ
      (EZ 0).toLinearEquiv.symm.toLinearMap,
    WeilComplex.cohomologyMap T.mor₁ 1 ∘ₗ (EU 1).toLinearEquiv.symm.toLinearMap, ?_, ?_, ?_, ?_⟩,
    WeilComplex.cohomologyMap T.mor₁ 0 ∘ₗ (EU 0).toLinearEquiv.symm.toLinearMap, ?_, ?_⟩
  · intro y
    have hex := WeilComplex.exact_cohomologyδ_right T 0 1 rfl hT ((EU 1).toLinearEquiv.symm y)
    change WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm y) = 0 ↔
      ∃ x, (EU 1).toLinearEquiv (WeilComplex.cohomologyδ T 0 1 rfl
        ((EZ 0).toLinearEquiv.symm x)) = y
    rw [hex]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨(EZ 0).toLinearEquiv x, ?_⟩
      rw [LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]
    · rintro ⟨x, hx⟩
      refine ⟨(EZ 0).toLinearEquiv.symm x, ?_⟩
      rw [← hx, LinearEquiv.symm_apply_apply]
  · intro z
    have := hZ 1 one_ne_zero
    obtain ⟨x, hx⟩ := (WeilComplex.exact_cohomologyMap T 1 hT z).1 (Subsingleton.elim _ _)
    refine ⟨(EU 1).toLinearEquiv x, ?_⟩
    change WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm
      ((EU 1).toLinearEquiv x)) = z
    rw [LinearEquiv.symm_apply_apply, hx]
  · intro x
    change (EU 1).toLinearEquiv (WeilComplex.cohomologyδ T 0 1 rfl
        ((EZ 0).toLinearEquiv.symm ((B.compactlySupportedCohomology 0).frobenius x))) =
      (F.compactlySupportedCohomology 1).frobenius ((EU 1).toLinearEquiv
        (WeilComplex.cohomologyδ T 0 1 rfl ((EZ 0).toLinearEquiv.symm x)))
    erw [(EZ 0).symm_map_frobenius x, WeilComplex.cohomologyδ_frobenius, (EU 1).map_frobenius]
    rfl
  · intro x
    change WeilComplex.cohomologyMap T.mor₁ 1
        ((EU 1).toLinearEquiv.symm ((F.compactlySupportedCohomology 1).frobenius x)) =
      (A.compactlySupportedCohomology 1).frobenius
        (WeilComplex.cohomologyMap T.mor₁ 1 ((EU 1).toLinearEquiv.symm x))
    erw [(EU 1).symm_map_frobenius x, WeilComplex.cohomologyMap_frobenius]
    rfl
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    change WeilComplex.cohomologyMap T.mor₁ 0 ((EU 0).toLinearEquiv.symm x) = 0 at hx
    obtain ⟨z, hz⟩ := (WeilComplex.exact_cohomologyδ_right T (-1) 0 (by norm_num) hT _).1 hx
    have := hZ (-1) (by norm_num)
    rw [Subsingleton.elim z 0, map_zero] at hz
    have := congrArg (EU 0).toLinearEquiv hz
    rwa [LinearEquiv.apply_symm_apply, map_zero, eq_comm] at this
  · intro x
    change WeilComplex.cohomologyMap T.mor₁ 0
        ((EU 0).toLinearEquiv.symm ((F.compactlySupportedCohomology 0).frobenius x)) =
      (A.compactlySupportedCohomology 0).frobenius
        (WeilComplex.cohomologyMap T.mor₁ 0 ((EU 0).toLinearEquiv.symm x))
    erw [(EU 0).symm_map_frobenius x, WeilComplex.cohomologyMap_frobenius]
    rfl

end AlgebraicGeometry
