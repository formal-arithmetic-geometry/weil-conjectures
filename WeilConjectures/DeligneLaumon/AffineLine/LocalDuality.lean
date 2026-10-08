/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.DeligneLaumon.AffineLine.Defs

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
`AlgebraicGeometry.LAdicWeilSheaf.IsUnramifiedAtInfinity`, which with the present coefficients holds
for every Weil sheaf.

## Main statements

- `AlgebraicGeometry.exists_linearEquiv_dual_stalk_higherDirectImage`: the local boundary
  pairing.
- `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`: the boundary sequence
  in degrees zero and one.

## Implementation notes

With the present coefficients every Weil sheaf is zero (`AlgebraicGeometry.LAdicWeilSheaf`), so the
statements about Weil sheaves in this file are proved by vanishing.

## TODO

The maps `g` and `h` of `AlgebraicGeometry.exists_exact_compactlySupportedCohomology_boundary`
should be the maps induced by the canonical arrow `LAdicWeilSheaf.extensionByZeroToDirectImage j`
from `j_!F` to `j_*F`. This needs the identification `H_c(U, F) ≅ H_c(C, j_!F)` and the
functoriality of `compactlySupportedCohomology`; once they exist, the existential statement
should be replaced by one about these maps. The map `δ` needs a triangulated structure on Weil
complexes.
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
    (F : LAdicWeilSheaf k₀ l U) (hF : F.IsLisse) (s : C.finitePoints)
    (hsU : s.1 ∉ Set.range j.base) :
    ∃ e : (((LAdicWeilSheaf.directImage j).obj F.dual).stalk s).carrier ≃ₗ[PadicAlgCl l]
        Module.Dual (PadicAlgCl l) (((LAdicWeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier,
      ∀ a b, e ((((LAdicWeilSheaf.directImage j).obj F.dual).stalk s).frobenius a)
          ((((LAdicWeilSheaf.higherDirectImage j 1).obj F).stalk s).frobenius b) =
        (((C ↘ Spec (CommRingCat.of k₀)).residueCard s.1 : PadicAlgCl l)) * e a b := by
  -- both stalks are zero, see `LAdicWeilSheaf.isZero_stalkObj`
  have : Subsingleton (((LAdicWeilSheaf.directImage j).obj F.dual).stalk s).carrier :=
    LAdicWeilSheaf.subsingleton_stalkAt_carrier _ _ _ _
  have : Subsingleton (((LAdicWeilSheaf.higherDirectImage j 1).obj F).stalk s).carrier :=
    LAdicWeilSheaf.subsingleton_stalkAt_carrier _ _ _ _
  refine ⟨LinearEquiv.ofSubsingleton _ _, fun a b ↦ ?_⟩
  simp [Subsingleton.elim b 0]

-- the provisional Weil sheaves are zero, and the proof needs no hypothesis
set_option linter.unusedVariables false in
/-- *Boundary localization sequence for a curve.* Let `j : U₀ ↪ C₀` be a dense open immersion
of smooth curves, `i : Z₀ ↪ C₀` the closed complement and `F` a lisse Weil sheaf on `U₀`. The
open–closed triangle `j_!F → j_*F → i_*i^*j_*F →` gives a long exact sequence of compactly
supported cohomology, and since the boundary `Z₀` is finite its cohomology is concentrated in
degree zero
(`AlgebraicGeometry.LAdicWeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`). Hence
there are Frobenius-equivariant maps forming an exact sequence

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
    (F : LAdicWeilSheaf k₀ l U) (hF : F.IsLisse) :
    -- `j_*F` on `C` and the boundary sheaf `i^*j_*F` on `Z`
    let A := (LAdicWeilSheaf.directImage j).obj F
    let B := (LAdicWeilSheaf.upperStar i).obj A
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
  -- all the groups are zero, see
  -- `LAdicWeilComplex.subsingleton_compactlySupportedCohomology_carrier`
  have hU := (LAdicWeilSheaf.toComplex.obj F).subsingleton_compactlySupportedCohomology_carrier
  have hC := (LAdicWeilSheaf.toComplex.obj A).subsingleton_compactlySupportedCohomology_carrier
  have : Subsingleton (F.compactlySupportedCohomology 0).carrier := hU 0
  have : Subsingleton (F.compactlySupportedCohomology 1).carrier := hU 1
  have : Subsingleton (A.compactlySupportedCohomology 0).carrier := hC 0
  have : Subsingleton (A.compactlySupportedCohomology 1).carrier := hC 1
  refine ⟨⟨0, 0, fun y ↦ ?_, fun y ↦ ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩, 0, fun _ _ _ ↦ Subsingleton.elim _ _,
    fun _ ↦ Subsingleton.elim _ _⟩
  simp [Subsingleton.elim y 0]

end AlgebraicGeometry
