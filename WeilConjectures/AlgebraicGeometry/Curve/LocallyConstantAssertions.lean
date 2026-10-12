/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenReduction

/-!
# The eight curve assertions for extensions by zero of locally constant sheaves

Let `X` be a reduced curve over an algebraically closed field `k`, `U ⊆ X` an irreducible open
and `H` a finite locally constant sheaf of `𝐅_ℓ`-vector spaces on `U`. Then the eight curve
assertions hold for the extension by zero `j_! H` of `H` to `X`. Together with the dense-open
localisation `AlgebraicGeometry.IsCurve.exists_dense_assertions_iff_forall_lowerShriek` this
gives the eight assertions for every constructible `𝐅_ℓ`-sheaf on a reduced curve.

## Main statements

- `AlgebraicGeometry.Etale.nsmul_id_eq_zero_of_zmod`: a sheaf of `𝐅_r`-modules is killed by `r`.
- `AlgebraicGeometry.IsCurve.Assertions.openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf`:
  the eight assertions for `j_! H`, `H` finite locally constant on an irreducible open.

## References

- Stacks Project, Section 59.83, <https://stacks.math.columbia.edu/tag/03SB>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- A sheaf of modules over `𝐅_r = ZMod r` (lifted to `Type (u + 1)`) is killed by `r`. -/
lemma Etale.nsmul_id_eq_zero_of_zmod {X : Scheme.{u}} (r : ℕ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r)))) :
    r • 𝟙 G = 0 := by
  have e : (r • 𝟙 G).hom = r • 𝟙 G.obj := (sheafToPresheaf _ _).map_nsmul (f := 𝟙 G) (n := r)
  ext U x
  rw [e, NatTrans.app_nsmul, NatTrans.id_app]
  change r • x = 0
  rw [← Nat.cast_smul_eq_nsmul (ULift.{u + 1} (ZMod r))]
  have : (r : ULift.{u + 1} (ZMod r)) = 0 := ULift.ext _ _ (ZMod.natCast_self r)
  rw [this, zero_smul]

/-- **The eight assertions for the extension by zero of a locally constant sheaf.** Let `k` be
algebraically closed, `X` a reduced curve over `k`, `U ⊆ X` an irreducible open and `H` a finite
locally constant sheaf of `𝐅_ℓ`-vector spaces on `U`. Then the eight curve assertions hold for
`j_! H`, `j : U ⟶ X` the inclusion.

This is the step of the proof of `prop-weil-pbc-algebraically-closed-extension` following the
dense-open localisation: a connected finite étale cover `v : V ⟶ U` of degree prime to `ℓ`
trivialises the monodromy up to an `ℓ`-group, so that `H` is a direct summand of `v_* v^* H` and
`v^* H` is filtered by constant sheaves `𝐅_ℓ`; extending `v` to a finite morphism `v̄` of curves,
`j_! v_* = v̄_* j'_!`, and the assertions for `j'_! 𝐅_ℓ` come from the normalisation and the
smooth calculations. -/
theorem IsCurve.Assertions.openImmersionLowerShriek_of_isFiniteLocallyConstantSheaf
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f]
    [IsReduced X] (U : X.Opens) (hU : IsIrreducible (U : Set X)) (ℓ : ℕ) [Fact ℓ.Prime]
    (H : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [Scheme.IsFiniteLocallyConstantSheaf H] :
    IsCurve.Assertions (ULift.{u + 1} (ZMod ℓ)) f
      ((U.ι)_!open[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj H) :=
  sorry

end AlgebraicGeometry
