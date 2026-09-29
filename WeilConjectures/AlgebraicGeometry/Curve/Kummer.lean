/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Brauer
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# `H²(C, μₙ)` of a curve

For a curve `C` over an algebraically closed field `k` and `n` prime to the characteristic,
`H²(C, μₙ) ≅ Pic(C)/n`. This is the Kummer sequence
`AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_two`, which holds for every
scheme on which `n` is invertible, together with the vanishing of the Brauer group of a curve.

## Main statements

- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **`H²` via the Kummer sequence.** For a curve `C` over an algebraically closed field `k`
and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

(blueprint: `sk-prop-h2`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two [IsAlgClosed k] (f : C ⟶ Spec (.of k))
    [IsCurve f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 2 ≃+
      C.CohomologicalPicardGroup ⧸
        (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).range) := by
  have hn' : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨α, β, hα, hαβ, -⟩ := C.exists_exact_sheafH_rootsOfUnitySheaf_two n hn'
  have := subsingleton_cohomologicalBrauerGroup f
  rw [← hα]
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective α
    fun y ↦ (hαβ y).1 (Subsingleton.elim _ _)).symm⟩

end AlgebraicGeometry.IsCurve
