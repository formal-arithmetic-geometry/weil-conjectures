/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.TraceFormula.Specialization.DefectLocal

/-!

# Generic vanishing of the defect along a principal divisor

Let `X` be a normal separated `k`-scheme of finite type, `Z = V(h)` the effective Cartier divisor
of a nonzero global function `h`, and `L` a bounded constructible `ℚ̄_ℓ`-complex on `X` with
`Li^* L = 0`. The defect `C_{X,Z}(L)` of `ProEtale.CondensedRing.specializationDefect` vanishes at
every generic point of `Z`, that is, over a dense open subset of `Z`
(`ProEtale.CondensedRing.exists_dense_isZero_specializationDefect`). This is the node
`det-sp-generic-divisor` of the blueprint subsection `sk-lem-tf-sp-generic-divisor`, stated here
for `ℚ̄_ℓ`-coefficients as an input of the proof of blueprint
`det-sp-zero-section-affine-space`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- **Generic vanishing of the defect along a principal divisor** (blueprint
`det-sp-generic-divisor`, a node of the subsection `sk-lem-tf-sp-generic-divisor`, for
`ℚ̄_ℓ`-coefficients): let `X` be normal, `Z = V(h)` the effective Cartier divisor of a nonzero
global function `h`, and `L` bounded constructible with `Li^* L = 0`. Then the defect `C_{X,Z}(L)`
vanishes at every generic point of `Z`: there is a dense open `U ⊆ Z` such that the restriction of
`C_{X,Z}(L)` to the inverse image of `U` in `N_⊥ Z ≅ Z ⊗ k'` is zero. -/
theorem exists_dense_isZero_specializationDefect (hX : IsNormalScheme X.left)
    {h : Γ(X.left, ⊤)} (hh : h ≠ 0) {I : X.left.IdealSheafData}
    (hI : I = IdealSheafData.ofIdealTop (Ideal.span {h}))
    (L : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hL : IsZero ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (centreι X I)).obj L)) :
    ∃ U : (centre X I).left.Opens, Dense (U : Set (centre X I).left) ∧
      IsZero ((L((((constantSpecialFibreProj k' (centre X I)) ⁻¹ᵁ U).ι)^*⟦
        Profinite.padicAlgClRingObj ℓ⟧)).obj
        (specializationDefect X I k' (Profinite.padicAlgClRingObj ℓ) L.obj)) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
