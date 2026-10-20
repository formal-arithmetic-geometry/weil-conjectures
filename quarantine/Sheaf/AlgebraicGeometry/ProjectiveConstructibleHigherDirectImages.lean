/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.AlgebraicGeometry.ConstructibleHigherDirectImages
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.ProjectiveConstructibilityFromLine
import Sheaf.AlgebraicGeometry.ProjectiveLineConstructible

/-!
# Projective direct-image constructibility

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-fin-projective-constructibility-complete.md`
(blueprint: thm-fin-projective-constructibility-complete).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every projective morphism between finite-type schemes over `k` satisfies `C(f)`
for the fixed finite coefficient ring and invertible annihilating integer.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`thm-fin-projective-constructibility-complete.md`
(blueprint: thm-fin-projective-constructibility-complete).

Proof plan:
1. Fix the finite coefficient ring `Λ` and integer `N` of `def-finrepair-property-c`.
   For every finite-type `k`-scheme `T`, `thm-fin-projective-line-constructible`
   gives constructibility of every nonnegative higher direct image of every
   constructible `Λ`-module sheaf along the projective-line projection over `T`.
   By `def-finrepair-property-c`, this is `C` for that projection, with precisely
   the same coefficients and annihilating integer. Since `T` is arbitrary, this
   supplies the universal projective-line hypothesis of the reduction lemma.
2. Apply `lem-finrepair-projective-from-line` to obtain `C(f)` for every projective
   morphism between finite-type `k`-schemes. Projectivity is the closed-embedding
   convention of `def-pc-projective-morphism`. This asserts neither arbitrary
   proper direct-image constructibility nor uniform vanishing. -/
theorem hasConstructibleHigherDirectImages_of_isProjective
    (k : Type u) [Field k] (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X S : Scheme.{u}} [X.Over (Spec (.of k))] [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (hX : IsSmoothBaseChangeCoefficients N Λ X)
    (hS : IsSmoothBaseChangeCoefficients N Λ S) (f : X ⟶ S) [IsProjective f] :
    HasConstructibleHigherDirectImages k N Λ hX hS f := by
  classical
  apply hasConstructibleHigherDirectImages_of_projectiveLine k N Λ ?_ hX hS f
  intro T _ _ _ hP hT q F hF
  by_cases hTempty : IsEmpty T
  · let strata : Scheme.Stratification T :=
      { n := 0
        stratum := fun i ↦ Fin.elim0 i
        isLocallyClosed_stratum := fun i ↦ Fin.elim0 i
        isConstructible_stratum := fun i ↦ Fin.elim0 i
        iUnion_stratum_eq_univ := by
          ext t
          exact isEmptyElim t
        pairwise_disjoint_stratum := fun i ↦ Fin.elim0 i
        domain := fun i ↦ Fin.elim0 i
        immersion := fun i ↦ Fin.elim0 i
        isImmersion := fun i ↦ Fin.elim0 i
        range_immersion := fun i ↦ Fin.elim0 i }
    exact ⟨strata, fun i ↦ Fin.elim0 i⟩
  · obtain ⟨t⟩ := not_isEmpty_iff.mp hTempty
    have hNk : (N : k) ≠ 0 := by
      intro hNkzero
      have hNTzero : (N : Γ(T, ⊤)) = 0 := by
        have h := congrArg
          (((Scheme.ΓSpecIso (.of k)).inv ≫ (T ↘ Spec (.of k)).appTop).hom) hNkzero
        simpa only [map_natCast, map_zero] using h
      have hunit := hT.2.2.2.map (T.presheaf.germ ⊤ t trivial).hom
      have hzero := congrArg (T.presheaf.germ ⊤ t trivial).hom hNTzero
      rw [map_natCast, map_zero] at hzero
      rw [map_natCast] at hunit
      exact hunit.ne_zero hzero
    have hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)) :=
      ⟨hT.1, hT.2.1, hT.2.2.1, by
        simpa only [map_natCast] using
          hNk.isUnit.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
    exact isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
      k T N Λ hcoeff F hF (q : ℤ)

end AlgebraicGeometry.Etale
