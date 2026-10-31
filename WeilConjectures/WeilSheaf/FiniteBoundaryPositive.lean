/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- Positive cohomology sheaves of compactly supported direct image from a finite scheme vanish.

Source: blueprint sec-deligne-laumon-a1/sk-i-dl-a1-local/
lem-a1-finite-boundary-cohomology.md, positive-degree part; proved as the special case of
`lem-zl-quasi-finite`, part 1.
(blueprint: lem-a1-finite-boundary-cohomology-positive)

Proof: Write a for the structure morphism X → Spec k₀. A finite morphism is separated,
locally quasi-finite, locally of finite type and quasi-compact, and Spec k₀ is quasi-compact,
quasi-separated and of finite type over itself. Hence a is a separated quasi-finite morphism of
finite-type k₀-schemes, and the vanishing of higher direct images with compact support along such
morphisms (`AlgebraicGeometry.isZero_higherLowerShriek_of_quasiFinite`, blueprint
`lem-zl-quasi-finite` part 1: Zariski's main theorem factors a as an open immersion followed by a
finite morphism, extension by zero and finite direct image are exact) gives R^r a_! G = 0 for
every natural r > 0. A positive integer r is such a natural number, and R^r a_! G is by
definition the r-th Weil cohomology sheaf of the compactly supported derived direct image of G
placed in degree zero. This argument uses no stalk-weight assumption. -/
theorem isZero_homology_compactSupport_of_isFinite_of_pos
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : 0 < r) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj G))) := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hr.le
  subst r
  exact isZero_higherLowerShriek_of_quasiFinite (X ↘ Spec (CommRingCat.of k₀)) n
    (by exact_mod_cast hr) G

end AlgebraicGeometry.WeilSheaf
