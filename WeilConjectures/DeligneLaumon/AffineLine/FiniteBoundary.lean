/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.WeilSheaf.Finiteness

/-!
# Compactly supported cohomology of a finite scheme

If `Z₀` is finite over `k₀`, the compactly supported cohomology `H_c^r(Z, G)` of a Weil sheaf `G`
on `Z₀` vanishes for `r ≠ 0`: for `r > 0` the higher direct images with compact support along
the quasi-finite structure morphism vanish, and for `r < 0` the direct image with compact support
of a sheaf is concentrated in nonnegative degrees, being the right derived pushforward of the
extension by zero of a sheaf.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

attribute [local instance] AlgebraicGeometry.Compactification.over

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support of a Weil sheaf placed in degree zero has no
cohomology sheaves in negative degrees. -/
theorem WeilComplex.isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg
    {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r < 0) :
    IsZero ((homologySheaf r).obj ((derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj G))) := by
  rw [isZero_homologySheaf_obj_iff]
  let c := HasCompactification.compactification f (hf := hasCompactification_of_over (k₀ := k₀) f)
  let E := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  have e : ((derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj G)).obj ≅
      (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj (E.obj G.obj)) :=
    (ProEtaleWeilSheaf.lowerStar k₀ l c.g).rightDerivedFunctor.mapIso
      ((E.mapDerivedCategorySingleFunctor 0).app G.obj)
  have := (ProEtaleWeilSheaf.lowerStar k₀ l c.g).isGE_rightDerivedFunctor_obj_singleFunctor
    (E.obj G.obj)
  exact ((_root_.DerivedCategory.isGE_iff _ 0).1 this r hr).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso e)

/-- *Cohomology of a finite boundary.* If `X` is finite over `k₀`, then the compactly supported
cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on `X` vanishes for `r ≠ 0`: after geometric
base change `X` becomes a finite discrete space, whose cohomology is concentrated in degree
zero. For `r > 0` this is the vanishing of the higher direct images with compact support along
the quasi-finite structure morphism, for `r < 0` the concentration of the direct image of a sheaf
in nonnegative degrees. The blueprint states this for `G` with stalk weights at most some `w`;
the weights play no role.
(blueprint: `lem-a1-finite-boundary-cohomology`) -/
theorem WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  apply WeilSheaf.subsingleton_globalSections_of_isZero
  rcases hr.lt_or_gt with hr | hr
  · exact WeilComplex.isZero_homologySheaf_derivedLowerShriek_toComplex_of_neg _ G hr
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr.le
    exact isZero_higherLowerShriek_of_quasiFinite (X ↘ Spec (CommRingCat.of k₀)) n
      (by exact_mod_cast hr) G

end AlgebraicGeometry
