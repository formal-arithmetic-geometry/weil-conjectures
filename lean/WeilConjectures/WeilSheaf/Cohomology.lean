/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.Stalk

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.WeilSheaf.FiniteBoundaryPositive
import Sheaf.WeilSheaf.AffineCurveRangePositive

/-!
# Compactly supported cohomology of Weil complexes

Let `k₀` be a finite field with algebraic closure `k̄` and geometric Galois Frobenius
`σ : Spec k̄ ≅ Spec k̄`. A Weil sheaf on `Spec k₀` is a constructible `ℓ`-adic sheaf `M` on
the pro-étale site of `Spec k̄` with an isomorphism `φ : σ^* M ≅ M`; its global sections
`Γ(Spec k̄, M)` carry the Frobenius

`Γ(Spec k̄, M) ≅ Γ(Spec k̄, σ^* M) --Γ(φ)--> Γ(Spec k̄, M)`

(`AlgebraicGeometry.WeilSheaf.globalSections`). Every pro-étale cover of `Spec k̄` splits, so
`Γ(Spec k̄, -)` is exact and the cohomology `Hʳ(Spec k̄, M)` of a Weil complex `M` on `Spec k₀`
is `Γ(Spec k̄, 𝓗ʳ M)`, the global sections of its `r`-th cohomology sheaf, with this Frobenius.

The compactly supported cohomology of a Weil complex `K` on a `k₀`-scheme `X` with structure
morphism `a : X ⟶ Spec k₀` is the cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of its
direct image with compact support (`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), with this
Frobenius.

## Main declarations

- `AlgebraicGeometry.WeilComplex.cohomologyFrobeniusModule`: the cohomology of a Weil complex on
  `Spec k₀` as a Frobenius module.
- `AlgebraicGeometry.WeilComplex.compactlySupportedCohomology` and
  `AlgebraicGeometry.WeilSheaf.compactlySupportedCohomology`: compactly supported cohomology
  with its geometric Frobenius.
- `AlgebraicGeometry.WeilComplex.cohomology` and `AlgebraicGeometry.WeilSheaf.cohomology`:
  ordinary cohomology `Hʳ(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_* K)` with its geometric Frobenius.

## Main statements

- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isFinite`: the
  compactly supported cohomology of a finite `k₀`-scheme is concentrated in degree zero.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_isAffine`: the
  compactly supported cohomology of a smooth affine curve is concentrated in degrees `0, 1, 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry


variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

/-- The `r`-th cohomology `Hʳ(Spec k̄, M) = Γ(Spec k̄, 𝓗ʳ M)` of a Weil complex `(M, φ)` on
`Spec k₀`, as a Frobenius module: the global sections of its `r`-th cohomology sheaf, with the
Frobenius induced by the Weil structure (`AlgebraicGeometry.WeilSheaf.globalSections`). -/
noncomputable def cohomologyFrobeniusModule (M : WeilComplex k₀ l (Spec (CommRingCat.of k₀)))
    (r : ℤ) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((homologySheaf r).obj M).globalSections

end WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

-- TODO(unify): thm:proetale-weil-perfectness
/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, K) := Hʳ(Spec k̄, Ra_! K)` of a Weil
complex `K` on a separated `k₀`-scheme `a : X ⟶ Spec k₀` of finite type, with its geometric
Frobenius: the cohomology of the direct image with compact support of `K` along `a`, a Weil
complex on `Spec k₀`. -/
noncomputable def compactlySupportedCohomology (K : WeilComplex k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj K).cohomologyFrobeniusModule r

end WeilComplex

section Ordinary

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

/-- The ordinary cohomology `Hʳ(Y ⊗ k̄, K) := Hʳ(Spec k̄, Ra_* K)` of a Weil complex `K` on a
`k₀`-scheme `a : Y ⟶ Spec k₀` of finite type, with its geometric Frobenius: the cohomology of the
derived direct image of `K` along `a`, a Weil complex on `Spec k₀`. For `a` proper it agrees with
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`. -/
noncomputable def WeilComplex.cohomology (K : WeilComplex k₀ l Y) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((derivedLowerStar (Y ↘ Spec (CommRingCat.of k₀))).obj K).cohomologyFrobeniusModule r

/-- The ordinary cohomology `Hʳ(Y ⊗ k̄, F)` of a Weil sheaf, with its geometric Frobenius: that of
the Weil complex `F` concentrated in degree zero. -/
noncomputable def WeilSheaf.cohomology (F : WeilSheaf k₀ l Y) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (toComplex.obj F).cohomology r

end Ordinary

namespace WeilSheaf

/-- The compactly supported cohomology `H_c^r(X ⊗ k̄, F)` of a Weil sheaf, with its geometric
Frobenius: that of the Weil complex `F` concentrated in degree zero. -/
noncomputable def compactlySupportedCohomology (F : WeilSheaf k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  (toComplex.obj F).compactlySupportedCohomology r

set_option linter.style.haveILetI false in
private theorem isZero_homology_compactSupport_of_neg (G : WeilSheaf k₀ l X)
    {r : ℤ} (hr : r < 0) :
    IsZero ((WeilComplex.homologySheaf r).obj
      ((WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))).obj
        (toComplex.obj G))) := by
  let a := X ↘ Spec (CommRingCat.of k₀)
  let c := HasCompactification.compactification a
    (hf := hasCompactification_of_over (k₀ := k₀) a)
  letI := c.over (k₀ := k₀)
  let E := ProEtaleWeilSheaf.extensionByZero k₀ l c.i
  let P := ProEtaleWeilSheaf.lowerStar k₀ l c.g
  have hge := P.isGE_rightDerivedFunctor_obj_singleFunctor (E.obj G.obj)
  rw [WeilComplex.isZero_homologySheaf_obj_iff]
  exact (_root_.DerivedCategory.isZero_of_isGE (hX := hge) _ 0 r hr).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (P.rightDerivedFunctor.mapIso ((E.mapDerivedCategorySingleFunctor 0).app G.obj)))

private theorem subsingleton_globalSections_of_isZero (F : WeilSheaf k₀ l
    (Spec (CommRingCat.of k₀))) (hF : IsZero F) : Subsingleton F.globalSections.carrier := by
  exact ModuleCat.subsingleton_of_isZero
    ((WeilCoefficients.toModuleCat l).map_isZero ((Sheaf.Γ _ _).map_isZero
      ((ProEtale.AdicSheaf.forget _).map_isZero (isZero_iff_isZero_carrier.mp hF))))

/-- *Cohomology of a finite boundary.* If `X` is finite over `k₀`, then the compactly supported
cohomology `H_c^r(X ⊗ k̄, G)` of a Weil sheaf `G` on `X` vanishes for `r ≠ 0`: after geometric
base change `X` becomes a finite discrete space, whose cohomology is concentrated in degree
zero. The blueprint states this for `G` with stalk weights at most some `w`; the weights play
no role.
(blueprint: `lem-a1-finite-boundary-cohomology`) -/
theorem subsingleton_compactlySupportedCohomology_of_isFinite
    [IsFinite (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ} (hr : r ≠ 0) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  rcases hr.lt_or_gt with hr | hr
  · exact subsingleton_globalSections_of_isZero _
      (isZero_homology_compactSupport_of_neg G hr)
  · exact subsingleton_globalSections_of_isZero _
      (isZero_homology_compactSupport_of_isFinite_of_pos G hr)

/-- *Cohomological range of an affine curve.* If `X` is a smooth affine curve over `k₀` and `G`
is a constructible Weil sheaf on `X`, then `H_c^r(X ⊗ k̄, G) = 0` for `r ∉ {0, 1, 2}`: after a
smooth compactification `j : X ↪ X̄`, `H_c^r(X ⊗ k̄, G) = H^r(X̄ ⊗ k̄, j_!G)` is the cohomology of
a sheaf on a proper curve, of cohomological dimension two.
(blueprint: `lem-zl-affine-curve-range`) -/
theorem subsingleton_compactlySupportedCohomology_of_isAffine [IsAffine X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) {r : ℤ}
    (hr : r < 0 ∨ 2 < r) :
    Subsingleton (G.compactlySupportedCohomology r).carrier := by
  rcases hr with hr | hr
  · exact subsingleton_globalSections_of_isZero _ (isZero_homology_compactSupport_of_neg G hr)
  · exact subsingleton_globalSections_of_isZero _
      (isZero_homology_compactSupport_of_isAffine_of_two_lt G hr)

end WeilSheaf

end AlgebraicGeometry
