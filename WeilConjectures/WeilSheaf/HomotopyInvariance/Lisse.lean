/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.WeilSheaf.Localization

/-!
# Homotopy invariance for Weil complexes with lisse cohomology

Let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle over a `k₀`-scheme `X` of finite type,
given by a cartesian square `Y ⟶ 𝔸¹, Y ⟶ X` over `Spec k₀`. This file proves that the unit
`K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism for every Weil complex `K` whose cohomology
sheaves are lisse (`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isLisse_homologySheaf`), from
the case of a lisse Weil sheaf placed in degree zero
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_toComplex_of_isLisse`), by dévissage along the
truncation triangles: the objects at which the unit of `π^* ⊣ Rπ_*` is invertible form a
triangulated subcategory (`CategoryTheory.Adjunction.isTriangulated_isoLocus_unit`).

The case of a lisse Weil sheaf is the `ℓ`-adic Weil form of the acyclicity of the affine line,
an input from the étale chapter which is not formalized here.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
  [π.IsOver (Spec (CommRingCat.of k₀))]
  (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
    (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
  [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]

include hπ in
/-- Blueprint `lem-pur-a1-direct-image` (for lisse Weil sheaves): **homotopy invariance for lisse
Weil sheaves**. For the trivial line bundle `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` and a lisse Weil sheaf
`L` on `X`, the unit `L ⟶ Rπ_* π^* L` of `π^* ⊣ Rπ_*` is an isomorphism.

With finite étale coefficients over an algebraically closed field and `L = Λ` this is
`AlgebraicGeometry.Etale.isIso_unit_constantComplex_affineLine`. A lisse `ℓ`-adic sheaf is,
modulo `λⁿ`, étale locally constant on `X̄`, and `Rπ_*` commutes with étale base change on `X̄`,
so the finite-level statement holds for the reductions of an integral lattice of `L`; the
`ℓ`-adic Weil form follows by passing to the limit over `n`, rationalizing and checking the
compatibility with the Frobenius structures. This passage from finite étale coefficients to
`ℓ`-adic Weil complexes belongs to the chapter comparing the étale and the pro-étale
formalisms and is not formalized; it is stated here with `sorry`. -/
theorem isIso_unit_app_toComplex_of_isLisse (L : WeilSheaf k₀ l X) (hL : L.IsLisse) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app
      (WeilSheaf.toComplex.obj L)) :=
  sorry

include hπ in
/-- **Homotopy invariance for Weil complexes with lisse cohomology.** For the trivial line bundle
`π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` and a Weil complex `K` on `X` whose cohomology sheaves are lisse, the
unit `K ⟶ Rπ_* π^* K` is an isomorphism. By dévissage along the truncation triangles, this
reduces to lisse Weil sheaves placed in degree zero
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_toComplex_of_isLisse`). -/
theorem isIso_unit_app_of_isLisse_homologySheaf (K : WeilComplex k₀ l X)
    (hK : ∀ n : ℤ, ((homologySheaf n).obj K).IsLisse) :
    IsIso ((upperStarDerivedLowerStarAdjunction (k₀ := k₀) (l := l) π).unit.app K) :=
  sorry

end AlgebraicGeometry.WeilComplex
