/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.FieldCoefficientCohomology
public import WeilConjectures.WeilSheaf.FieldCoefficientTwoColimit

/-!
# Cohomology at the coefficient stage `ℚ̄_ℓ`

Blueprint `def-weil-ordinary-compact-cohomology` defines, at every coefficient stage `Λ`, the
coefficient complexes `RΓ(Y, K) = Fib_s(Ra_{Y*} K)` and `RΓ_c(Y, K) = Fib_s(Ra_{Y!} K)` of an
object `K` of `D^b_c(Y, Λ)` and their cohomology; for a Weil complex they are applied to its
underlying complex. This file records the stage `Λ = ℚ̄_ℓ`:

- for objects of the derived category of sheaves of `ℚ̄_ℓ,Y`-modules on the pro-étale site
  (the direct model of `D^b_c(Y, ℚ̄_ℓ)`), the construction of
  `WeilConjectures.WeilSheaf.FieldCoefficientCohomology` at the ultrametric field `Λ = ℚ̄_ℓ`
  (`AlgebraicGeometry.ProEtale.algClosedCohomology`,
  `AlgebraicGeometry.ProEtale.algClosedCompactlySupportedCohomology`);
- for objects `(E, K)` of the `2`-colimit model `D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`
  (`AlgebraicGeometry.WeilComplexTwoColimit`), the cohomology of `ℚ̄_ℓ ⊗_E K`
  (`AlgebraicGeometry.WeilComplexTwoColimit.cohomology`,
  `AlgebraicGeometry.WeilComplexTwoColimit.compactlySupportedCohomology`), with its geometric
  Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace ProEtale

variable (l : ℕ) [Fact l.Prime] {Y s : Scheme.{u}} (a : Y ⟶ s)

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the cohomology
`Hⁱ(Y, K) = Hⁱ(Fib_s(Ra_* K))` of a complex `K` of sheaves of `ℚ̄_ℓ,Y`-modules on the pro-étale
site of `Y`, along `a : Y ⟶ s` (for `a` the structure morphism of a separated `k`-scheme of
finite type, `k` algebraically closed); `AlgebraicGeometry.ProEtale.fieldCohomology` at
`Λ = ℚ̄_ℓ`. -/
noncomputable abbrev algClosedCohomology (i : ℤ) :
    _root_.DerivedCategory (FieldSheaf (PadicAlgCl l) Y) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  fieldCohomology a i

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`: the compactly supported
cohomology `Hⁱ_c(Y, K) = Hⁱ(Fib_s(Ra_! K))` of a complex `K` of sheaves of `ℚ̄_ℓ,Y`-modules on the
pro-étale site of `Y`, along `a : Y ⟶ s` admitting a compactification;
`AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology` at `Λ = ℚ̄_ℓ`. -/
noncomputable abbrev algClosedCompactlySupportedCohomology [HasCompactification a] (i : ℤ) :
    _root_.DerivedCategory (FieldSheaf (PadicAlgCl l) Y) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl l)) :=
  fieldCompactlySupportedCohomology a i

end ProEtale

namespace WeilComplexTwoColimit

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`, `2`-colimit model: the
cohomology `Hʳ(X ⊗ k̄, K)` of an object `K = (E, K_E)` of
`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`, with its geometric Frobenius: the cohomology
(`AlgebraicGeometry.WeilComplex.cohomology`) of its image `ℚ̄_ℓ ⊗_E K_E` in the direct
`ℚ̄_ℓ`-stage (`AlgebraicGeometry.WeilComplexTwoColimit.toWeilComplex`). -/
noncomputable def cohomology (K : WeilComplexTwoColimit k₀ l X) (r : ℤ) :
    FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((toWeilComplex k₀ X).obj K).cohomology r

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = ℚ̄_ℓ`, `2`-colimit model: the
compactly supported cohomology `H_cʳ(X ⊗ k̄, K)` of an object `K = (E, K_E)` of
`D^b_{c,W}(X, ℚ̄_ℓ)`, with its geometric Frobenius: that
(`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`) of `ℚ̄_ℓ ⊗_E K_E`. -/
noncomputable def compactlySupportedCohomology [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplexTwoColimit k₀ l X) (r : ℤ) : FrobeniusModule.{u + 1, 0} (PadicAlgCl l) :=
  ((toWeilComplex k₀ X).obj K).compactlySupportedCohomology r

end WeilComplexTwoColimit

end AlgebraicGeometry
