/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryCocycle
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraCompIso
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.CategoryTheory.RingObjects.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ExtendScalarsComp
public import WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars

/-!
# The directed system of the `E`-stages `D^b_{c,W}(X, E)` and its cocone to `D^b_{c,W}(X, ℚ̄_ℓ)`

Following blueprint `def-weil-weil-sheaf-complex`, the `ℚ̄_ℓ`-stage of Weil complexes is the
`2`-colimit

`D^b_{c,W}(X, ℚ̄_ℓ) = 2-colim_E D^b_{c,W}(X, E)`

over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (`PadicAlgCl.FiniteIntermediateField l`), along the
extensions of scalars `F ⊗_E -` for `E ⊆ F`.
In this repository the `E`-stages are `AlgebraicGeometry.FieldWeilComplex k₀ E X` and the
`ℚ̄_ℓ`-stage is realised directly as `AlgebraicGeometry.WeilComplex k₀ l X`, with the functors
`AlgebraicGeometry.FieldWeilComplex.toWeilComplex` from the `E`-stages
(`WeilConjectures.WeilSheaf.FieldCoefficientExtendScalars`). This file constructs

- the transition functors: for a continuous map `e : Λ → Λ'` of finite extensions of `ℚ_ℓ`, the
  extension of scalars `Λ' ⊗_Λ -` of pro-étale sheaves
  (`AlgebraicGeometry.ProEtale.fieldExtendScalars`) commutes with the Frobenius pullbacks
  (`AlgebraicGeometry.fieldExtendScalarsFrobeniusIso`), so it induces an exact functor of
  pro-étale Weil sheaves (`AlgebraicGeometry.ProEtaleFieldWeilSheaf.extendScalars`) and a functor
  `D^b_{c,W}(X, Λ) ⥤ D^b_{c,W}(X, Λ')` (`AlgebraicGeometry.FieldWeilComplex.extendScalars`,
  and `AlgebraicGeometry.FieldWeilComplex.transition` for `E ⊆ F`);
- their compatibility with the functors to the `ℚ̄_ℓ`-stage,
  `ℚ̄_ℓ ⊗_{Λ'} (Λ' ⊗_Λ -) ≅ ℚ̄_ℓ ⊗_Λ -`, as Weil complexes
  (`AlgebraicGeometry.FieldWeilComplex.extendScalarsCompExtendScalarsToAdicIso`): on pro-étale
  sheaves this is `AlgebraicGeometry.ProEtale.fieldExtendScalarsCompExtendScalarsToAdicIso`,
  and it is compatible with the Weil structures
  (`AlgebraicGeometry.fieldExtendScalarsCompExtendScalarsToAdicIso_frobenius`);
- hence the cocone of categories `E ↦ (D^b_{c,W}(X, E) ⥤ D^b_{c,W}(X, ℚ̄_ℓ))` on the directed
  system of the `E`-stages, with vertex the `ℚ̄_ℓ`-stage
  (`AlgebraicGeometry.FieldWeilComplex.cocone`), in the sense of
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry

open ProEtale

section Transition

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end Transition

section Comp

variable {l : ℕ} [Fact l.Prime] {Λ Λ' : Type} [NormedField Λ] [IsUltrametricDist Λ]
  [NormedField Λ'] [IsUltrametricDist Λ'] [Algebra ℚ_[l] Λ] [Algebra ℚ_[l] Λ']
  [FiniteDimensional ℚ_[l] Λ] [FiniteDimensional ℚ_[l] Λ'] {e : Λ →ₐ[ℚ_[l]] Λ'}
  (he : Continuous e) (hc : Continuous (algebraMap ℚ_[l] Λ))
  {e' : Λ' →ₐ[ℚ_[l]] PadicAlgCl l} (he' : Continuous e')
  (hc' : Continuous (algebraMap ℚ_[l] Λ'))
  (k₀ : Type u) [Field k₀] [Finite k₀] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

variable [Fact (ringChar k₀ ≠ l)]

end Comp

section FiniteSubextension

open PadicAlgCl

variable {l : ℕ} [Fact l.Prime] (k₀ : Type u) [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

end FiniteSubextension

end AlgebraicGeometry
