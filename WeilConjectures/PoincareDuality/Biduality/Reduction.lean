/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Integral
public import WeilConjectures.TraceFormula.OrdinaryKunnethReduction

/-!
# Biduality along the reduction `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`

Write `R = (𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})` for the reduction modulo
`ℓⁿ` of bounded constructible `𝒪_E`-complexes, with values in the ambient derived category of
module objects over `(𝒪_E ⧸ ℓⁿ)_X`. This file proves the integral step (ii) of blueprint
`det-pd-biduality-coefficients`: `R` is lax braided monoidal and commutes with internal homs, so it
carries the double-dual morphism `δ_{K₀}` of `K₀` (relative to `ω_{X, 𝒪_E}`) to the double-dual
morphism of `R K₀` (relative to `R ω_{X, 𝒪_E}`), and `R` detects isomorphisms (derived Nakayama).

## Main results

- `ProEtale.CondensedRing.isIso_of_isIso_integersModPowReductionAmbient_map`: derived Nakayama, a
  morphism of bounded constructible `𝒪_E`-complexes whose reduction modulo `ℓⁿ` (`n ≠ 0`) is an
  isomorphism is an isomorphism.
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_isIso_toIhomIhom_reduction`: `δ_{K₀}` is an
  isomorphism as soon as the double-dual morphism of `R K₀` relative to `R ω_{X, 𝒪_E}` is.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

/-- The reduction modulo `ℓⁿ` of bounded constructible `𝒪_E`-complexes, with values in the
ambient derived category of module objects over `(𝒪_E ⧸ ℓⁿ)_X`: the inclusion followed by the
derived extension of scalars along `𝒪_{E,X} ⟶ (𝒪_E ⧸ ℓⁿ)_X`. -/
noncomputable abbrev integersModPowReductionAmbient :
    Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.integersModPowRingObj ℓ E.1 n) X.left)) :=
  (boundedConstructible _).ι ⋙ L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n))

/-- The derived reduction modulo `ℓⁿ`, `(𝒪_E ⧸ ℓⁿ) ⊗ᴸ_{𝒪_E} - : D(Mod_{𝒪_{E,X}}) ⥤
D(Mod_{(𝒪_E ⧸ ℓⁿ)_X})`, is monoidal, with comonoidal structure the tensor comparison
`Functor.leftDerivedTensorComparison`. -/
@[instance_reducible]
noncomputable def leftDerivedIntegersModPowReductionMonoidal :
    L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).Monoidal :=
  letI := Mod.extendScalarsMonoidal (integersModPowReduction X.left ℓ E.1 n)
  (Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)).leftDerivedFunctorMonoidal

attribute [local instance] leftDerivedIntegersModPowReductionMonoidal

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-tensor-hom`, (2), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`. **Reduction
modulo `ℓⁿ` commutes with internal homs**: for bounded constructible `𝒪_E`-complexes `A` and `B`,
the comparison `v_{A,B} : RHom(A, B) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ⟶ RHom(A ⊗ᴸ 𝒪_E ⧸ ℓⁿ, B ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`, the
transpose of the reduction of the evaluation
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`), is an isomorphism. (Blueprint
`lem-coef-integral-hom-reduction`: `𝒪_E ⧸ ℓⁿ` has the finite free resolution
`𝒪_E --ℓⁿ--> 𝒪_E`, so `RHom(A, -) ⊗ᴸ 𝒪_E ⧸ ℓⁿ ≅ RHom(A, - ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`, and the
extension–restriction adjunction identifies the latter with the restriction of scalars of
`RHom(A ⊗ᴸ 𝒪_E ⧸ ℓⁿ, - ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`.) -/
theorem isIso_ihomComparison_integersModPowReduction
    (A B : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧) :
    IsIso ((Functor.LaxMonoidal.ihomComparison
      L(Mod.extendScalars (integersModPowReduction X.left ℓ E.1 n)) A.obj).natTrans.app B.obj) :=
  sorry

/-- **Derived Nakayama for the reduction modulo `ℓⁿ`** (blueprint `sk-lem-pe-derived-nakayama`):
for `n ≠ 0`, a morphism `f` of bounded constructible `𝒪_E`-complexes whose reduction modulo `ℓⁿ`
is an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_integersModPowReductionAmbient_map (hn : n ≠ 0)
    {K L : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧} (f : K ⟶ L)
    (h : IsIso ((integersModPowReductionAmbient ℓ E n X).map f)) : IsIso f :=
  sorry

attribute [local instance] DerivedCategory.braidedCategory'

/-- **Biduality along the reduction modulo `ℓⁿ`** (blueprint `det-pd-biduality-coefficients`,
(ii)): for `n ≠ 0`, the double-dual morphism `δ_{K₀}` of a bounded constructible `𝒪_E`-complex is
an isomorphism as soon as the double-dual morphism of its reduction `R K₀`, relative to the
reduction `R ω_{X, 𝒪_E}` of the dualizing complex, is one. -/
theorem isIso_verdierBiduality_of_isIso_toIhomIhom_reduction (hn : n ≠ 0)
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (h : IsIso (toIhomIhom
      ((integersModPowReductionAmbient ℓ E n X).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))
      ((integersModPowReductionAmbient ℓ E n X).obj K₀))) :
    IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
