/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.StrictWeilComplexTrace

/-!
# Compatibility of the trace formula with the coefficient comparisons

For a homomorphism `R → S` of finite coefficient rings whose exponent is invertible on `X`, the
categorical traces of the global Frobenius operator `F_{c,m}` on `RΓ_c(X, K)` and of the local
Frobenius operators `F_{x,m}` on the stalks `K_x̄` of a strict Weil complex `(K, φ)` over `R` map
to those of its scalar extension `(K_S, φ_S)`
(`AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_globalFrobenius_extendScalars`,
`AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_localFrobenius_extendScalars`). Hence an
identity `tr_R(F_{c,m}) = ∑ₓ tr_R(F_{x,m})` over `R` is carried to the same identity over `S`
(`AlgebraicGeometry.ProEtale.StrictWeilComplex.trace_globalFrobenius_extendScalars_eq_sum`):
the trace formula is compatible with the coefficient comparisons between finite coefficient
rings. The compatibility with the reductions `𝒪_E → 𝒪_E ⧸ π_Eⁿ` is
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_globalOperatorFamily` and
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.exists_trace_eq_localOperatorFamily`, and
the one with the extension `𝒪_E → E` is
`AlgebraicGeometry.Etale.AdicSystem.FrobeniusSystem.trace_smul_map_eq_finsum_trace`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.StrictWeilComplex

open Scheme

attribute [local instance] DerivedCategory.braidedCategory'

variable {R : Type (u + 1)} [CommRing R] [IsNoetherianRing R] {k : Type u} [Field k]
  {X : Scheme.{u}} {aX : X ⟶ Spec (.of k)} {g : X ≅ X} (c : Compactification aX)
  {gZ : c.Z ⟶ c.Z} (hi : IsPullback g.hom c.i c.i gZ) (hg : CommSq gZ c.g c.g (𝟙 _))
  (S : Type (u + 1)) [CommRing S] [Algebra R S] [Finite R] [Finite S]
  [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent R X]

/-- If the trace formula `tr_R(F_{c,m} ∣ RΓ_c(X, K)) = ∑_{x ∈ s} tr_R(F_{x,m} ∣ K_x̄)` holds for
a strict Weil complex `(K, φ)` over `R`, with the traces the scalars `a` and `b x`, then it holds
for its scalar extension `(K_S, φ_S)` along `R → S`, with the traces the images of `a` and `b x`. -/
theorem trace_globalFrobenius_extendScalars_eq_sum
    (W : StrictWeilComplex (ModuleCat.{u + 1} R) g) (m : ℕ)
    (s : Finset {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x})
    [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj)]
    [HasRightDual (Rf_!(c)[ModuleCat.{u + 1} S].obj (W.extendScalars S aX).obj.obj)]
    [HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
      (Rf_!(c)[ModuleCat.{u + 1} R].obj W.obj.obj))]
    [∀ x : {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x},
      HasRightDual (L((x.1)^*[ModuleCat.{u + 1} R]).obj W.obj.obj)]
    [∀ x : {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x},
      HasRightDual (L((x.1)^*[ModuleCat.{u + 1} S]).obj (W.extendScalars S aX).obj.obj)]
    [∀ x : {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x},
      HasRightDual (L(sheafExtendScalars (algebraMap R S) (Spec (.of k))).obj
        (L((x.1)^*[ModuleCat.{u + 1} R]).obj W.obj.obj))]
    {a : R} (ha : trace (W.globalFrobenius c hi hg m) = a • 𝟙 _)
    {b : {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x} → R}
    (hb : ∀ x, trace (W.localFrobenius m x.1 x.2) = b x • 𝟙 _) (h : a = ∑ x ∈ s, b x) :
    trace ((W.extendScalars S aX).globalFrobenius c hi hg m) =
      ∑ x ∈ s, trace ((W.extendScalars S aX).localFrobenius m x.1 x.2) := by
  rw [trace_globalFrobenius_extendScalars_of_eq_smul c hi hg S W m ha,
    Finset.sum_congr rfl fun (x : {x : Spec (.of k) ⟶ X // x ≫ iterateHom g.hom m = x}) _ ↦
      trace_localFrobenius_extendScalars_of_eq_smul (aX := aX) S W m x.1 x.2 (hb x),
    ← Finset.sum_smul, ← map_sum, h]

end AlgebraicGeometry.ProEtale.StrictWeilComplex
