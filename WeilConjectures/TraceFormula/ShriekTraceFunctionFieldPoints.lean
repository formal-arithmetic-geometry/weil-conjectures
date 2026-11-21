/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.Statement

/-!
# Trace functions and direct image with compact support, at rational points

Let `f : X ⟶ Y` be a morphism of separated schemes of finite type over a finite field
`k = 𝔽_q`, and `K` a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for the Frobenius, that is for the identity
automorphism of `X`. Give `Rf_! K` the induced Weil structure (`weilLowerShriek`). For every
`m ≥ 1` and every `𝔽_{qᵐ}`-rational point `y` of `Y`,
```
t_{Rf_! K, m}(y) = ∑_{x ∈ X(𝔽_{qᵐ}), f(x) = y} t_{K, m}(x).
```

## Main statements

- `ProEtale.CondensedRing.weilShriekTraceFunction_fieldPoints`.

## Implementation details

The local trace at a rational point `x : Spec 𝔽_{qᵐ} ⟶ X` is taken at the geometric point
`Spec k̄ ⟶ Spec 𝔽_{qᵐ} ⟶ X` given by the embedding `𝔽_{qᵐ} ↪ k̄` chosen by `IsAlgClosed.lift`
(`ProEtale.CondensedRing.fieldPointsEquivFrobeniusFixedPointsRefl`). The statement is the case
of the identity automorphisms in `ProEtale.CondensedRing.weilShriekTraceFunction`, transported
along this bijection between rational points and points of degree `m`.
-/

@[expose] public section

universe u

open CategoryTheory FiniteField FiniteField.galoisExtension

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Trace functions and direct image with compact support.** For a morphism `f : X ⟶ Y` of
separated schemes of finite type over `k = 𝔽_q`, a Weil object `K` on `X` for the Frobenius and an
`𝔽_{q^{m+1}}`-rational point `y` of `Y`, the trace function of `Rf_! K`, with its induced Weil
structure, at `y` is the sum of the trace function of `K` over the `𝔽_{q^{m+1}}`-rational points
`x` of `X` with `f(x) = y`. -/
theorem weilShriekTraceFunction_fieldPoints {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y)
    (K : WeilBoundedConstructible ℓ (Iso.refl X).hom) (m : ℕ)
    (y : Y.hom.fieldPoints (galoisExtension k (m + 1))) :
    weilStalkTraceAlternatingSum ℓ (m + 1) (fieldPointsEquivFrobeniusFixedPointsRefl m y).1
        (fieldPointsEquivFrobeniusFixedPointsRefl m y).2.2
        ((weilLowerShriek ℓ (Iso.refl X) (Iso.refl Y)
          (by simp : (Iso.refl X).hom ≫ f = f ≫ (Iso.refl Y).hom)).obj K) =
      ∑ᶠ x : {x : X.hom.fieldPoints (galoisExtension k (m + 1)) // x.1 ≫ f.left = y.1},
        weilStalkTraceAlternatingSum ℓ (m + 1) (fieldPointsEquivFrobeniusFixedPointsRefl m x.1).1
          (fieldPointsEquivFrobeniusFixedPointsRefl m x.1).2.2 K := by
  rw [weilShriekTraceFunction_of_genericallyHolds ℓ (shriekTraceFunctionGenericallyHolds ℓ k)
    (Iso.refl X) (Iso.refl Y) _ ⟨0, Iso.pow_refl _⟩ K m]
  refine (finsum_comp_equiv ((fieldPointsEquivFrobeniusFixedPointsRefl m).subtypeEquiv
    fun x ↦ ?_)).symm
  simp only [fieldPointsEquivFrobeniusFixedPointsRefl_apply_coe, Category.assoc, cancel_epi]

end AlgebraicGeometry.ProEtale.CondensedRing
