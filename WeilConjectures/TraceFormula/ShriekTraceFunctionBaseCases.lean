/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale
public import WeilConjectures.TraceFormula.ShriekTraceFunctionInduction

/-!

# The base cases of the sheaf–function compatibility of the Weil lower shriek

By Noetherian induction (`ProEtale.CondensedRing.weilShriekTraceFunction_of_genericallyHolds`),
the sheaf–function compatibility `ProEtale.CondensedRing.ShriekTraceFunctionAt` of the Weil lower
shriek holds along every morphism as soon as it holds generically
(`ProEtale.CondensedRing.ShriekTraceFunctionGenericallyHolds`). This file reduces the generic
statement to two base cases, stated as separate inputs:

- **dimension zero** (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_isFinite_of_etale`, proved in
  `WeilConjectures.TraceFormula.ShriekTraceFunctionFiniteEtale`): `f`
  finite étale. Then `Rf_! = f_*` and the stalk of `f_* K` at `ȳ` is `⊕_{x̄ ↦ ȳ} K_x̄`, on which
  the Frobenius permutes the summands; only the summands at points of degree `n + 1` contribute
  to the trace;
- **curves** (`ProEtale.CondensedRing.shriekTraceFunctionAt_of_smoothOfRelativeDimension_one`):
  `f` smooth of relative dimension one. By compactly supported base change to `ȳ` this is the
  trace formula for a smooth curve over a finite field, deduced from the Lefschetz–Verdier
  formula of the model-Frobenius setting (`WeilConjectures.TraceFormula.LefschetzVerdier`) and
  the vanishing of the local terms of the Frobenius graph away from its fixed points
  (`WeilConjectures.TraceFormula.LocalTermLocality`).

The reduction (`ProEtale.CondensedRing.shriekTraceFunctionGenericallyHolds_of_baseCases`) is
the generic structure of morphisms of finite type: a nonempty `X` with an automorphism of
finite order has a nonempty stable open subscheme whose map to `Y` is a composite of finite
étale maps and smooth maps of relative dimension one, with compatible automorphisms on the
intermediate schemes, so that `ProEtale.CondensedRing.shriekTraceFunctionAt_comp` applies.

## Bridge to the model-Frobenius setting

The curve case needs a comparison between the two settings: the Weil objects of
`WeilConjectures.TraceFormula.Statement` live over the finite field `k` with an automorphism `e`,
those of the Lefschetz–Verdier formula over an algebraically closed field with a model
Frobenius `Φ`. The comparison is the base change of Weil objects from `k` to `k̄`, which is not
yet available; the curve case is therefore stated directly.

## Sorried inputs

- `ProEtale.CondensedRing.shriekTraceFunctionAt_of_smoothOfRelativeDimension_one`;
- `ProEtale.CondensedRing.shriekTraceFunctionGenericallyHolds_of_baseCases`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-- **Dimension zero**: the sheaf–function compatibility holds along a finite
étale morphism `f`. The stalk of `Rf_! K = f_* K` at `ȳ` is the sum of the stalks `K_x̄` over
the geometric points `x̄ ↦ ȳ`, permuted by the Frobenius; the trace only sees the summands at
the points fixed by the Frobenius, which are the points of degree `n + 1`
(`ShriekTraceFunctionAt.of_isFinite_of_etale`, which does not need `e_X` to have finite order).
The hypothesis `_he` is therefore redundant; it is kept so that the statement has the form of the
base case `H₀` of `shriekTraceFunctionGenericallyHolds_of_baseCases`. -/
theorem shriekTraceFunctionAt_of_isFinite_of_etale {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [IsFinite f.left] [Etale f.left] (_he : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  ShriekTraceFunctionAt.of_isFinite_of_etale ℓ eX eY hf

/-- **Curves** (still `sorry`): the sheaf–function compatibility holds along a smooth morphism
`f` of relative dimension one. By compactly supported base change to `ȳ`, it is the trace
formula for the smooth curve `X_ȳ` over a finite field, which follows from the Lefschetz–Verdier
formula for the Frobenius graph on a compactification and the vanishing of the local terms
away from the fixed points (blueprint `thm-trf-grothendieck-lefschetz-finite-ring`, the case of
curves). -/
theorem shriekTraceFunctionAt_of_smoothOfRelativeDimension_one {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
    [SmoothOfRelativeDimension 1 f.left] (he : ∃ m : ℕ, eX.powSucc m = Iso.refl X) :
    ShriekTraceFunctionAt ℓ eX eY hf :=
  sorry

/-- **Generic structure** (still `sorry`): the base cases give the sheaf–function compatibility
generically. A nonempty `X` with an automorphism `e_X` of finite order has a nonempty
`e_X`-stable open `U` whose map to `Y` factors as a composite of finite étale morphisms and
smooth morphisms of relative dimension one between schemes with compatible automorphisms of
finite order (after passing to the quotient by the finite group generated by `e_X`, by generic
smoothness and elementary fibrations), and `shriekTraceFunctionAt_comp` composes the base
cases. -/
theorem shriekTraceFunctionGenericallyHolds_of_baseCases
    (H₀ : ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
      [IsFinite f.left] → [Etale f.left] → (∃ m : ℕ, eX.powSucc m = Iso.refl X) →
      ShriekTraceFunctionAt ℓ eX eY hf)
    (H₁ : ∀ (X Y : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (eX : X ≅ X) (eY : Y ≅ Y) (f : X ⟶ Y) (hf : eX.hom ≫ f = f ≫ eY.hom),
      [SmoothOfRelativeDimension 1 f.left] → (∃ m : ℕ, eX.powSucc m = Iso.refl X) →
      ShriekTraceFunctionAt ℓ eX eY hf) :
    ShriekTraceFunctionGenericallyHolds ℓ k :=
  sorry

/-- The sheaf–function compatibility holds generically, from the two base cases. -/
theorem shriekTraceFunctionGenericallyHolds : ShriekTraceFunctionGenericallyHolds ℓ k :=
  shriekTraceFunctionGenericallyHolds_of_baseCases ℓ k
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ _ he ↦ by
      exact shriekTraceFunctionAt_of_isFinite_of_etale ℓ k eX eY hf he)
    (fun _ _ _ _ _ _ _ _ eX eY _ hf _ he ↦ by
      exact shriekTraceFunctionAt_of_smoothOfRelativeDimension_one ℓ k eX eY hf he)

end AlgebraicGeometry.ProEtale.CondensedRing
