/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier

/-!

# Compatibilities of smooth purity used by the Künneth–Verdier theorem

The Künneth–Verdier theorem for `ℚ̄_ℓ`-coefficients
(`ProEtale.CondensedRing.isIso_kunnethVerdierMap`, blueprint `thm-trf-kunneth-verdier`) uses
smooth purity through a single statement: for `Y` smooth over `k`, the exceptional Künneth map `α : M ⊠ ω_Y ⟶ Rp_X^! M` of the projection
`p_X : X ⨯ Y ⟶ X` is an isomorphism. It is stated here, to be proved in the smooth purity
section.

## Compatibility required from smooth purity

- `ProEtale.CondensedRing.isIso_exceptionalKunnethMap_of_smooth`: purity for the smooth
  projection `p_X`, for arbitrary coefficients, in its compatibility with the purity isomorphism
  of `a_Y` (SGA 4, Exposé XVIII, Théorème 3.2.5, and the compatibility of the trace with base
  change, Théorème 2.9 (Var 4); blueprint `sk-thm-sp-qbar`, `thm-pur-affine-line-purity`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Compatibility required from smooth purity (to be proved there): **purity for a smooth
projection**. Let `Y` be smooth over `k`. The projection `p_X : X ⨯ Y ⟶ X` is the base change of
the smooth morphism `a_Y : Y ⟶ s` along `a_X`, and the exceptional Künneth map
```
α : Lp_X^* M ⊗ᴸ Lp_Y^* ω_Y ⟶ Rp_X^! M,
```
the exceptional adjoint of the projection formula, the compact-support base change of the product
square and the counit `Ra_Y! ω_Y ⟶ ℚ̄_ℓ` (`exceptionalKunnethMap`), is an isomorphism for every
bounded constructible `M` on `X`.

This is smooth purity for arbitrary coefficients, `Rp_X^! M ≅ Lp_X^* M ⊗ᴸ Rp_X^! ℚ̄_ℓ`
(SGA 4, Exposé XVIII, Théorème 3.2.5), combined with the compatibility of the trace with base
change (SGA 4, Exposé XVIII, Théorème 2.9 (Var 4)), which identifies the purity isomorphism
`Rp_X^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of `p_X` with the pullback `Lp_Y^*` of the purity isomorphism
`ω_Y = Ra_Y^! ℚ̄_ℓ ≅ ℚ̄_ℓ(d)[2d]` of `a_Y` (blueprint `sk-thm-sp-qbar`, and
`thm-pur-affine-line-purity`: "compatible with arbitrary base change of `Y`"). The statement does
not involve the trace `smoothTrace`, so it holds for every construction of it. -/
theorem isIso_exceptionalKunnethMap_of_smooth [Smooth Y.hom]
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (exceptionalKunnethMap ℓ (Y := Y) M) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
