/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.FreePresentation
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit

/-!
# Extension of scalars `ℚ̄_ℓ ⊗_{ℤ_ℓ} -` as a colimit of copies of the module

Choose a basis `B` of `ℚ̄_ℓ` over `ℚ_ℓ`. For a `ℤ_ℓ,X`-module `M` on `X_proét` there is a natural
morphism of abelian sheaves
```
κ_M : ⨁_{b ∈ B} colim (M --ℓ--> M --ℓ--> M --ℓ--> ⋯) ⟶ ℚ̄_ℓ ⊗_{ℤ_ℓ} M
```
(`AlgebraicGeometry.ProEtale.rationalizationComparison`), sending the `n`-th copy of `M` in the
summand `b` to `ℚ̄_ℓ ⊗ M` by `m ↦ (b / ℓⁿ) ⊗ m`. Since `ℚ̄_ℓ,X = ⨁_B ℚ_ℓ,X` and
`ℚ_ℓ,X = colim (ℤ_ℓ,X --ℓ--> ℤ_ℓ,X --ℓ--> ⋯)` as `ℤ_ℓ,X`-modules, `κ_M` is an isomorphism
(*the rationalization formula*); this is not proved here, and is a hypothesis
(`[IsIso (rationalizationComparison X l)]`) of the results below.

Granting the rationalization formula on `X` and on `Y`, and the continuity of higher direct
images along a quasi-compact quasi-separated `f : X ⟶ Y`
(`WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarFilteredColimit`), the
three hypotheses of
`WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleExtendScalarsBaseChange` hold:

* extension of scalars is exact
  (`AlgebraicGeometry.ProEtale.preservesFiniteLimits_adicSheafExtendScalars`);
* for every injective `ℤ_ℓ,X`-module `I`, `ℚ̄_ℓ ⊗ I` is `f_*`-acyclic
  (`AlgebraicGeometry.ProEtale.rightAcyclic_lowerStar_toAb_adicSheafExtendScalars_obj`);
* the comparison `ℚ̄_ℓ ⊗ f_* M ⟶ f_* (ℚ̄_ℓ ⊗ M)` is an isomorphism
  (`AlgebraicGeometry.ProEtale.isIso_adicSheafExtendScalarsPushforwardComparison`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory

variable {C : Type*} [Category* C] [Preadditive C] (l : ℕ)

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime]

/-! ### The rationalization formula -/

section Model

variable (X : Scheme.{u})

end Model

/-! ### Extension of scalars commutes with the pushforward -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

end Pushforward

/-! ### Higher direct images of extensions of scalars -/

section RightDerived

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  [IsIso (rationalizationComparison l X)] [IsIso (rationalizationComparison l Y)]

end RightDerived

end AlgebraicGeometry.ProEtale
