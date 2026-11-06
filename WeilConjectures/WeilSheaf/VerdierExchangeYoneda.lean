/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierExchange
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# The Verdier exchange for Weil complexes

Let `f : X ⟶ Y` be a separated morphism of finite type of separated `k₀`-schemes of finite type
over a base `S`, with structure morphisms `a_X = f ≫ a_Y`, and let `G_X`, `G_Y` be right adjoints
of the direct images with compact support `Ra_{X,0}!`, `Ra_{Y,0}!` of Weil complexes. For a Weil
complex `Q` on `S` put `ω_X = G_X Q` and `ω_Y = G_Y Q`. Then, naturally in the Weil complex `M`
on `X`,

`RHom(Rf₀! M, ω_Y) ≅ Rf_* RHom(M, ω_X)`

(blueprint: `fix-cor-verdier-exchange`). The proof is the Yoneda argument of
`fix-lem-tensor-adjunction`: for a test Weil complex `T` on `Y`,

`Hom(T, RHom(Rf₀! M, ω_Y)) = Hom(Rf₀! M ⊗ T, ω_Y) = Hom(Rf₀!(M ⊗ f^* T), ω_Y)`
`= Hom(Ra_{X,0}!(M ⊗ f^* T), Q) = Hom(M ⊗ f^* T, ω_X) = Hom(f^* T, RHom(M, ω_X))`
`= Hom(T, Rf_* RHom(M, ω_X))`,

all natural in `M` and `T`, using the tensor–hom adjunction of the native derived tensor product
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison`), the compact-support
projection formula (`AlgebraicGeometry.WeilComplex.nonempty_nativeCompactProjectionLeft_iso`),
the composition law `Ra_{X,0}! ≅ Ra_{Y,0}! ∘ Rf₀!` and the adjunction `f^* ⊣ Rf_*`. In particular
no exceptional inverse image `Rf^!` along `f` is needed.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensorCurryYonedaIso` and
  `AlgebraicGeometry.WeilComplex.nativeConstructibleTensorCurryYonedaIso`: the tensor–hom
  adjunction, natural in both variables.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_op_comp_iso_of_adjunction`: the
  exchange, natural in `M`.
-/
