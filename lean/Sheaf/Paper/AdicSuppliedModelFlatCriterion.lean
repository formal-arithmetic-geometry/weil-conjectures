/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.LevelwiseAdicTruncations

/-! # The supplied-model half of the Padic flatness criterion -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Ambient and supplied common-model cohomology flatness agree.
Source: blueprint integral truncations, hypothesis paragraph, steps 9--11 of
lem-weil-pbc-adic-tor-flat-cohomology
(blueprint: lem-weil-pbc-adic-flat-iff-supplied-model-flat).

Proof: each bounded adic-lisse supplied complex is complete by torsion-limit
completeness and the constant/completed coefficient equivalence. Exact stratum and
slice restrictions preserve completed coefficients, countable products and the Roos
completion triangle, so the restricted ambient complex is complete too. The supplied
normalization equations identify their quotient towers. Sequential evaluation
fullness lifts this to an isomorphism of strict derived towers. Derived limit and
Koszul reconstruction identify the model with the restricted ambient complex.
Exact inverse image therefore identifies all cohomology sheaves. It preserves
flatness by the tensor comparison. Conversely choose a supplied system from uniform
constructibility and detect the kernel of tensoring every injection on its stratum
covers. Noetherian stratum detection makes that kernel zero globally. Tensor is
right exact, giving ambient flatness. Zero objects and empty strata need no separate
nonzero hypothesis. -/
theorem pbc_adic_flat_iff_supplied_model_flat
    (T : Scheme.{u}) [IsNoetherian T]
    (_hdim : ∃ n : ℕ, topologicalKrullDim T ≤ n)
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hl : ∀ t : T, IsUnit (l : T.presheaf.stalk t))
    (K : PbcBoundedConstructibleComplete T (pbcPadicCoefficientDatum l E)) :
    (∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := pbcAdicCompletion T (pbcPadicCoefficientDatum l E))
        ((DerivedCategory.homologyFunctor _ q).obj K.obj)) ↔
    ∀ (d₀ d₁ : ℤ), d₀ ≤ d₁ → ∀ (S : Stratification T)
        (V : ∀ α : Fin S.n, Sieve (⊤_ (S.domain α).ProEt)),
        (∀ α : Fin S.n, V α ∈ ProEt.topology (S.domain α) (⊤_ (S.domain α).ProEt)) →
        ∀ L : ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt),
            V α f → AdicTowerLocalModel (pbcPadicCoefficientDatum l E) (U.hom ≫ S.immersion α)
              (pbcReductionAdicTower T (pbcPadicCoefficientDatum l E) K.obj) d₀ d₁,
          ∀ (α : Fin S.n) (U : (S.domain α).ProEt)
            (f : U ⟶ ⊤_ (S.domain α).ProEt) (hf : V α f) (q : ℤ),
            SheafOfModules.IsFlatOnSite (J := ProEt.topology U.left)
              (R := (adicTowerInverseImage (U.hom ≫ S.immersion α)).obj
                (pbcAdicCompletion T (pbcPadicCoefficientDatum l E)))
              ((DerivedCategory.homologyFunctor _ q).obj
                (DerivedCategory.Q.obj (L α U f hf).complex)) := by
  sorry

end AlgebraicGeometry.Scheme
