/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal
import Sheaf.AlgebraicGeometry.EtaleOpenProjectionExchange
import Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Sheaf.Paper.ProjectionMateExact
import Sheaf.Paper.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# Coefficient-first compact-support projection maps commute with etale exchange

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-asd-smooth-generic-direct-image.md`,
proof, last paragraph (compatibility implicit in transporting the internal adjunction through
compact-support exchange); Stacks Project, Tags 0E48, 0GL1 and 03S6
(blueprint: lem-asd-compact-projection-exchange).

The compact-support projection map is taken with the coefficient first, as in
lem-amb-proper-coproducts-projection: the upstream right-coefficient projection map
`AlgebraicGeometry.Etale.projectionMap` (proper projection of the compactification followed by
the inverse open tensor comparison) conjugated by the canonical signed derived symmetry
`AlgebraicGeometry.Etale.derivedTensorSymmetry`. The exchange map is the upstream
`AlgebraicGeometry.Etale.rightDerivedLowerShriekBaseChangeMap`. The upstream theorem
`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap` is the
right-coefficient form of the statement (step 5 of the proof below).

## Main declarations

- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst`: the map
  `Π_{f,Q,M} : Q ⊗ᴸ Rf_!M ⟶ Rf_!(Lf^*Q ⊗ᴸ M)`.
- `AlgebraicGeometry.Etale.compactProjectionMapCoeffFirst_baseChangeMap`: the statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

-- As in the upstream module `LowerShriekProjectionExchange`: search the braiding of
-- `ModuleCat Λ` through its symmetric structure, so that the monoidal structures agree.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

/-- The canonical compact-support projection map with the coefficient first,
`Π_{f,Q,M} : Q ⊗ᴸ Rf_!M ⟶ Rf_!(Lf^*Q ⊗ᴸ M)`: the signed symmetry, the projection map
`projectionMap` of the chosen compactification (proper counit-defined projection map followed
by the inverse extension-by-zero tensor comparison), and `Rf_!` of the signed symmetry.
Source: blueprint `lem-asd-smooth-generic-direct-image.md`, proof, last paragraph; Stacks
Project, equation-projection-formula-map and lemma-j-shriek-and-tensor (Tag 0GL1), with the
coefficient-first convention of lem-amb-proper-coproducts-projection
(blueprint: lem-asd-compact-projection-exchange). -/
noncomputable def compactProjectionMapCoeffFirst {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj Q).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ⟶
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj M) :=
  ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) Y).hom.app Q).app
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
    ((projectionMap _ f).app M).app Q ≫
    (R(f)_![ModuleCat.{u + 1} Λ]).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app M).app
        (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q))

/-- **Compact-support projection maps commute with etale exchange.** For a cartesian square
`g' ≫ f = f' ≫ g` (`v = g`, `v_X = g'`) with `f` and `f'` compactifiable, finite commutative
coefficients and arbitrary unbounded `M ∈ D(X_et, Λ)`, `Q ∈ D(Y_et, Λ)`,
`b_{Lf^*Q ⊗ M} ∘ Lg^*(Π_{f,Q,M}) = Π_{f',Lg^*Q,Lg'^*M} ∘ (1 ⊗ b_M)`, after the tensor
comparison `Lg^*(Q ⊗ Rf_!M) ⟶ Lg^*Q ⊗ Lg^*Rf_!M` on the source and the tensor comparison
followed by `Lg'^*Lf^*Q ≅ Lf'^*Lg^*Q` on the target. Here `b` is
`rightDerivedLowerShriekBaseChangeMap`: the proper exchange of the compactification followed by
extension-by-zero base change, then the comparison `Rf'_!(c') ≅ R(f')_!` of the base-changed
compactification with the chosen one. No boundedness or constructibility is assumed.
Source: blueprint `lem-asd-smooth-generic-direct-image.md`, proof, last paragraph; Stacks
Project, Tag 0E48 (remark-compatible-with-diagram), Tags 0GL1, 03S6
(blueprint: lem-asd-compact-projection-exchange).

Proof (the node's proof, step by step):
1. Fix the compactification `X →j X̄ →p S` and its base change `(j', p')`, `a : X̄' ⟶ X̄`,
   `u = v_X`. Let `P_f(M,Q) = Rp_*(γ_{j;M,p^*Q}) ∘ π_{p;j_!M,Q}` (the right-coefficient
   projection map `projectionMap`), `e_E : v^*Rp_*E ⟶ Rp'_*a^*E` the proper exchange and
   `β_M : a^*j_!M ⟶ j'_!u^*M` the open base change; then `b_M = Rp'_*(β_M) ∘ e_{j_!M}`.
   Uses: def-amb-etale-compact-support, def-kun-projection-formula-map, sbc-def-base-change-map,
   sbc-prop-extension-by-zero-and-arbitrary-base-change, lem-pur-etale-open-derived-tensor.
2. Apply lem-weil-pbc-ringed-exchange-tensor-coherence to the square `(p, p', v, a)` with
   `E = j_!M` and coefficient `Q`: with `θ : p'^*v^*Q ≅ a^*p^*Q` and
   `d_E = (1 ⊗ θ⁻¹) t_a`, `Rp'_*(d_E) e_{E ⊗ p^*Q} v^*(π_{p;E,Q}) = π_{p';a^*E,v^*Q}(e_E ⊗ 1) t_v`.
3. Apply lem-asd-open-projection-exchange to `(j, j', a, u)`, `E = M`, `N = p^*Q`, with
   `O = M ⊗ f^*Q`, and identify the composition comparisons by
   lem-kun-derived-pullback-composition-monoidal:
   `β̃_O a^*(γ_{j;M,p^*Q}) = γ_{j';u^*M,p'^*v^*Q} (β_M ⊗ 1) d_E`.
4. Naturality of proper exchange at `γ = γ_{j;M,p^*Q}` gives
   `e_{j_!O} v^*Rp_*(γ) = Rp'_*a^*(γ) e_{E ⊗ p^*Q}`; expanding `b_O v^*P_f` with step 1 and
   substituting step 3 gives `Rp'_*(γ') Rp'_*(β_M ⊗ 1) Rp'_*(d_E) e_{E ⊗ p^*Q} v^*(π_p)`.
5. Replace the last three factors by the right side of step 2 and use naturality of `π_{p'}`
   in its first argument (lem-weil-pbc-ringed-projection-mate-exact) at `β_M`: the composite is
   `P_{f'}(u^*M, v^*Q) (b_M ⊗ 1) t_v`. This right-coefficient identity is the upstream theorem
   `projectionMap_rightDerivedLowerShriekBaseChangeMap`.
6. By lem-amb-proper-coproducts-projection the coefficient-first map is
   `Π_{f,Q,M} = Rf_!(σ_{M,f^*Q}) P_f(M,Q) σ_{Q,Rf_!M}`. Conjugate step 5 by the symmetries using
   naturality of `σ` (lem-kun-tensor-sym) and its compatibility with the pullback tensor
   comparison (lem-kun-inverse-image-monoidal: bidegree `(r,s)` and sign `(-1)^{rs}` are
   unchanged); `b_M ⊗ 1` becomes `1 ⊗ b_M` and `P_f, P_{f'}` become `Π_f, Π_{f'}`. -/
theorem compactProjectionMapCoeffFirst_baseChangeMap
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (Q : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    L((g)^*[ModuleCat.{u + 1} Λ]).map (compactProjectionMapCoeffFirst Λ f Q M) ≫
        (rightDerivedLowerShriekBaseChangeMap Λ sq).app
          (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).obj M) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((leftDerivedUpperStarTensorComparison _ g').app
            (L((f)^*[ModuleCat.{u + 1} Λ]).obj Q)).app M) ≫
        (R(f')_![ModuleCat.{u + 1} Λ]).map
          (((-⊗ᴸ-(X')[ModuleCat.{u + 1} Λ]).map
            (derivedSquareUpperStarIsoInvApp _ sq.toCommSq Q)).app
              (L((g')^*[ModuleCat.{u + 1} Λ]).obj M)) =
      ((leftDerivedUpperStarTensorComparison _ g).app Q).app
          ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ≫
        ((-⊗ᴸ-(Y')[ModuleCat.{u + 1} Λ]).obj (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q)).map
          ((rightDerivedLowerShriekBaseChangeMap Λ sq).app M) ≫
        compactProjectionMapCoeffFirst Λ f' (L((g)^*[ModuleCat.{u + 1} Λ]).obj Q)
          (L((g')^*[ModuleCat.{u + 1} Λ]).obj M) := by
  sorry

end Etale

end AlgebraicGeometry
