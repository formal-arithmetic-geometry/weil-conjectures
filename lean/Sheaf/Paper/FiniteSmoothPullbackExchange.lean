/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteReductionRootCharts

/-! # The specified smooth pullback exchange

Source: blueprint main-20261015, def-pur-smooth-pullback-exchange
(blueprint: def-pur-smooth-pullback-exchange).
The exchange is the literal purity composite with the canonical middle source map.

## Main definitions

- `finiteReductionBaseChangeSource`: the canonical tensor/pullback source map.
- `finiteReductionSmoothExchange`: inverse pulled-back purity, source map, purity.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- The exact realization pullback has its termwise shift comparison.
Source: blueprint base-change statement (blueprint: def-pur-smooth-pullback-exchange).
Proof: the ordinary inverse image is exact and additive, hence its termwise derived
functor commutes with cochain shift. Transport this comparison through the published
realization equivalences, using their termwise shift comparisons. -/
instance finiteReductionPullbackCommShift (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (P.finiteReductionPullback f).CommShift ℤ := by
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  letI := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  exact inferInstanceAs
    (((Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse.mapDerivedCategory ⋙
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).mapDerivedCategory ⋙
      (Scheme.sfIntrinsicModuleEquivalence X P.Ring).functor.mapDerivedCategory).CommShift ℤ)

/-- Pullback composition through the very same realization units as gamma.
Source: blueprint base-change statement, c_(h,g)
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionPullbackCompositor (P : PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReductionPullback (f ≫ g)).obj K ≅
      (P.finiteReductionPullback f).obj ((P.finiteReductionPullback g).obj K) :=
  (Scheme.sfIntrinsicDerivedEquivalence X P.Ring).functor.mapIso
    ((compositionFixedPullbackComp P.Ring f g).app
        ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K) ≪≫
      (P.smoothPurityPullback f).mapIso
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).unitIso.app
          ((P.smoothPurityPullback g).obj
            ((Scheme.sfIntrinsicDerivedEquivalence Z P.Ring).inverse.obj K))))

/-- The canonical inverse-image square from its two compositors and its commutativity.
Source: blueprint base-change statement, middle identification
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionPullbackSquare (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionPullback u).obj ((P.finiteReductionPullback f).obj K) ≅
      (P.finiteReductionPullback f').obj ((P.finiteReductionPullback v).obj K) :=
  (P.finiteReductionPullbackCompositor u f K).symm ≪≫
    eqToIso (congrArg (fun h ↦ (P.finiteReductionPullback h).obj K) sq.w) ≪≫
    P.finiteReductionPullbackCompositor f' v K

/-- The tensor/twist source identification for a square is uniquely fixed in root charts.
This is b_square, with ordinary pullback compositors, tensor pullback and root restriction.
Source: def-pur-smooth-pullback-exchange, middle identification
(blueprint: def-pur-smooth-pullback-exchange).
Proof: trivialize the root line on the base by a primitive root. Tensor pullback
and the termwise shift comparison identify both sides with the shifted double
pullback. The two pullback compositors and the square's equality give the middle
map. Changing the primitive root rescales both sides by the same unit to the same
power, so the composite is independent of that chart. A chart exists because the
base field is algebraically closed and ell differs from its characteristic; its
equation determines the isomorphism uniquely. -/
theorem existsUnique_finiteReductionBaseChangeSource (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    ∃! b : (P.finiteReductionPullback u).obj ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f' d).obj ((P.finiteReductionPullback v).obj K),
      ∀ (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ P.diagonalExponent),
        b = (P.finiteReductionPullback u).mapIso
            (P.finiteReductionSourceTrivialization f d ζ hζ K) ≪≫
          ((P.finiteReductionPullback u).commShiftIso (2 * (d : ℤ))).app _ ≪≫
          (shiftFunctor _ (2 * (d : ℤ))).mapIso
            (P.finiteReductionPullbackSquare u f' f v sq K) ≪≫
          (P.finiteReductionSourceTrivialization f' d ζ hζ
            ((P.finiteReductionPullback v).obj K)).symm := by
  sorry

/-- The source identification of the actual purity-defined base-change square.
Source: def-pur-smooth-pullback-exchange
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionBaseChangeSource (P : PurityFiniteSetting.{u})
    {X X' Y Y' : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v) (d : ℕ) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionPullback u).obj ((P.compositionShiftedPullback f d).obj K) ≅
      (P.compositionShiftedPullback f' d).obj ((P.finiteReductionPullback v).obj K) :=
  (P.existsUnique_finiteReductionBaseChangeSource u f' f v sq d K).choose

section BaseChange
variable (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
variable {X X' Y Y' : Scheme.{u}}
variable [X.Over (Spec (.of P.field.k))] [X'.Over (Spec (.of P.field.k))]
variable [Y.Over (Spec (.of P.field.k))] [Y'.Over (Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (X' ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y ↘ Spec (.of P.field.k))]
variable [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
variable [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
variable (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
variable [u.IsOver (Spec (.of P.field.k))] [v.IsOver (Spec (.of P.field.k))]
variable [f.IsOver (Spec (.of P.field.k))] [f'.IsOver (Spec (.of P.field.k))]
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
variable (sq : IsPullback u f' f v) (d : ℕ)
variable [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f']

/-- Pullback of a finite-Tor constructible object has the required finite-Tor domain.
Source: def-pur-smooth-pullback-exchange, domains
(blueprint: def-pur-smooth-pullback-exchange).
Proof: inverse image is exact, preserves flat modules, and sends a bounded flat
model to a bounded flat model in the same Tor interval. Pull back the finite
constructible stratification and use the canonical finite-coefficient realization.
This proves the intrinsic finiteTorConstructible predicate without any flatness,
smoothness or properness requirement on the base morphism. -/
theorem finiteReductionBaseChangeInput (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y'
      ((P.finiteReductionPullback v).obj K) := by
  sorry

/-- The canonical smooth purity morphism is invertible on its stated domain.
Source: def-pur-smooth-purity-map, tau / Pi / theta
(blueprint: def-pur-smooth-pullback-exchange).
Proof: tau is the specified tensor-shift isomorphism, Pi is the specified diagonal
purity isomorphism, and theta is invertible by thm-pur-cohomological-smoothness.
Tensoring the inverse of Pi preserves its inverse equations. Their composite,
transported through the realization equivalence, is therefore an isomorphism. -/
theorem finiteReductionPurityIsIso (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    IsIso (P.smoothPurityMap f d K hK) := by
  sorry

/-- The actual smooth exchange is the literal purity composite, not a separately
chosen right-adjoint base-change mate. Its middle arrow was fixed above independently.
Source: def-pur-smooth-pullback-exchange, displayed composite
(blueprint: def-pur-smooth-pullback-exchange). -/
def finiteReductionSmoothExchange (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y K) :
    (P.finiteReductionPullback u).obj ((P.compositionExceptional f).obj K) ≅
      (P.compositionExceptional f').obj ((P.finiteReductionPullback v).obj K) := by
  letI := P.finiteReductionPurityIsIso f d K hK
  letI := P.finiteReductionPurityIsIso f' d ((P.finiteReductionPullback v).obj K)
    (P.finiteReductionBaseChangeInput v K hK)
  exact ((P.finiteReductionPullback u).mapIso (asIso (P.smoothPurityMap f d K hK))).symm ≪≫
    P.finiteReductionBaseChangeSource u f' f v sq d K ≪≫
    asIso (P.smoothPurityMap f' d ((P.finiteReductionPullback v).obj K)
      (P.finiteReductionBaseChangeInput v K hK))

end BaseChange

end WeilConjectures.PurityFiniteSetting
