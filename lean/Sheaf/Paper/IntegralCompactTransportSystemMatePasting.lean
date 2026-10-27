/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.SixFunctors.SchemeFrobenius
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.FrobeniusGeometricExchange
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Integral compact-support transport mate pasting

Source: blueprint main-20261015, `prop-trf-rational-frobenius-integral-model.proof.md`,
clause (3), and `thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting).

All operations are the landed simultaneous-system operations. The compactification is
base changed from the supplied model over k₀; exchanges and compositors are constructed,
rather than parameters. The equality precedes evaluation and inverse-limit realization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.FrobeniusExchange

variable (D : FiniteFieldDatum.{u})

/-- The r-th power of geometric coefficient Frobenius, in the scheme endomorphism monoid.
Source: `def-trf-scheme-frobenius`, geometric Galois Frobenius
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
abbrev compactTransportPower (W₀ : Over (Spec (.of D.k₀))) (r : ℕ) :=
  End.of (galois D W₀) ^ r

set_option linter.defProp false in
/-- Horizontal pasting of the actual geometric Frobenius square r times.
Source: Stacks 03SM; the Cartesian square of `def-weil-frobenius-square-exchange`
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
def compactTransportPowerSquare {U₀ V₀ : Over (Spec (.of D.k₀))}
    (h₀ : U₀ ⟶ V₀) (r : ℕ) :
    IsPullback (compactTransportPower D U₀ r) (fiberMap D h₀)
      (fiberMap D h₀) (compactTransportPower D V₀ r) := by
  induction r with
  | zero =>
    simpa only [compactTransportPower, pow_zero, End.one_def, End.of,
      Over.pullback_obj_left] using
      (IsPullback.of_id_fst :
        IsPullback (𝟙 _) (fiberMap D h₀) (fiberMap D h₀) (𝟙 _))
  | succ r ih =>
    change IsPullback (galois D U₀ ≫ End.of (galois D U₀) ^ r)
      (fiberMap D h₀) (fiberMap D h₀)
      (galois D V₀ ≫ End.of (galois D V₀) ^ r)
    simpa only [compactTransportPower, pow_succ, End.mul_def, End.of, galois,
      fiberMap, zlFiberMap] using
      ((D.frobenius_square_cartesian U₀ V₀ h₀).2.2.2.2.2.1).paste_horiz ih

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Frobenius inverse image on the ordinary unbounded derived category of strict systems.
Source: the system construction of `def-weil-frobenius-square-exchange`
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
abbrev compactTransportSystemPull (W₀ : Over (Spec (.of D.k₀)))
    [wft : LocallyOfFiniteType W₀.hom] [wqc : QuasiCompact W₀.hom] (r : ℕ) :
    coefficientSequenceDerived l E (@FiniteFieldDatum.geometricFiber D W₀ wft wqc).left ⥤
      coefficientSequenceDerived l E (@FiniteFieldDatum.geometricFiber D W₀ wft wqc).left :=
  integralComparisonDerivedSequencePullback l E (compactTransportPower D W₀ r)

/-- The inverse of the recorded canonical simultaneous inverse-image compositor.
The final equality merely rewrites the product of powers as the (m+1)-st power.
Source: Stacks 0D6D; `lem-weil-pbc-proetale-derived-pullback-composition`
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
def compactTransportSystemCompositor (W₀ : Over (Spec (.of D.k₀)))
    [wft : LocallyOfFiniteType W₀.hom] [wqc : QuasiCompact W₀.hom] (m : ℕ) :
    compactTransportSystemPull D l E W₀ m ⋙ compactTransportSystemPull D l E W₀ 1 ≅
      compactTransportSystemPull D l E W₀ (m + 1) :=
  (integralComparisonSystemComposition l E
    (compactTransportPower D W₀ 1) (compactTransportPower D W₀ m)).symm ≪≫
    eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
      (by simp only [compactTransportPower, pow_succ, pow_zero, End.mul_def,
        End.one_def, Category.comp_id]))

variable {X₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  (f₀ : X₀ ⟶ Y₀) (c₀ : Compactification f₀.left)

/-- Compact support using exactly the supplied k₀-descended compactification.
Source: `def-weil-frobenius-square-exchange`, item 2, integral system paragraph
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
abbrev compactTransportSystemFunctor :
    coefficientSequenceDerived l E (D.geometricFiber X₀).left ⥤
      coefficientSequenceDerived l E (D.geometricFiber Y₀).left :=
  systemDerivedOpen l E (geometricCompactification D f₀ c₀).i ⋙
    systemDirect l E (geometricCompactification D f₀ c₀).g

/-- The actual proper-adjunction mate followed by proper image of open exchange.
Both squares are obtained from the retained model, for the r-th geometric Frobenius power.
Source: `def-weil-frobenius-square-exchange`, item 2, integral system paragraph
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting). -/
def compactTransportSystemExchange (r : ℕ) :
    compactTransportSystemFunctor D l E f₀ c₀ ⋙ compactTransportSystemPull D l E Y₀ r ⟶
      compactTransportSystemPull D l E X₀ r ⋙ compactTransportSystemFunctor D l E f₀ c₀ :=
  systemCompactExchange l E (geometricCompactification D f₀ c₀)
    (compactTransportPower D X₀ r)
    (compactTransportPower D (zlCompactificationMiddle D f₀ c₀) r)
    (compactTransportPower D Y₀ r)
    (compactTransportPowerSquare D (zlCompactificationProper D f₀ c₀) r).w
    (compactTransportPowerSquare D (zlCompactificationOpen D f₀ c₀) r)

/-- Pasting of the specified compact-support exchanges on simultaneous derived systems.
Source: blueprint main-20261015, `prop-trf-rational-frobenius-integral-model.proof.md`,
clause (3), and `thm-trf-l-function-euler-product.proof.md`, Step 1, Global powers
(blueprint: lem-trf-integral-compact-transport-system-mate-pasting).

Proof, on whole systems and before evaluation:
1. Write F = S_p J_j. Expand each E_r as (S_p b_r)(e_{p,r} J_j), using the actual
   system adjunctions and constant coefficient pullbacks of semilinearDerivedSections.
2. The canonical inverse-image square comparisons satisfy the composition cocycle:
   their right-adjoint conjugates are the same strict pushforward identification.
   Uniqueness in unit_conjugateEquiv_symm gives equality. Exact localization gives
   integralComparisonSystemComposition, in the inverse direction used here.
3. Apply mateEquiv_vcomp to the proper squares for powers m and 1. Move the source
   and target compositors outside the mate with mateEquiv_whiskerTop_whiskerBottom.
   This gives e_{m+1}(t S) = (S u)(e_1 H_m)(G_1 e_m), without inverting e.
4. By openTensorNormalization the inverse open exchange is the left-adjunction mate
   of the inverse pullback square. Apply mateEquiv_vcomp to these inverse exchanges,
   then invert and insert the compositors: b_{m+1}(u J) = (J v)(b_1 K_m)(H_1 b_m).
5. Substitute the previous two identities into E_{m+1}(t F). Naturality of e_1 at
   b_{m,C} interchanges (S H_1 b_m)(e_1 H_m J) with (e_1 J K_m)(G_1 S b_m).
   Regrouping gives F(v)(E_1 K_m)(G_1 E_m), the right-hand side below.
6. These are natural transformations on unbounded derived system categories, so the
   equality is natural in every C and precedes evaluation, inverse limits and realization.
   For Y₀ = Spec k₀, levelwise sections on Spec k preserve it and give the tower equation.
   For general Y it remains over Y, with no identification with compact cohomology.
No boundedness, constructibility or finite Tor-amplitude hypothesis on C is used. -/
theorem integralCompactTransportSystemMatePasting
    (hl : l ≠ D.p) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] :
    ∀ (m : ℕ), 1 ≤ m →
      Functor.whiskerLeft (compactTransportSystemFunctor D l E f₀ c₀)
          (compactTransportSystemCompositor D l E Y₀ m).hom ≫
        compactTransportSystemExchange D l E f₀ c₀ (m + 1) =
      Functor.whiskerRight (compactTransportSystemExchange D l E f₀ c₀ m)
          (compactTransportSystemPull D l E Y₀ 1) ≫
        (Functor.associator (compactTransportSystemPull D l E X₀ m)
          (compactTransportSystemFunctor D l E f₀ c₀)
          (compactTransportSystemPull D l E Y₀ 1)).hom ≫
        Functor.whiskerLeft (compactTransportSystemPull D l E X₀ m)
          (compactTransportSystemExchange D l E f₀ c₀ 1) ≫
        (Functor.associator (compactTransportSystemPull D l E X₀ m)
          (compactTransportSystemPull D l E X₀ 1)
          (compactTransportSystemFunctor D l E f₀ c₀)).inv ≫
        Functor.whiskerRight (compactTransportSystemCompositor D l E X₀ m).hom
          (compactTransportSystemFunctor D l E f₀ c₀) := by
  sorry

end WeilConjectures.FrobeniusExchange
