/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotientCoefficients
public import WeilConjectures.SixFunctors.ScalarSixCompactSupport
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibilitySupplement
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement

/-!
# Integral compact supports and their prescribed condensed reductions

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-compact-support.md and its proof
(blueprint: lem-coef-integral-compact-support).

All categories below are ordinary uncompleted derived categories of internal modules.
The continuous integral ring, discrete finite quotients and actual quotient arrows are
those of `IntegralQuotient`. Level `n` denotes the positive exponent `n + 1`.
The canonical compact-support map is the proper scalar mate followed by the open scalar
comparison. The last equation states compatibility with every quotient transition using
the canonical derived scalar associator.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing continuous integral condensed ring, bundled for the scalar-six maps.
Source: current blueprint integral compact-support coefficient clause
(blueprint: lem-coef-integral-compact-support). -/
abbrev integralCompactSupportRing : ScalarSixRing.{u} :=
  ⟨IntegralQuotient.integral l E⟩

/-- The existing discrete quotient by pi^(n+1), bundled without changing its ring data.
Source: current blueprint integral compact-support coefficient clause
(blueprint: lem-coef-integral-compact-support). -/
abbrev integralCompactSupportLevel (n : ℕ) : ScalarSixRing.{u} :=
  ⟨IntegralQuotient.finite l E n⟩

/-- The actual continuous quotient map, as a morphism of bundled commutative rings.
Source: current blueprint canonical coefficient comparison
(blueprint: lem-coef-integral-compact-support). -/
def integralCompactSupportReduction (n : ℕ) :
    integralCompactSupportRing l E ⟶ integralCompactSupportLevel l E n :=
  CommMon.homMk (Mon.ofHom (IntegralQuotient.reduction l E n))

/-- The actual quotient transition at any two positive levels.
Source: current blueprint proof, final successive-reduction clause
(blueprint: lem-coef-integral-compact-support). -/
def integralCompactSupportTransition (m n : ℕ) (h : n ≤ m) :
    integralCompactSupportLevel l E m ⟶ integralCompactSupportLevel l E n :=
  CommMon.homMk (Mon.ofHom (IntegralQuotient.finiteMap l E m n h))

/-- Integral compact support is bounded constructible, has its prescribed canonical
positive reductions, and has common reduction Tor interval [a,b+2d]. The final equality
is the coefficient-composition square, including the scalar associators at X and Y.
The composite coefficient arrow in its left side is the direct reduction at level n,
by `IntegralQuotient.reduction_comp`.

Source: latest blueprint lem-coef-integral-compact-support and its proof
(blueprint: lem-coef-integral-compact-support).

Proof: compact support preserves Dctf by sk-thm-existence, and for integral coefficients
Dctf equals Dbc by lem-integral-ctf-equals-bc. Apply sk-prop-scalar-six to the continuous
quotient R to A_n to obtain the specified proper/open comparison isomorphism. At each
finite level extension by zero preserves the common Tor interval. Refine the fixed
compactification by the closure of X, whose dimension is at most d, and apply the proper
direct-image Tor bound and the 2d cohomological-dimension bound. Transport the result
back to the fixed compactification and use the comparison to obtain [a,b+2d] for the
reduced integral output. Finally scalar-six coefficient composition for R to A_m to A_n
is precisely the displayed square; the actual quotient maps satisfy reduction_comp,
so it is the compatibility with the direct reduction R to A_n, including m = n.
-/
theorem boundedConstructibleIntegral_compactSupport
    (D : WeilConjectures.FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of D.k)) (aY : Y ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [IsSeparated aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (IntegralQuotient.integral l E) X)))
    (_hK : (constantModelBoundedConstructible (IntegralQuotient.integral l E) X ⊓
      DerivedCategory.finiteTorAmplitude _) K)
    (d : ℕ) (_hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    (_hred : ∀ n : ℕ, DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (IntegralQuotient.finite l E n) X)) a b
      ((scalarSixChange (integralCompactSupportReduction l E n) X).obj K)) :
    constantModelBoundedConstructible (IntegralQuotient.integral l E) Y
      ((rightDerivedLowerShriekOfCompactification (IntegralQuotient.integral l E) c).obj K) ∧
    (∀ n : ℕ, IsIso
      ((scalarCompactSupportMap (integralCompactSupportReduction l E n) c.i c.g).app K)) ∧
    (∀ n : ℕ, DerivedCategory.torAmplitudeIn
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj (IntegralQuotient.finite l E n) Y)) a (b + 2 * (d : ℤ))
      ((scalarSixChange (integralCompactSupportReduction l E n) Y).obj
        ((rightDerivedLowerShriekOfCompactification
          (IntegralQuotient.integral l E) c).obj K))) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      (scalarSixTower (integralCompactSupportReduction l E m)
        (integralCompactSupportTransition l E m n h) Y).hom.app
          ((rightDerivedLowerShriekOfCompactification
            (IntegralQuotient.integral l E) c).obj K) ≫
          (scalarCompactSupportMap (integralCompactSupportReduction l E m ≫
            integralCompactSupportTransition l E m n h) c.i c.g).app K =
        (scalarSixChange (integralCompactSupportTransition l E m n h) Y).map
            ((scalarCompactSupportMap (integralCompactSupportReduction l E m) c.i c.g).app K) ≫
          (scalarCompactSupportMap (integralCompactSupportTransition l E m n h) c.i c.g).app
            ((scalarSixChange (integralCompactSupportReduction l E m) X).obj K) ≫
          (rightDerivedLowerShriekOfCompactification
            (IntegralQuotient.finite l E n) c).map
              ((scalarSixTower (integralCompactSupportReduction l E m)
                (integralCompactSupportTransition l E m n h) X).hom.app K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
