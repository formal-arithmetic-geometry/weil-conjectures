/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory

/-!
# The data and conditions of the local resolution invariant calculus

Source: ILO, Expose VIII, 2.3.11 and 2.3.13, pp. 93--94; BMT, Q-universal
desingularization, Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: def-trf-resolution-invariant-calculus-data).

This interface spells out the four clauses; it does not assert their existence.
The value order has a least element but is not assumed well founded.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open EmbeddedResolutionHistory

/-- A reduced ideal of one invariant stratum. In the empty case the ideal is the unit
ideal; that equality is required explicitly by the smooth comparison clause below.
Source: ILO VIII 2.3.11--2.3.13
(blueprint: def-trf-resolution-invariant-calculus-data). -/
def IsResolutionStratumIdeal {V : Type w} (ν : ValueFamily.{u} V)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n)
    (m : V) (J : H.X.IdealSheafData) : Prop :=
  IsReduced J.subscheme ∧ ∀ x : H.X, x ∈ J.support ↔ ν H x = m

/-- A simultaneous normalized invariant and its four clauses: finite image with regular
bottom; regular coherent maximum centers and strict local progress; smooth and intrinsic
comparison of finite histories and reduced ideals; and termination of this particular
maximum-center process. The same assignment is used for every embedded pair, including
disconnected pairs with components of differing dimensions. No global bound on dimension,
constant relative dimension, or well-foundedness of the value order is assumed.
Source: ILO VIII 2.3.11, 2.3.13; BMT Theorem 6.1 and Addendum, sections 6.1--6.3
(blueprint: def-trf-resolution-invariant-calculus-data). -/
structure ResolutionInvariantCalculus (V : Type w) [LinearOrder V] [OrderBot V] where
  value : ValueFamily.{u} V
  finiteImage : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n), Admissible value H → (Set.range (value H)).Finite
  regularPoint : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n), Admissible value H →
      ∀ x : H.X, value H x = ⊥ ↔ IsRegularLocalRing (H.X.presheaf.stalk x)
  maximumExists : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n), Admissible value H → ¬ IsRegularScheme H.X →
      ∃ (K : EmbeddedResolutionHistory A (n + 1)) (E : Extension H K), IsMaximumStep value E
  maximumGeometry : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K), Admissible value H → IsMaximumStep value E →
      Nonempty (K.center (Fin.last n)).subscheme ∧
      IsRegularScheme (K.center (Fin.last n)).subscheme ∧
      interior (Set.range E.centerMap) = ∅ ∧
      (K.center (Fin.last n)).toModules.IsFiniteTypeWithFiniteTypeKernels ∧
      E.centerMap.ker.toModules.IsFiniteTypeWithFiniteTypeKernels
  nextGeometry : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K), Admissible value H → IsMaximumStep value E →
      Smooth K.base ∧ IsSeparated K.base ∧ LocallyOfFiniteType K.base ∧
      QuasiCompact K.base ∧ IsReduced K.X
  strictProgress : ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K), Admissible value H → IsMaximumStep value E →
      ∀ m m' : V, IsGreatest (Set.range (value H)) m →
        IsGreatest (Set.range (value K)) m' → ⊥ < m' → m' < m
  pullbackExists : ∀ {A B : EmbeddedResolutionPair.{u}} {n : ℕ}
    (f : EmbeddedResolutionSmoothMap A B) (K : EmbeddedResolutionHistory B n),
      Admissible value K → ∃ (m : ℕ) (H : EmbeddedResolutionHistory A m),
        Nonempty (SmoothPullback f H K)
  smoothValues : ∀ {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {f : EmbeddedResolutionSmoothMap A B} {H : EmbeddedResolutionHistory A m}
    {K : EmbeddedResolutionHistory B n} (c : SmoothPullback f H K),
      Admissible value K → ∀ x : H.X, value H x = value K (c.finalMap x)
  smoothIdeals : ∀ {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {f : EmbeddedResolutionSmoothMap A B} {H : EmbeddedResolutionHistory A m}
    {K : EmbeddedResolutionHistory B n} (c : SmoothPullback f H K),
      Admissible value K → ∀ (a : V) (J : K.X.IdealSheafData),
        IsGreatest (Set.range (value K)) a → IsResolutionStratumIdeal value K a J →
          IsResolutionStratumIdeal value H a (J.comap c.finalMap) ∧
            ((∀ x : H.X, value H x ≠ a) → J.comap c.finalMap = ⊤)
  intrinsicValues : ∀ {A B : EmbeddedResolutionPair.{u}} {n : ℕ}
    {e : A.X ≅ B.X} {H : EmbeddedResolutionHistory A n}
    {K : EmbeddedResolutionHistory B n} (c : IntrinsicComparison e H K),
      Admissible value H → Admissible value K → ∀ x : H.X,
        value H x = value K ((c.iso.app (op (Fin.last n))).hom x)
  intrinsicIdeals : ∀ {A B : EmbeddedResolutionPair.{u}} {n : ℕ}
    {e : A.X ≅ B.X} {H : EmbeddedResolutionHistory A n}
    {K : EmbeddedResolutionHistory B n} (c : IntrinsicComparison e H K),
      Admissible value H → Admissible value K →
        ∀ (a : V) (I : H.X.IdealSheafData) (J : K.X.IdealSheafData),
          IsGreatest (Set.range (value K)) a →
            IsResolutionStratumIdeal value H a I → IsResolutionStratumIdeal value K a J →
              I = J.comap (c.iso.app (op (Fin.last n))).hom
  termination : ∀ A : EmbeddedResolutionPair.{u},
    ¬ ∃ (H : ∀ n : ℕ, EmbeddedResolutionHistory A n)
      (E : ∀ n : ℕ, Extension (H n) (H (n + 1))),
        ∀ n : ℕ, IsMaximumStep value (E n)

end AlgebraicGeometry
