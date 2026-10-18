/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import Sheaf.Paper.EtaleHomFiniteTorAmplitude

/-! # Internal Hom with finite Tor amplitude and an integer dimension bound

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
`sk-thm-sf-hom-ctf/_section.md`, order 1713 (blueprint: sk-thm-sf-hom-ctf).

The dimension takes values in `WithBot ℕ∞`. For a negative integer bound, comparison
means dimension at most bottom; for a nonnegative bound, it is the usual comparison
with its natural-number value. This retains the empty scheme for every integer bound.
Site-perfectness is the existing local finite-projective-model predicate. Together
with the assumed Tor interval, its local models can be chosen in that same interval.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Derived internal Hom of finite-Tor bounded constructible etale complexes has Tor
amplitude in `[c-b-2m,d-a+2m]`, and in `[c-b,d-a]` for a site-perfect first argument.
Source: Weil blueprint, main-20261015, `sk-thm-sf-hom-ctf/_section.md`, order 1713
(blueprint: sk-thm-sf-hom-ctf).

Proof (the node's single step, including its empty-scheme case):
1. If `m < 0`, the dimension hypothesis says that the dimension is bottom. By
   def-kun-topological-krull-dimension this means that X is empty. The empty object
   on its small etale site has an empty covering family, so the sheaf axiom forces
   every module sheaf to be zero. Consequently K, M and their derived internal Hom
   are zero. The zero complex is bounded constructible and has Tor amplitude in
   every interval, including a reversed interval. Both conclusions follow.
2. If `0 ≤ m`, apply thm-sf-hom-ctf, namely
   `finiteCoefficient_derivedHom_ctf_etale`, with dimension bound `m.toNat` and the
   same global finite-field datum, coefficient extension, level, scheme, complexes
   and Tor intervals. Since `(m.toNat : ℤ) = m`, its general clause gives precisely
   the constructibility and interval asserted here.
3. The site-perfect clause of that theorem gives the sharper interval. The source's
   local finite-projective models in `[a,b]` imply its IsSitePerfect hypothesis by
   forgetting bounds. Conversely, in the presence of the given Tor amplitude,
   lem-sf-site-perfect-tor-window chooses models within `[a,b]`, so this predicate
   renders the source's stated site-perfect condition without an extra assumption. -/
theorem finiteCoefficient_derivedHom_ctf_etale_intDimension
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (m : ℤ)
    (_hm : topologicalKrullDim X ≤
      if m < 0 then ⊥ else (m.toNat : WithBot ℕ∞))
    (a b c d : ℤ) (_hab : a ≤ b) (_hcd : c ≤ d)
    (K M : Etale.DerivedCategoryModule
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X)
    (_hK : finiteTorConstructibleEtale l E n hn X K)
    (_hM : finiteTorConstructibleEtale l E n hn X M)
    (_hKt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X a b K)
    (_hMt : Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X c d M) :
    finiteTorConstructibleEtale l E n hn X
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    Etale.DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X
      (c - b - 2 * m) (d - a + 2 * m)
      (((Etale.derivedHom (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) X (c - b) (d - a)
        (((Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X).obj (op K)).obj M)) := by
  sorry

end WeilConjectures
