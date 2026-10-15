/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
import Sheaf.AlgebraicGeometry.ProperBoundedConstructible
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Bounded constructibility and base change for compact direct images

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-compact-bounded-and-base-change.md`, statement and proof
(blueprint: lem-fin-compact-bounded-and-base-change).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Compact direct image preserves bounded constructibility over a field of characteristic
other than `ℓ`, and its specified exchange is invertible after every Noetherian base change.
Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/`
`lem-fin-compact-bounded-and-base-change.md`
(blueprint: lem-fin-compact-bounded-and-base-change).

The coefficient ring is the universe lift of the prime field `ZMod ℓ`. A bounded constructible
complex is viewed in `D⁺`, with the constructibility and two-sided bound imposed on its underlying
object in `D`. The compactification `c` computes the candidate `Rp_* j_!`; its base change computes
the target of the exchange, exactly as in `def-cbc-exchange-map`.

Proof: (1) Finite-type schemes over a field are Noetherian by
`lem-weil-pbc-finite-type-over-noetherian`. Nagata (`thm-nagata-compactification`) supplies a
compactification, and its ambient scheme is Noetherian and finite type over the same field by
`lem-weil-pbc-proper-fp-permanence`. The definition `def-amb-etale-compact-support` identifies the
candidate with `Rp_* j_!`.
(2) Extension by zero is exact (`sbc-prop-extension-by-zero-and-arbitrary-base-change`). The
cohomology comparison `lem-weil-pbc-exact-functor-complex-cohomology` and
`lem-fin-extension-by-zero` show that `j_!K` is bounded constructible, with the same interval.
(3) The finite ring F_ℓ is killed by ℓ, which is invertible on the schemes in question. Apply
`lem-fin-proper-bounded-constructible` to the proper compactification map to obtain the first
conclusion.
(4) Base change of the compactification is a compactification
(`lemma-nagata-compactification-base-change`, `def-nagata-compactification-base-change`). Its
ambient scheme is Noetherian over the given Noetherian base; its open source is Noetherian too.
Extension-by-zero base change identifies the inverse image of `j_!K` with `j'_!v_X^*K`.
(5) Bounded-below proper base change (`thm-weil-pbc-bounded-below`) applies to `j_!K` with torsion
cohomology. The comparison `lem-weil-pbc-exchange-forget-coefficients` identifies the specified
module-coefficient exchange and reflects its invertibility.
(6) Exact inverse image is module pullback (`prop-weil-pbc-inverse-image-modules-exact`). The map
of `def-cbc-exchange-map` is the proper exchange followed by the image of the extension-by-zero
isomorphism. Both factors are invertible, so their composite is invertible. No finite-type
hypothesis over the original field is used for the new base. -/
theorem isBoundedConstructible_compactSupport_and_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (hℓ : (ℓ : k) ≠ 0)
    {X S : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aS : S ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hf : f ≫ aS = aX) (c : Compactification f)
    (K : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))))
    (hK : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X K.obj) :
    DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) S
      ((rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) c).obj K.obj) ∧
    ∀ (S' : Scheme.{u}) [IsNoetherian S'] (v : S' ⟶ S)
      (X' : Scheme.{u}) (vX : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback vX f' f v),
      IsIso ((rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap
        (ULift.{u + 1} (ZMod ℓ)) sq c).app K) := by
  sorry

end AlgebraicGeometry.Etale
