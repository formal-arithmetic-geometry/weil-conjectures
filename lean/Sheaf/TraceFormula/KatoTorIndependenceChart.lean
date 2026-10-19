/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.StrictHenselization
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.MonoidAlgebra.Basic
import Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison
import Sheaf.AlgebraicGeometry.LogRegularCompletedChart
import Sheaf.AlgebraicGeometry.LogRegularSharpChart
import Sheaf.RingTheory.StrictHenselizationCompletionNoetherian
import WeilConjectures.RingTheory.StrictHenselizationTriples
import Sheaf.RingTheory.TorFlatBaseChange
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CohenRing

/-!
# Tor independence of monoid-ideal quotients in a log regular chart

Source: ILO, Exposé VIII, Lemma 3.4.3 proof, invoking Kato (1994), 6.1(ii)
(blueprint: lem-trf-kato-tor-independence-chart).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- For a locally Noetherian fs log regular scheme, every monoid ideal in a chart at
an algebraically closed geometric point is Tor-independent from the chart ring.
The proof follows ILO, Exposé VIII, Lemma 3.4.3, using the completed chart models
of Exposé VI 1.6 and Kato (1994), 6.1(ii), together with faithfully flat descent.
(blueprint: lem-trf-kato-tor-independence-chart). -/
theorem torOne_monoidIdeal_independence
    {X : FineSaturatedLogScheme.{u}} (hlog : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ X.scheme)
    {W : X.scheme.Etale} (w : (Scheme.pointSmallEtale t).fiber.obj W)
    {P : Type u} [CommMonoid P] (hP : IsFineSaturatedMonoid P)
    (c : P →* X.logStructure.monoidSheaf.obj.obj (op W))
    (hc : X.logStructure.IsChart W c)
    (e : P ≃* (X.logStructure.characteristic t))
    (he : ∀ p : P,
      e p = Associates.mk
        (X.logStructure.toEtalePrelogStructure.germ t W w (c p)))
    (a : P →* strictLocalRing X.scheme t)
    (ha : ∀ p : P,
      a p = X.logStructure.toEtalePrelogStructure.stalkAlpha t
        (X.logStructure.toEtalePrelogStructure.germ t W w (c p)))
    (I : Set P) (hI : ∀ q ∈ I, ∀ p : P, q * p ∈ I) :
    IsZero (((Tor' (ModuleCat.{u} (MonoidAlgebra ℤ P)) 1).obj
      (ModuleCat.of (MonoidAlgebra ℤ P)
        (MonoidAlgebra ℤ P ⧸ Ideal.span
          {x : MonoidAlgebra ℤ P | ∃ q ∈ I, x = MonoidAlgebra.single q 1}))).obj
      (@ModuleCat.of (MonoidAlgebra ℤ P) _ (strictLocalRing X.scheme t) inferInstance
        (Module.compHom (strictLocalRing X.scheme t)
          (MonoidAlgebra.lift ℤ (strictLocalRing X.scheme t) P a).toRingHom))) := by
  sorry

end AlgebraicGeometry
