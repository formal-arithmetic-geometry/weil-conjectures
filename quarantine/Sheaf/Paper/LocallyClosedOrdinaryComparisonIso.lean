/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module
public import Sheaf.Paper.InternalAdjunctionPairingChange
public import Sheaf.Paper.EtaleLocallyClosedShriek
/-! # Ordinary coefficient comparison through a locally closed immersion

Source: thm-coef-finite-hom, proof paragraph 4.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange
/-- The ordinary comparison through an open then closed immersion is invertible on the
finite-Tor bounded constructible internal Hom object.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-locally-closed-ordinary-comparison-iso).
Proof: apply the finite-coefficient direct-image comparison to the composite `j ≫ g`,
then cancel the canonical direct-image compositor using `finiteCoefficientDirectImageMap_comp`.
The geometric hypotheses are discharged by the Noetherian, separated and finite-type
assumptions on the immersion and by the finite-Tor constructibility of the object. -/
theorem locallyClosedOrdinaryComparison_isIso
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n) {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (Q : DerivedCategoryModule (coefficient l E n) S)
    (hQ : WeilConjectures.finiteTorConstructibleEtale l E n n.property S Q) :
    IsIso (ordinaryComparison (reduction l E n m hmn) g j Q) := by
  sorry
end AlgebraicGeometry.Etale
