module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicity
public import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import Sheaf.AlgebraicGeometry.EtaleSheaves
import Sheaf.CategoryTheory.ExactCoupleConvergence
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

@[expose] public section

universe u_comp

open CategoryTheory
namespace AlgebraicGeometry.Etale

/-! # Composition stability of proper base change

Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-reduction/prop-weil-pbc-composition-stability.md,
node prop-weil-pbc-composition-stability, order 1195
(blueprint: prop-weil-pbc-composition-stability).
-/

/-- Composition stability of proper base change. The proper composite has injective
acyclicity for every prime and therefore proper base change.
Source: literature/blueprint/master/blueprint/sec-proper-base-change/
sk-thm-reduction/prop-weil-pbc-composition-stability.md,
node prop-weil-pbc-composition-stability, order 1195
(blueprint: prop-weil-pbc-composition-stability).

Proof: properness of the composite uses the proper-composition lemma. The injective
acyclicity assertion follows by the cartesian-square pasting argument, injectivity
preservation by direct image, the two acyclicity hypotheses, underived exchange, and
the Grothendieck spectral sequence. Finally the equivalence between proper base
change and injective acyclicity gives the last conjunct.
-/
theorem prop_weil_pbc_composition_stability
    {X Y Z : Scheme.{u_comp}} (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsProper f] [IsProper h]
    (hf : HasAllPrimeInjectiveAcyclicity f)
    (hh : HasAllPrimeInjectiveAcyclicity h) :
    IsProper (f ≫ h) ∧
      HasAllPrimeInjectiveAcyclicity (f ≫ h) ∧
      HasTorsionAbelianBaseChange (f ≫ h) := by
  sorry

end AlgebraicGeometry.Etale
