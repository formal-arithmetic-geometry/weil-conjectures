import Sheaf.RingTheory.FittingIdealZero
import Sheaf.RingTheory.PresentationFittingIdeal
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Zeroth Fitting ideal of a direct sum

Source: Stacks Project, More on Algebra, Lemma Tag 07ZA(2)
(blueprint: lem-trf-fitting-ideal-direct-sum).
-/

universe u v w

namespace LinearMap

/-- For finitely generated modules, the zeroth Fitting ideal of their binary direct sum is the
product of their zeroth Fitting ideals.  Binary direct sums of modules are represented by the
product module `M × N`.  The proof chooses finite free surjections for both modules, forms their
block direct-sum presentation, expands its kernel-row determinants by the Leibniz formula, and
uses presentation independence.  Empty presentations are included by the empty determinant
convention. (blueprint: lem-trf-fitting-ideal-direct-sum) -/
theorem fittingIdealZero_prod {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R M] [Module.Finite R N] :
    fittingIdealZero (R := R) (M := M × N) =
      fittingIdealZero (R := R) (M := M) * fittingIdealZero (R := R) (M := N) := by
  sorry

end LinearMap
