/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.ThickeningSystemPushforward
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Adic conditions for the explicit pushforward system

Source: Stacks Project, Cohomology of Schemes, Remark 088F, Lemma 087T, equation 0880.
(blueprint: lem-weil-pbc-thickening-system-pushforward-adic).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

/-- The explicit pushed system satisfies coherence, annihilation, and the quotient
transition condition. This is an object assertion, without full faithfulness or lifting.

Source: Stacks, Remark 088F, Lemma 087T, equation 0880
(blueprint: lem-weil-pbc-thickening-system-pushforward-adic).
Proof: Each `j n` is a closed immersion into a Noetherian scheme, so its source is
Noetherian. Closed-immersion coherent equivalence makes the pushed term coherent and
annihilated by its kernel `J^(n+1)`. Convert the ideal-sheaf power to the multiplication
image power used in `IsCoherentFormalModule`. Since `i n ≫ j (n+1) = j n` and both
projections are closed immersions, `i n` is a closed immersion with kernel
`(J^(n+1)).comap (j (n+1))`. The closed-immersion unit-quotient theorem, transported to
the supplied adjunction `ai n` by uniqueness of left adjoints, identifies the adjoint
of `M.comparison n` with the quotient projection followed by an isomorphism.
Push this identity along `j (n+1)`. Closed pushforward of ideal powers identifies its
source quotient with the quotient of the pushed term by `J^(n+1)`. Compose the quotient
comparison with the pushforward of `M.comparison n`, the pushforward-composition
comparison, and the comparison induced by `hi n`. This gives the required quotient
isomorphism. Its composite with the quotient projection is the explicit adjacent
transition. `Functor.ofOpSequence_map_homOfLE_succ` identifies this with the inverse
system's adjacent map. These are precisely the three defining conjuncts. -/
theorem thickeningSystemPushforward_isAdic
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (M : CoherentThickeningSystem T i) :
    IsCoherentFormalModule J ((thickeningSystemPushforward j hi ai).obj M) := by sorry

end
end AlgebraicGeometry
