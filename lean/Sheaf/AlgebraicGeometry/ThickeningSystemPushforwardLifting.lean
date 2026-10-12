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
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
import Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardIdealPowers
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Lifting an adic system to the closed thickenings

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting).
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

/-- Every adic system has a preimage under the explicit pushforward system functor.
This only asserts object lifting, without constructing an equivalence or evaluation
comparisons and without asserting full faithfulness.

Source: Stacks, Remark 088F, Lemma 087T, equation 0880
(blueprint: lem-weil-pbc-thickening-system-pushforward-lifting).
Proof: The sources of the closed immersions `j n` are Noetherian. For each term of `H`,
the annihilation condition and `(j n).ker = J^(n+1)` place it in the essential image
of the closed-immersion coherent equivalence. Choose coherent terms `M_n` and
isomorphisms `j_(n,*) M_n ≅ H_n`. Transport each adjacent transition of `H` across these
isomorphisms. Use pushforward composition and `hi` to regard its target as
`j_(n+1,*) i_(n,*) M_n`. Full faithfulness of `j_(n+1,*)` uniquely lifts this morphism
and the supplied adjunction takes it to a map `i_n^* M_(n+1) → M_n`.
The kernel of `i n` is `(J^(n+1)).comap (j (n+1))`. The unit-quotient theorem and the
closed pushforward ideal-power comparison identify the pushforward of the adjoint map
with the induced quotient transition of `H`, conjugated by the chosen term isomorphisms.
The adic quotient condition makes this pushforward invertible. Full faithfulness of
closed pushforward reflects isomorphisms, so these maps are the comparison isomorphisms
of a coherent thickening system `M`. The term isomorphisms commute with the adjacent
transitions by construction. `NatTrans.ofOpSequence` extends their homs and inverses
to natural transformations; their two inverse identities hold componentwise. They
therefore assemble to the displayed isomorphism of inverse systems. -/
theorem thickeningSystemPushforward_lifting
    {X : Scheme.{v}} [IsNoetherian X] {T : ℕ → Scheme.{v}}
    {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
    (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))
    (J : X.IdealSheafData)
    (hgeom : ∀ n, IsClosedImmersion (j n) ∧ (j n).ker = J ^ (n + 1))
    (H : CoherentFormalModule X J) :
    ∃ M : CoherentThickeningSystem T i,
      Nonempty ((thickeningSystemPushforward j hi ai).obj M ≅ H.obj) := by sorry

end
end AlgebraicGeometry
