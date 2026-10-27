module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Simultaneous bases in finitely many residue-field targets

Source: Stacks Project, `algebra.tex`, Tag 03C1,
`algebra-lemma-semi-local-module-basis-in-submodule`, proof, with its infinite-field
avoidance argument isolated for finitely many linear targets
(blueprint: lem-a1-simultaneous-residue-bases).
-/

@[expose] public section

set_option autoImplicit false

universe u v w x z

namespace IsLocalRing

/-- A tuple in a module can give bases simultaneously in finitely many spanning
residue-field targets. Source: Stacks Project, Tag 03C1, proof of
`algebra-lemma-semi-local-module-basis-in-submodule`, infinite-field linear avoidance
and induction (blueprint: lem-a1-simultaneous-residue-bases).

Proof: If the target index set is empty, take all tuple entries to be zero.
Otherwise inductively choose `t` vectors, for `0 ≤ t ≤ r`, independent in every target.
For `t < r`, their spans `W i` are proper by the dimension assumption. Since each image
spans its target, choose `q i` whose image is outside `W i`.
On the finite-dimensional coefficient space `(ResidueField D)^I`, take the linear map
sending `c` to the sum of `ι i (c j) • ρ i (q j)`. The inverse image of `W i` is a proper
subspace, since the `i`-th coordinate vector maps outside `W i`. Apply finite linear
avoidance (lem-pc-finite-linear-avoidance, `Subspace.biUnion_ne_univ_of_top_notMem`)
to choose coefficients outside all these inverse images. Lift the coefficients along
`residue D` and take the resulting `D`-linear combination of the `q j` in `Q`.
Semilinearity places its image outside every `W i`; in any linear relation its coefficient
must vanish, and independence of the previous vectors kills all remaining coefficients.
At `t = r`, the images also span: otherwise adjoining a vector outside the span gives
`r + 1` independent vectors, contradicting the dimension bound
(lem-weil-independent-family-card-le-dimension, `LinearIndependent.fintype_card_le_finrank`).
They therefore form bases, with dimension interpreted by `Module.finrank`
(def-weil-vector-space-dimension). This also handles `r = 0`: a vector outside the zero
span would give an independent singleton in dimension zero. -/
theorem exists_simultaneous_residue_bases
    (D : Type u) [CommRing D] [IsLocalRing D] [Infinite (ResidueField D)]
    (Q : Type v) [AddCommGroup Q] [Module D Q]
    (I : Type w) [Finite I] (r : ℕ)
    (K : I → Type x) [∀ i, Field (K i)]
    (ι : ∀ i, ResidueField D →+* K i)
    (F : I → Type z) [∀ i, AddCommGroup (F i)] [∀ i, Module (K i) (F i)]
    [∀ i, Module.Finite (K i) (F i)]
    (hdim : ∀ i, Module.finrank (K i) (F i) = r)
    (ρ : ∀ i, Q →ₛₗ[(ι i).comp (residue D)] F i)
    (hspan : ∀ i, Submodule.span (K i) (Set.range (ρ i)) = ⊤) :
    ∃ y : Fin r → Q, ∀ i, ∃ b : Module.Basis (Fin r) (K i) (F i),
      ∀ j, b j = ρ i (y j) := by
  sorry

end IsLocalRing
