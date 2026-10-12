module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- A finite free sequence of any prescribed length, with an unrestricted left kernel.
Source: Stacks Project, Algebra, Tag 00LP, part (2), the finite truncation of its
successive finite-free-surjection construction
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction).

Proof: Induct on `k`, for all finite modules `M`, including the zero module.
At `k = 0`, take `0 → ULift M → ULift M → 0`, with the identity middle map and
`ULift.moduleEquiv` identifying the penultimate object with `M`. For the successor
step choose finite generators of `M` and the associated surjection `F → M` from a
finite free module. Its kernel `N` is finite because it is a submodule of a finite
module over a Noetherian ring. Apply the induction hypothesis to `N`. Replace that
sequence's terminal `N → 0` by `N → F → M → 0`, using the kernel inclusion and the
chosen surjection. Exactness at `N` follows from injectivity of the kernel inclusion;
at `F` it follows from image(kernel inclusion) = kernel(surjection); at `M` it follows
from surjectivity. The preceding terms keep their exactness and finite freeness.
Lift all modules into universe `max u v` and conjugate the maps by the lift
isomorphisms. This preserves exactness and finite freeness and gives the asserted
module equivalence. No assertion about depth or Cohen--Macaulayness is involved. -/
theorem exists_finite_free_resolution_data
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (k + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (k + 3)) ∧
      Nonempty ((S.obj' (k + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin k,
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  sorry

end IsLocalRing
