module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ExactSequence

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits

namespace IsLocalRing

/-- The zero-step truncation in the finite-free resolution construction.
Source: Stacks Project, Algebra, Tag 00LP, part (2).
The identity complex with zero endpoints supplies the base case.
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction-zero) -/
theorem exists_finite_free_resolution_data_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (0 + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (0 + 3)) ∧
      Nonempty ((S.obj' (0 + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin 0,
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  let U := ModuleCat.of R (ULift.{max u v} M)
  let Z := ModuleCat.of R PUnit
  let z : Z ⟶ U := 0
  let e : U ⟶ U := 𝟙 _
  let S := ComposableArrows.mk₃ z e (0 : U ⟶ Z)
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · change (ComposableArrows.mk₃ (0 : Z ⟶ U) (𝟙 U) (0 : U ⟶ Z)).Exact
    apply ComposableArrows.exact_of_δ₀
    · apply ComposableArrows.exact₂_mk _ (by simp [ComposableArrows.Precomp.map])
      apply (CategoryTheory.ShortComplex.exact_iff_mono _ (by simp)).2
      change Mono (𝟙 U)
      infer_instance
    · apply ComposableArrows.exact₂_mk _ (by simp [ComposableArrows.Precomp.map])
      apply (CategoryTheory.ShortComplex.exact_iff_epi _ (by simp [ComposableArrows.Precomp.map])).2
      change Epi (𝟙 U)
      infer_instance
  · change IsZero Z
    exact ModuleCat.isZero_of_subsingleton _
  · change IsZero Z
    exact ModuleCat.isZero_of_subsingleton _
  · exact ⟨ULift.moduleEquiv⟩
  · intro i
    exact i.elim0

/-- The successor step, adjoining one finite-free presentation to a truncation.
Source: Stacks Project, Algebra, Tag 00LP, part (2).
The kernel of a finite free surjection is finite over a Noetherian ring and the
induction truncation is spliced to that presentation.
(blueprint: lem-weil-pbc-cm-local-free-resolution-construction-succ) -/
theorem exists_finite_free_resolution_data_succ
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (k : ℕ) :
    ∃ S : ComposableArrows (ModuleCat.{max u v} R) (k + 1 + 3),
      S.Exact ∧ IsZero (S.obj' 0) ∧ IsZero (S.obj' (k + 1 + 3)) ∧
      Nonempty ((S.obj' (k + 1 + 2)) ≃ₗ[R] M) ∧
      (∀ i : Fin (k + 1),
        Module.Free R (S.obj' (i.val + 2) (by omega)) ∧
        Module.Finite R (S.obj' (i.val + 2) (by omega))) := by
  sorry

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
  induction k with
  | zero => simpa using exists_finite_free_resolution_data_zero M
  | succ k =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        exists_finite_free_resolution_data_succ M k

end IsLocalRing
