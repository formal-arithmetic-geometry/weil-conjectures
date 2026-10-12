module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
import Sheaf.Paper.TorLongExactFirstVariable

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace CategoryTheory

set_option maxHeartbeats 200000 in
-- The Tor exact-sequence elaboration needs a larger reduction budget.
/-- The exactness component of the Tor kernel boundary construction.

Source: Stacks Project, Algebra, Section 00LY, Tags 00M0 and 00LZ.
Proof: for each surjection, resolve the kernel inclusion and quotient map by a
degreewise split short exact sequence of free resolutions. Tensor with `M` and take
the connecting morphism in homology. The identifications of first homology with
`Tor'` and of zeroth homology with the tensor product transport the two adjacent
exact pairs in the homology long exact sequence to the displayed assertions.
(blueprint: lem-sc-p1-tor-kernel-boundary-exact) -/
theorem exists_tor_kernel_boundary_exact
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) :
    ∃ δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
        Function.Surjective q →
          (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
            (LinearMap.ker q ⊗[R] M),
      ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q),
        Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom q)).app M).hom (δ F N q hq) ∧
        Function.Exact (δ F N q hq) ((LinearMap.ker q).subtype.rTensor M) := by
  classical
  let E : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
      Function.Surjective q →
        ∀ (X : Type u) [AddCommGroup X] [Module R X],
          (((Tor' (ModuleCat.{u} R) 1).obj N).obj (ModuleCat.of R X)) ⟶
            ModuleCat.of R (LinearMap.ker q ⊗[R] X) := fun F N q hq =>
    (tor_long_exact_first_variable (LinearMap.ker q).subtype q
      (Submodule.subtype_injective _) hq
      ((LinearMap.exact_iff).2 (by rw [Submodule.range_subtype]))).choose
  let δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
      Function.Surjective q →
        (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
          (LinearMap.ker q ⊗[R] M) := fun F N q hq =>
    (E F N q hq (M : Type u)).hom
  refine ⟨δ, ?_⟩
  intro F N q hq
  cases M
  rename_i carrier inst₁ inst₂
  have hs := (tor_long_exact_first_variable (LinearMap.ker q).subtype q
    (Submodule.subtype_injective _) hq
    ((LinearMap.exact_iff).2 (by rw [Submodule.range_subtype]))).choose_spec
  have h := hs.1 carrier
  exact ⟨by simpa [δ, E] using h.1, by simpa [δ, E] using h.2.1⟩

end CategoryTheory
