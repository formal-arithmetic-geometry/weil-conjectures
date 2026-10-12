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
  sorry

end CategoryTheory
