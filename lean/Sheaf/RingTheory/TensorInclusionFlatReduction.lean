module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.AlgebraicGeometry.TorLongExactFirstVariable
import WeilConjectures.Algebra.Homology.FreeRestrictionTorBound
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor injectivity under flat reduction

Source: Stacks Project, Algebra, Tag 051C, first proof paragraph, and Tag 00M6
(blueprint: lem-sfb-tensor-inclusion-flat-reduction).

The submodule `J • (⊤ : Submodule R E)` is the module of finite sums of products
of elements of `J` with elements of `E`. Its quotient carries Mathlib's canonical
`R ⧸ J`-module structure. The ideal multiplication map and the inclusion-induced
tensor map are Mathlib's tensor lift and `LinearMap.rTensor`, respectively.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace Module.Flat

/-- Tensoring with `E` preserves a submodule inclusion whose quotient is killed by `J`,
provided that reduction of `E` modulo `J` is flat and ideal multiplication is injective.

Source: Stacks Project, Algebra, Tag 051C (lemma-what-does-it-mean), first proof
paragraph; Tag 00M6 (remark-Tor-ring-mod-ideal).
(blueprint: lem-sfb-tensor-inclusion-flat-reduction).

Proof:
1. Compute `Tor₁(R,E) = 0` using the resolution concentrated in degree zero. Apply
   lem-weil-pbc-tor-long-exact-first-variable to `0 → J → R → R/J → 0`.
   The boundary embeds `Tor₁(R/J,E)` in the kernel of `J ⊗ E → R ⊗ E`.
   The isomorphism `R ⊗ E ≃ E`, with inverse `e ↦ 1 ⊗ e`, identifies this map
   with multiplication. Its assumed injectivity gives `Tor₁(R/J,E) = 0`.
2. For an `R`-module `A` killed by `J`, give `A` its quotient-ring action and
   present it by the free `R/J`-module of finitely supported functions on `A`.
   Write `0 → K → F → A → 0` for this presentation. By
   lem-pc-free-restriction-tor-bound and step 1, `Tor₁(F,E) = 0`. The Tor sequence
   therefore embeds `Tor₁(A,E)` in the kernel of `K ⊗ E → F ⊗ E`.
3. By lem-weil-pbc-tensor-over-quotient-ring, this last tensor map identifies with
   `K ⊗[R/J] (E/JE) → F ⊗[R/J] (E/JE)`. The identification commutes with inclusion
   on pure tensors, hence on every tensor. By lem-weil-pbc-flat-tensor-exact and
   the flatness hypothesis, it is injective. Thus `Tor₁(A,E) = 0` for every `A`
   killed by `J`.
4. The hypothesis on scalar products implies `J(V/U) = 0`. Apply step 3 to
   `A = V/U`, and then the first-variable Tor sequence to `0 → U → V → V/U → 0`.
   The kernel of `U ⊗ E → V ⊗ E` is the image of the zero module `Tor₁(V/U,E)`,
   giving the claimed injectivity. No finiteness or nilpotence is used.
-/
theorem rTensor_subtype_injective_of_flat_reduction
    {R : Type u} [CommRing R] (J : Ideal R)
    {E : Type v} [AddCommGroup E] [Module R E]
    (hflat : Module.Flat (R ⧸ J) (E ⧸ J • (⊤ : Submodule R E)))
    (hmul : Function.Injective
      (TensorProduct.lift ((LinearMap.lsmul R E).comp J.subtype)))
    {V : Type w} [AddCommGroup V] [Module R V]
    (U : Submodule R V) (hJU : ∀ (j : R), j ∈ J → ∀ (x : V), j • x ∈ U) :
    Function.Injective (U.subtype.rTensor E) := by
  sorry

end Module.Flat
