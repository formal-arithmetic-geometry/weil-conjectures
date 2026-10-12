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

/-- Naturality of a family of Tor kernel boundary maps.

Source: Stacks Project, Algebra, Section 00LY, Tags 00M0 and 00LZ.
Proof: lift every compatible square of kernel short exact sequences to a morphism
of the chosen degreewise split free resolutions. Naturality of the homology
connecting morphism gives commutation after tensoring with `M`; the standard
resolution comparison identifies the degree-one map with `Tor'` and the degree-zero
map with the tensor of the kernel map, yielding the displayed equality.
(blueprint: lem-sc-p1-tor-kernel-boundary-naturality-of) -/
theorem tor_kernel_boundary_naturality_of
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R)
    (δ : ∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N),
      Function.Surjective q →
        (((Tor' (ModuleCat.{u} R) 1).obj N).obj M) →ₗ[R]
          (LinearMap.ker q ⊗[R] M)) :
    (∀ (F N : ModuleCat.{u} R) (q : F →ₗ[R] N) (hq : Function.Surjective q),
      Function.Exact (((Tor' (ModuleCat.{u} R) 1).map
        (ModuleCat.ofHom q)).app M).hom (δ F N q hq) ∧
      Function.Exact (δ F N q hq) ((LinearMap.ker q).subtype.rTensor M)) →
    ∀ (F N F' N' : ModuleCat.{u} R) (q : F →ₗ[R] N) (q' : F' →ₗ[R] N')
        (hq : Function.Surjective q) (hq' : Function.Surjective q')
        (a : F →ₗ[R] F') (b : N →ₗ[R] N')
        (c : LinearMap.ker q →ₗ[R] LinearMap.ker q'),
      q'.comp a = b.comp q →
      (∀ x : LinearMap.ker q, (c x : F') = a (x : F)) →
      ∀ t : (((Tor' (ModuleCat.{u} R) 1).obj N).obj M),
        δ F' N' q' hq' ((((Tor' (ModuleCat.{u} R) 1).map
          (ModuleCat.ofHom b)).app M).hom t) =
        c.rTensor M (δ F N q hq t) := by
  sorry


end CategoryTheory
