/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.RingTheory.EtaleAlgebraLift
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.CotangentBaseChange

/-!
# Étaleness of maps between square-zero extensions

Source: Stacks Project, Tag 05YT, `lemma-lift-etale-infinitesimal`
(blueprint: lem-sfb-square-zero-etale-extension-criterion).

The two algebra structures encode the upper map and the composite to the lower
right ring. The algebra map `q` and the equation `hcomm` express the commutative
square. The kernel comparison is specified on pure tensors using every lift in
`Bplus`, so the isomorphism in the hypothesis is the canonical comparison.

The tensor product is written over `Aplus`. Since `p` is surjective and its
square-zero kernel annihilates itself, this is canonically the tensor product
of its quotient `A`-module with `B` over `A`. No choice of quotient action or
of lifts is part of the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

open scoped TensorProduct

namespace RingHom

/-- A map of square-zero extensions is étale when its reduction is étale and
its canonical kernel comparison is an isomorphism.

Source: Stacks Project, Tag 05YT, `lemma-lift-etale-infinitesimal`
(blueprint: lem-sfb-square-zero-etale-extension-criterion).

Proof (the accepted stage-1 split):
1. Identify `Aplus / ker p` with `A`. The affine étale criterion
   (`lem-weil-pbc-etale-ring-map-iff-etale-affine`) and
   `lem-exc-etale-algebra-lift` give an étale `Aplus`-algebra `C` whose
   reduction modulo `(ker p) C` is `B`.
2. The same criterion gives vanishing of the first cotangent homology and
   of the differentials of `C`. The latter zero module is projective.
   Apply `lem-weil-pbc-smooth-ring-map-square-zero-lifting` to lift the
   reduction map to an `Aplus`-algebra map `phi : C → Bplus` over `B`.
3. By `lem-weil-pbc-etale-algebra-flat`, `C` is flat. Apply
   `lem-weil-pbc-ideal-cotangent-flat-base-change-ring`, using the two
   vanishing ideal squares, to identify `(ker p) C` with
   `(ker p) tensor_A B`. The balancing relations and pure tensor generation
   are those of `def-weil-pbc-module-tensor-product`.
4. On a pure tensor represented by `i` and a lift `c` of `b`, the kernel
   map sends `v(i) * c` to `algebraMap Aplus Bplus i * phi(c)`.
   The equation `he` therefore identifies it with the assumed isomorphism
   `e`. Changing a lift changes the product by an element of `(ker q)^2`.
5. If `phi(c)=0`, reduction puts `c` in its kernel ideal and the kernel
   isomorphism makes `c=0`. To lift `bplus`, first lift its reduction to
   `c`, then correct `c` by an element of the kernel ideal. Thus `phi` is
   bijective, and identifies the given map with the étale structure map
   of `C`. The affine criterion gives the asserted conclusion. -/
theorem etale_of_squareZero_kernel_comparison
    {Aplus : Type u} {A : Type v} {Bplus : Type w} {B : Type t}
    [CommRing Aplus] [CommRing A] [CommRing Bplus] [CommRing B]
    [Algebra Aplus Bplus] [Algebra Aplus B]
    (p : Aplus →+* A) (q : Bplus →ₐ[Aplus] B) (u : A →+* B)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hcomm : u.comp p = algebraMap Aplus B)
    (hI : (RingHom.ker p) ^ 2 = ⊥) (hJ : (RingHom.ker q.toRingHom) ^ 2 = ⊥)
    (hu : u.Etale)
    (e : (RingHom.ker p) ⊗[Aplus] B ≃ₗ[Aplus] RingHom.ker q.toRingHom)
    (he : ∀ (i : RingHom.ker p) (b : Bplus),
      (e (i ⊗ₜ[Aplus] q b) : Bplus) = algebraMap Aplus Bplus (i : Aplus) * b) :
    (algebraMap Aplus Bplus).Etale := by
  sorry

end RingHom
