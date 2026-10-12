/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.ULift
import Sheaf.RingTheory.TwoTermKernelBaseChange

/-!
# The full Jacobi–Zariski homology sequence

Source: Stacks Project, Algebra, Tag 00S2, `lemma-exact-sequence-NL`
(blueprint: lem-weil-pbc-jacobi-zariski-homology-sequence).
-/

@[expose] public section

universe u v w

open TensorProduct KaehlerDifferential CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- Source: Stacks Project, Algebra, Tag 00S2, `lemma-exact-sequence-NL`
(blueprint: lem-weil-pbc-jacobi-zariski-homology-sequence).

The presentations are the canonical polynomial presentations. Tensor products are written
with `C` on the left, using the symmetry over `B`. The equations for `u` and `t` specify their
ambient conormal maps and hence their well-defined restrictions to the kernels. The maps
`v`, `w`, `z`, and the snake connecting map are Mathlib's canonical maps. The coefficient
formula specifies the connecting map on every polynomial representative. ULift only puts
both Tor arguments in a common module universe.

Proof (the node's ten steps). (1) Use the polynomial differential basis to identify the
canonical cotangent complexes with the presentation complexes. (2) Include A[B] into
A[B,C] and map A[B,C] to B[C]; these commute with the differentials and have zero composite
on conormals. (3) The row of free differential modules is split exact by its B- and C-bases.
(4) The conormal row is right exact: the coefficient map has kernel I A[B,C], whose image
modulo K squared is exactly the image of C tensor I/I squared.
(5) Apply the module snake lemma to obtain the six-term kernel/cokernel sequence.
(6) Identify its cokernels with Kahler differentials by the conormal exact sequence and
right exactness of tensor product. (7) Compare A[B,C] with A[C] in both directions;
presentation independence of H1 identifies their kernels and the specified maps u and v.
(8) Transport snake exactness across this isomorphism. (9) Apply the two-term complex
kernel base-change lemma: the degree-zero term is free, and Tor in degrees one and two
vanishes, so the natural kernel tensor map is bijective. (10) Lift each coefficient b of
a polynomial in B[C] to the variable [b] in A[B,C]. Its differential in the B-directions
is the coefficient-derivative sum displayed below, and its C-directions vanish because
the representative is a cycle. This computes the snake connecting map.
Dependency nodes by step: (1), (3), (10)
`lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`; (1), (2), (7)
`lem-weil-pbc-nl-presentation-h1-functoriality`; (4)
`lem-weil-pbc-polynomial-coefficient-map-kernel`; (5), (10)
`lem-weil-pbc-snake-lemma-modules`; (6), (9)
`lem-weil-pbc-jacobi-zariski-differential-maps`; (6)
`lem-weil-pbc-tensor-right-exact`; (9)
`lem-weil-pbc-two-term-complex-kernel-base-change` and `def-weil-pbc-tor-modules`.
Step (8) is elementary transport of images and kernels through an isomorphism. -/
theorem jacobiZariski_homology_sequence
    (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    let P := (Generators.self A B).toExtension
    let Q := (Generators.self B C).toExtension
    let E := (Generators.self A C).toExtension
    let K := (P.cotangentComplex.baseChange C).ker
    let f := Extension.Cotangent.map
      (Generators.defaultHom (Generators.self A B) (Generators.self A C)).toExtensionHom
    let v := H1Cotangent.map A B C C
    let w := KaehlerDifferential.mapBaseChange A B C
    let z := KaehlerDifferential.map A B C C
    let δ := H1Cotangent.δ A B C
    ∃ (u : K →ₗ[C] H1Cotangent A C)
      (t : C ⊗[B] H1Cotangent A B →ₗ[C] K),
      (∀ x : K, E.h1Cotangentι (u x) = f.liftBaseChange C x.val) ∧
      (∀ (c : C) (h : H1Cotangent A B),
        (t (c ⊗ₜ[B] h)).val = c ⊗ₜ[B] P.h1Cotangentι h) ∧
      (∀ (g : Q.ker) (h : H1Cotangent B C),
        Q.h1Cotangentι h = Extension.Cotangent.mk g →
        δ h = ∑ α ∈ g.val.support,
          (α.prod (fun c n ↦ c ^ n)) ⊗ₜ[B] D A B (MvPolynomial.coeff α g.val)) ∧
      Function.Exact u v ∧ Function.Exact v δ ∧ Function.Exact δ w ∧
      Function.Exact w z ∧ Function.Surjective z ∧
      ((IsZero (((Tor' (ModuleCat (ULift.{max u v w} B)) 1).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} Ω[B⁄A]))).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} C))) ∧
        IsZero (((Tor' (ModuleCat (ULift.{max u v w} B)) 2).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} Ω[B⁄A]))).obj
          (ModuleCat.of (ULift.{max u v w} B) (ULift.{max u v w} C)))) → Function.Bijective t) := by
  sorry

end Algebra
