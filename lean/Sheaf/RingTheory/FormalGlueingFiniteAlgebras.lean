/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations

import WeilConjectures.RingTheory.FormalGlueingEquivalence
import WeilConjectures.RingTheory.FormalGlueingComplexExact
import WeilConjectures.RingTheory.FormalGlueingH0
import Sheaf.RingTheory.FiniteIffFormalGlueing

/-!
# Formal glueing of finite commutative algebras

Source: Stacks Project, More on Algebra, Tags 05ER and 05EU, including the tensor
structure and algebra-category assertion (blueprint: lem-per-formal-glueing-finite-algebras).

Localizations of algebras are written as tensor products with the localized base ring.
The hypothesis `hdatum` identifies their underlying maps with the recorded module datum.
The two concluding equations test the compatibility squares on the image of `D`;
linearity and the invertible denominators extend them to the entire squares.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace FormalGlueing

/-- Finite commutative algebra data algebraize compatibly with every transition map.
Source: Stacks Project, Tags 05ER and 05EU
(blueprint: lem-per-formal-glueing-finite-algebras).

Proof:
1. Forget the algebra structures and use prop-weil-pbc-formal-glueing-equivalence on
   the datum supplied by `hdatum`. Obtain a module `M` with compatible component
   isomorphisms from its canonical datum.
2. In the product of the given algebras, take tuples satisfying the prime-chart and
   chart-chart matching equations of def-weil-pbc-formal-glueing-H0. Coordinatewise
   sums, negatives, products and the unit preserve these equations, since the
   transitions are algebra maps. This is a real commutative R-subalgebra `D`.
3. The component isomorphisms give an R-linear map from `M` to the matching tuples.
   The morphism equations for these isomorphisms and their inverses identify the
   matching equations on both sides. The canonical matching tuples are exactly `M`
   by lem-weil-pbc-formal-glueing-complex-exact, so this map is bijective.
4. The coordinate projections extend to algebra maps from `S ⊗ D` and from each
   localization of `D`. Their composites with the base change and localizations of
   the preceding bijection are the component isomorphisms from step 1, as checked
   on pure tensors and fractions. Hence they are bijective algebra maps.
5. The defining tuple equations give the two displayed compatibility equations.
   S-linearity extends the first to pure tensors and fractions; invertibility of
   both denominators extends the second to double fractions. Additivity gives the
   full compatibility squares, hence an isomorphism of the specified glueing data.
6. The components of `D` are finite by the hypotheses and the algebra isomorphisms.
   Apply lem-weil-pbc-formal-glueing-finite-modules to conclude `Module.Finite R D`.

The R-algebra structures on the input algebras are the restrictions of their given
base-algebra structures, as specified by the scalar towers. Tensor symmetry accounts
for the source's factor order. No nonzero-ring or nonempty-chart hypothesis is used. -/
theorem exists_finite_algebra_of_formalGlueing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (t : ℕ) (f : Fin t → R)
    (hflat : (algebraMap R S).Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (E' : Type w) [CommRing E'] [Algebra S E'] [Algebra R E']
    [IsScalarTower R S E']
    (E : Fin t → Type w) [∀ i, CommRing (E i)]
    [∀ i, Algebra (Localization.Away (f i)) (E i)] [∀ i, Algebra R (E i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (E i)]
    (α : ∀ i, E' ⊗[R] Localization.Away (f i) ≃ₐ[S] S ⊗[R] E i)
    (αij : ∀ i j, E i ⊗[R] Localization.Away (f j) ≃ₐ[R]
      E j ⊗[R] Localization.Away (f i))
    (hdatum : ∃ X : Data.{u, v, w} (algebraMap R S) f,
      X.M' = ModuleCat.of S E' ∧
      (∀ i, X.M i = ModuleCat.of (Localization.Away (f i)) (E i)) ∧
      (∀ i, HEq (fun x : X.M' ↦ X.alpha i (LocalizedModule.mk x 1))
        (fun x : E' ↦ α i (x ⊗ₜ[R] 1))) ∧
      (∀ i j, HEq
        (fun x : piece (f i) (X.M i) ↦
          (TensorProduct.comm R (Localization.Away (f i)) (piece (f j) (X.M j)))
            ((LocalizedModule.equivTensorProduct (Submonoid.powers (f i))
              (piece (f j) (X.M j)))
                (X.alpha_overlap i j (LocalizedModule.mk x 1))))
        (fun x : E i ↦ αij i j (x ⊗ₜ[R] 1))))
    (hfinite' : Module.Finite S E')
    (hfinite : ∀ i, Module.Finite (Localization.Away (f i)) (E i)) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra R D),
      Module.Finite R D ∧
      ∃ (q' : S ⊗[R] D ≃ₐ[S] E')
        (q : ∀ i, Localization.Away (f i) ⊗[R] D ≃ₐ[Localization.Away (f i)] E i),
        (∀ (i : Fin t) (d : D),
          α i (q' (1 ⊗ₜ[R] d) ⊗ₜ[R] 1) = 1 ⊗ₜ[R] q i (1 ⊗ₜ[R] d)) ∧
        (∀ (i j : Fin t) (d : D),
          αij i j (q i (1 ⊗ₜ[R] d) ⊗ₜ[R] 1) = q j (1 ⊗ₜ[R] d) ⊗ₜ[R] 1) := by
  sorry

end FormalGlueing
