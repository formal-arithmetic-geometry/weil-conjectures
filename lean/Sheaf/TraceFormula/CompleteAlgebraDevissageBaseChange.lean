/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.TraceFormula.CompleteAlgebraDevissage
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Complete algebra dévissage under pointed base change

Source: Stacks Project, flat.tex, Tags 05HJ, 05HX and 05I0
(blueprint: lem-sfb-complete-algebra-devissage-base-change).

The module convention is extension of scalars along `A → T ⊗[R] A`. Its underlying
module `(T ⊗[R] A) ⊗[A] M` is canonically `T ⊗[R] M`, hence also `M ⊗[R] T`.
The identification sends `(t ⊗ a) ⊗ m` to `t ⊗ (a • m)`; its inverse sends
`t ⊗ m` to `(t ⊗ 1) ⊗ m`. Thus the scalar structures are the canonical ones.
The conclusion identifies all algebras, modules, algebra maps, free ranks, and
module maps of the given dévissage after tensoring, including its specified
first and successive cokernel isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.CompleteAlgebraDevissage

/-- Canonical module extension along `A → T ⊗[R] A`, using Mathlib's extension functor.
This is the tensor module `M ⊗[R] T`, with the scalar action of the tensor algebra,
represented as `(T ⊗[R] A) ⊗[A] M` by the explicit identification in the module docstring.

Source: Stacks Project, Tags 05HJ and 05HX
(blueprint: lem-sfb-complete-algebra-devissage-base-change). -/
noncomputable abbrev tensorModule (R T A : Type u) [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra R A] (M : ModuleCat.{v} A) : ModuleCat (T ⊗[R] A) :=
  (ModuleCat.extendScalars
    (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom).obj M

/-- The canonical tensor unit `m ↦ (1 ⊗ 1) ⊗ m`, equivalently `m ↦ m ⊗ 1`.
It is Mathlib's pure tensor, with restriction along the canonical algebra inclusion.

Source: Stacks Project, Tag 05HJ, tensoring the maps of Tag 05HX
(blueprint: lem-sfb-complete-algebra-devissage-base-change). -/
noncomputable def tensorUnit (R T A : Type u) [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra R A] (M : ModuleCat.{v} A) : M → tensorModule R T A M :=
  fun m ↦ (1 : T ⊗[R] A) ⊗ₜ[A,
    (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A).toRingHom] m

/-- Every given complete algebra dévissage survives arbitrary pointed base change,
with all its data canonically tensored and with the same length, also at length zero.
The equivalence of finite index sets preserves their values and therefore their order.
The equations on tensor units specify the base-changed linear maps uniquely, because
these units generate after extension of scalars. No flatness or finite presentation
of the base change is assumed.

Source: Stacks Project, Tag 05HJ (lemma-base-change-complete), interpreted in the
algebra data of Tag 05HX (definition-complete-devissage-algebra) via Tag 05I0
(blueprint: lem-sfb-complete-algebra-devissage-base-change).

Proof plan:
1. Tensor the algebras, modules and maps of the given dévissage. The tensor products
   of a finite generating family generate each new module; algebra generators give
   finite type of the new ambient algebra. The finite free sources retain their ranks.
2. Right exactness (lem-weil-pbc-tensor-right-exact) preserves the surjections.
   Finite presentation is preserved by base change, using the balancing isomorphism
   `D ⊗[C] (T ⊗[R] C) ≃ T ⊗[R] D`
   (lem-weil-pbc-finite-presentation-base-change-composition).
3. Smoothness and geometrically irreducible fibres survive base change, by
   lem-weil-pbc-smooth-ring-map-base-change-composition and the geometric fibre
   definition def-pc-geometrically-irreducible. The extended maps remain finite.
4. For each new `B`, its quotient by the extended base prime is smooth and flat over
   the base domain. It injects into its generic fibre by lem-weil-pbc-flat-tensor-exact
   and lem-weil-pbc-smooth-ring-map-flat. That fibre is irreducible and nonempty by
   step 3, and reduced by sbc-lem-smooth-geometrically-reduced, hence a domain
   (def-pc-integral-scheme). Its subring is a domain, so the extended ideal is prime.
5. The original base-prime quotient injects into the new base-prime quotient.
   Tensor with the original smooth algebra, which is flat, to show that the new
   extended prime contracts to the original extended prime. Passing to fractions
   gives the canonical residue-field extension (def-weil-pbc-localization-at-prime).
6. Both new generic-fibre modules identify with the original generic-fibre modules
   tensored with this residue-field extension. The new alpha is the tensor of the
   old isomorphism; tensoring its inverse proves it is an isomorphism.
7. Right exactness identifies the new cokernel with the tensor of the old cokernel.
   Tensor the first and successive cokernel isomorphisms and their inverses. The last
   cokernel remains zero. This also gives the displayed compatibility equations.
8. These are all the conditions of def-trf-complete-algebra-devissage, on the same
   ordered index set. At length zero the original module is zero, so its tensor is
   zero and the empty sequence works. No kernel preservation or flat base change
   has been used. -/
theorem exists_baseChange
    (R T A : Type u) [CommRing R] [CommRing T] [CommRing A]
    [Algebra R T] [Algebra R A] [Algebra.FiniteType R A]
    (N : ModuleCat.{v} A) [Module.Finite A N]
    (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    (hpq : Ideal.comap (algebraMap R T) q = p)
    (D : AlgebraicGeometry.CompleteAlgebraDevissage R A p N) :
    Algebra.FiniteType T (T ⊗[R] A) ∧
      ∃ (hN : Module.Finite (T ⊗[R] A) (tensorModule R T A N)),
      ∃ D' : @AlgebraicGeometry.CompleteAlgebraDevissage T (T ⊗[R] A) _ _ _
        inferInstance q _ (tensorModule R T A N) _ _ hN,
      ∃ (e : Fin D.n ≃ Fin D'.n) (he : ∀ i, (e i).val = i.val),
      ∃ (ae : ∀ i, (T ⊗[R] D.A i) ≃ₐ[T] D'.A (e i))
        (be : ∀ i, (T ⊗[R] D.B i) ≃ₐ[T] D'.B (e i)),
      ∃ (me : ∀ i, tensorModule R T (D.A i) (D.M i) ≃ₗ[T ⊗[R] D.A i]
        (ModuleCat.restrictScalars (ae i).toAlgHom.toRingHom).obj (D'.M (e i))),
      ∃ (hr : ∀ i, D'.rIndex (e i) = D.rIndex i),
        (∀ (i : Fin D.n) (b : D.B i),
          ae i (1 ⊗ₜ[R] D.bToA i b) = D'.bToA (e i) (be i (1 ⊗ₜ[R] b))) ∧
        (∀ (i : Fin D.n) (hi : i.val = 0) (a : A),
          ae i (1 ⊗ₜ[R] D.sToA i hi a) =
            D'.sToA (e i) ((he i).trans hi) (1 ⊗ₜ[R] a)) ∧
        (∀ (i j : Fin D.n) (hij : j.val = i.val + 1) (b : D.B i),
          ae j (1 ⊗ₜ[R] D.bToAnext i j hij b) =
            D'.bToAnext (e i) (e j)
              ((he j).trans (hij.trans (congrArg (· + 1) (he i).symm)))
              (be i (1 ⊗ₜ[R] b))) ∧
        (∀ (i : Fin D.n) (f : Fin (D.rIndex i) → D.B i),
          me i (tensorUnit R T (D.A i) (D.M i) (D.alpha i f)) =
            D'.alpha (e i) (fun j ↦ be i (1 ⊗ₜ[R] f (Fin.cast (hr i) j)))) ∧
        (∀ (i : Fin D.n) (hi : i.val = 0) (m : N),
          me i (tensorUnit R T (D.A i) (D.M i) (D.firstIso i hi m)) =
            D'.firstIso (e i) ((he i).trans hi) (tensorUnit R T A N m)) ∧
        (∀ (i j : Fin D.n) (hij : j.val = i.val + 1) (m : D.M i),
          me j (tensorUnit R T (D.A j) (D.M j)
            (D.cokerIso i j hij (Submodule.Quotient.mk m))) =
            D'.cokerIso (e i) (e j)
              ((he j).trans (hij.trans (congrArg (· + 1) (he i).symm)))
              (Submodule.Quotient.mk (me i (tensorUnit R T (D.A i) (D.M i) m)))) := by
  sorry

end AlgebraicGeometry.CompleteAlgebraDevissage
