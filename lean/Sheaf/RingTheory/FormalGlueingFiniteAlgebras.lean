/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.RingTheory.FormalGlueingData
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.FormalGlueingEquivalence
import Sheaf.RingTheory.FormalGlueingComplexExact
import Sheaf.RingTheory.FiniteIffFormalGlueing
import Sheaf.RingTheory.FormalGlueingH0

/-!
# Formal glueing of finite commutative algebras

Source: Stacks Project, More on Algebra, Proposition 05ER and Remark 05EU,
including its tensor-structure and algebra-category assertion
(blueprint: lem-per-formal-glueing-finite-algebras).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace FormalGlueing

/-- Finite commutative algebra data algebraize under the formal glueing hypotheses.
The algebra map `R → S` is `algebraMap R S`. The scalar towers specify the restrictions
of the given `S`- and `R_f`-algebras. The witness in `hdata` identifies the underlying
modules and transition maps with an object of the recorded module glueing category;
its `alpha_smul` makes `alpha` linear over `S`, hence over `S_f`. Similarly, the
`R`-algebra overlap equivalences are automatically linear over `R_{f_i f_j}`.
The conclusion's equations on images of `D` specify both commuting squares: scalar
linearity extends the first to pure tensors and fractions, and the second to double
fractions. Thus the resulting component algebra equivalences give an isomorphism
of the canonical glueing datum with the prescribed one.

Source: Stacks Project, More on Algebra, Proposition 05ER and Remark 05EU
(blueprint: lem-per-formal-glueing-finite-algebras).

Proof (the node's six steps):
1. Forget multiplication and use the essential-surjectivity part of
   [prop-weil-pbc-formal-glueing-equivalence] to obtain an R-module M and compatible
   component module equivalences from its canonical datum to the specified datum.
2. Construct D as the subring of E' times the product of the E_i consisting of
   matching tuples. The matching equations are preserved by addition, negation,
   multiplication, one and the R-action because the transitions are algebra maps.
   Its underlying R-module is [def-weil-pbc-formal-glueing-H0].
3. Send m to the images of m tensor 1 and m/1 under the component equivalences.
   These maps identify the canonical matching tuples with those defining D, in
   both directions. Exactness [lem-weil-pbc-formal-glueing-complex-exact] therefore
   makes this R-linear map M to D bijective.
4. Extend the prime projection by q'(s tensor d) = s times p'(d), and localize
   each chart projection by q_i(d/f_i^n) = p_i(d)/f_i^n. They preserve products and
   one, and their composites with the scalar extension and localizations of the
   preceding bijection are the original component equivalences. Thus they are
   algebra equivalences [def-weil-module-base-change,
   def-weil-pbc-module-localization-away].
5. The defining matching equations of D give both displayed compatibility
   equations. S-linearity extends the prime equation to pure-tensor fractions;
   R-linearity and invertibility of f_i and f_j extend the overlap equation to
   double fractions. These generate the domains, so both full squares commute.
6. By [lem-weil-pbc-formal-glueing-finite-modules], D is finite over R, because
   its scalar extension and chart localizations are the given finite modules. -/
theorem exists_finite_algebra_of_formalGlueing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (t : ℕ) (f : Fin t → R)
    (hflat : (algebraMap R S).Flat)
    (hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (E' : Type w) [CommRing E'] [Algebra S E'] [Algebra R E']
    [IsScalarTower R S E']
    (E : Fin t → Type w) [∀ i, CommRing (E i)] [∀ i, Algebra R (E i)]
    [∀ i, Algebra (Localization.Away (f i)) (E i)]
    [∀ i, IsScalarTower R (Localization.Away (f i)) (E i)]
    (alpha : ∀ i : Fin t, LocalizedModule.Away (f i) E' ≃ₐ[R] (S ⊗[R] E i))
    (alphaOverlap : ∀ i j : Fin t,
      LocalizedModule.Away (f j) (E i) ≃ₐ[R] LocalizedModule.Away (f i) (E j))
    (hdata : ∃ X : Data.{u, v, w} (algebraMap R S) f,
      X.M' = ModuleCat.of S E' ∧
      (∀ i : Fin t, X.M i = ModuleCat.of (Localization.Away (f i)) (E i)) ∧
      (∀ i : Fin t, HEq (X.alpha i).toLinearMap (alpha i).toLinearMap) ∧
      (∀ i j : Fin t,
        HEq (X.alpha_overlap i j).toLinearMap (alphaOverlap i j).toLinearMap))
    (hfinitePrime : Module.Finite S E')
    (hfiniteChart : ∀ i : Fin t, Module.Finite (Localization.Away (f i)) (E i)) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra R D),
      Module.Finite R D ∧
      ∃ (a' : (S ⊗[R] D) ≃ₐ[S] E')
        (a : ∀ i : Fin t, LocalizedModule.Away (f i) D ≃ₐ[R] E i),
        (∀ (i : Fin t) (d : D),
          alpha i (LocalizedModule.mk (a' (1 ⊗ₜ[R] d)) 1) =
            1 ⊗ₜ[R] a i (LocalizedModule.mk d 1)) ∧
        (∀ (i j : Fin t) (d : D),
          alphaOverlap i j (LocalizedModule.mk (a i (LocalizedModule.mk d 1)) 1) =
            LocalizedModule.mk (a j (LocalizedModule.mk d 1)) 1) := by
  sorry

end FormalGlueing
