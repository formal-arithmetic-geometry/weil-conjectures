/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.FiniteStability
import Mathlib.Algebra.Module.FinitePresentation

/-!
# Flat and finitely presented algebras over a ring fibre product

Source: Stacks Project, More on Algebra, Situation 08KH and Lemma 08KQ,
parts (2), (3), and the final assertion
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation).

In `CommRingCat`, `pullback b q` is canonically the coordinatewise ring
`B ×[A] A'`, and `pushout b d` is canonically `A ⊗[B] D`.
For a surjection `q : A' ⟶ A` with kernel I, `pushout q c` is canonically
`C'/IC'`. The compatibility equation on the pushout isomorphism says exactly
that this is an A-algebra isomorphism. The helpers below construct the specified
structure map and the specified flat-algebra reconstruction map by universal properties.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat.FibreProductAlgebra

/-- The canonical structure map `B ×[A] A' → D ×[C] C'`.
Source: Stacks Project, Situation 08KH and Lemma 08KQ
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation).
The two coordinates are induced by the given algebra structure maps `d` and `c`;
the A-algebra compatibility of φ makes them agree over C. -/
noncomputable def structureMap
    {A A' B D C' : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (d : B ⟶ D) (c : A' ⟶ C') (φ : pushout b d ≅ pushout q c)
    (hφ : pushout.inl b d ≫ φ.hom = pushout.inl q c) :
    pullback b q ⟶ pullback (pushout.inr b d ≫ φ.hom) (pushout.inr q c) :=
  pullback.map b q (pushout.inr b d ≫ φ.hom) (pushout.inr q c)
    d c (pushout.inl q c)
    (by rw [← hφ, ← Category.assoc, pushout.condition, Category.assoc])
    (pushout.condition (f := q) (g := c))

/-- The map `L ⊗[R] B → L ⊗[R] A` induced by `b`, where `R = B ×[A] A'`.
Source: Stacks Project, Lemma 08KQ, final assertion
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation). -/
noncomputable def baseChangeLeft
    {A A' B L : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (ℓ : pullback b q ⟶ L) :
    pushout ℓ (pullback.fst b q) ⟶ pushout ℓ (pullback.fst b q ≫ b) :=
  pushout.map ℓ (pullback.fst b q) ℓ (pullback.fst b q ≫ b)
    (𝟙 L) b (𝟙 (pullback b q)) (by simp) (by simp)

/-- The map `L ⊗[R] A' → L ⊗[R] A` induced by `q`, where `R = B ×[A] A'`.
Source: Stacks Project, Lemma 08KQ, final assertion
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation). -/
noncomputable def baseChangeRight
    {A A' B L : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (ℓ : pullback b q ⟶ L) :
    pushout ℓ (pullback.snd b q) ⟶ pushout ℓ (pullback.fst b q ≫ b) :=
  pushout.map ℓ (pullback.snd b q) ℓ (pullback.fst b q ≫ b)
    (𝟙 L) q (𝟙 (pullback b q)) (by simp)
    (by simpa using (pullback.condition (f := b) (g := q)).symm)

/-- The canonical ring homomorphism from L to the fibre product of its two base changes.
Its coordinates are `l ↦ l ⊗ 1`; it is defined for every algebra L without flatness.
Source: Stacks Project, Lemma 08KQ, final assertion
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation). -/
noncomputable def reconstruction
    {A A' B L : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (ℓ : pullback b q ⟶ L) :
    L ⟶ pullback (baseChangeLeft b q ℓ) (baseChangeRight b q ℓ) :=
  pullback.lift (pushout.inl ℓ (pullback.fst b q))
    (pushout.inl ℓ (pullback.snd b q))
    (by simp [baseChangeLeft, baseChangeRight])

/-- Flatness, flat finite presentation, and reconstruction for algebras over a ring
fibre product along an arbitrary surjection; zero rings are permitted.
Source: Stacks Project, Situation 08KH, Lemma 08KQ (2), (3), and final assertion
(blueprint: lem-sfb-fibre-product-algebra-flat-presentation).

Proof:
1. The underlying compatible modules satisfy [lem-sfb-patched-module-base-change].
   Its canonical base-change isomorphisms identify E tensor B with D and E tensor A'
   with C'. Their displayed coordinate formulas preserve multiplication and units.
2. Flat base change [lem-weil-pbc-flat-module-base-change] and finite-presentation
   base change [lem-weil-pbc-finite-presentation-base-change-composition] give both
   forward implications.
3. Apply [lem-sfb-flat-module-fibre-product-patching] to the underlying flat modules
   D and C' for the reverse flatness implication. Its assertion for an arbitrary
   flat module L makes the canonical reconstruction map bijective. Both coordinates
   preserve products and units, so it is an isomorphism of rings.
4. For the reverse finite-presentation implication, lift finite algebra generators
   of D to E and express finite generators of C' using E tensor A'. Combine these
   into a finite list of elements of E generating both scalar extensions.
5. The polynomial ring P = R[t_1,...,t_n] is the coefficientwise pullback of the
   corresponding polynomial rings over B and A' over the one over A. Evaluation
   gives surjections to D and C'; their reductions agree because the variables
   are chosen in E. Apply [lem-sfb-finite-module-fibre-product-patching] to make E
   finite as a P-module. Append its module generators to the chosen list, making
   the polynomial evaluation P → E surjective.
6. The two polynomial evaluation kernels are finitely generated by
   [lem-weil-pbc-finite-presentation-surjection-kernel-fg], so D and C' are finitely
   presented modules over their polynomial rings [def-sc-finitely-presented-module].
   Also P is flat over R since its monomials form a free R-module basis.
7. Apply [lem-sfb-relative-fp-module-fibre-product] with ambient algebra P to make
   E finitely presented over P. The kernel of the surjection P → E is finitely
   generated by [lem-trf-finite-presentation-surjective-module-kernel]. This gives
   a finite polynomial algebra presentation of E over R. Combine with step 3.
-/
theorem flat_and_finitePresentation_iff
    {A A' B D C' : CommRingCat.{u}} (b : B ⟶ A) (q : A' ⟶ A)
    (hq : Function.Surjective q) (d : B ⟶ D) (c : A' ⟶ C')
    (φ : pushout b d ≅ pushout q c)
    (hφ : pushout.inl b d ≫ φ.hom = pushout.inl q c) :
    ((structureMap b q d c φ hφ).hom.Flat ↔ d.hom.Flat ∧ c.hom.Flat) ∧
    (((structureMap b q d c φ hφ).hom.Flat ∧
        (structureMap b q d c φ hφ).hom.FinitePresentation) ↔
      (d.hom.Flat ∧ d.hom.FinitePresentation) ∧
        (c.hom.Flat ∧ c.hom.FinitePresentation)) ∧
    (∀ (L : CommRingCat.{u}) (ℓ : pullback b q ⟶ L),
      ℓ.hom.Flat → IsIso (reconstruction b q ℓ)) := by
  sorry

end CommRingCat.FibreProductAlgebra
