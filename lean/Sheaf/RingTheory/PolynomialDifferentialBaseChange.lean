/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.RingTheory.Kaehler.Polynomial
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import Sheaf.TraceFormula.OnePointDerivedRingIdentification

/-!
# Derived base change of polynomial differential complexes

Source: Stacks Project, Cotangent Complex, Tag 08QQ, proof, and Algebra,
Tags 00RX and 00RV (blueprint: lem-trf-polynomial-differential-base-change).

The tensor-product algebras are specified by their pushout universal property.
Thus `h.map` is the inclusion `p ↦ p ⊗ 1`, and the augmentation is necessarily
`p ⊗ a' ↦ f(ε(p)) a'`. This permits any realization of the tensor product.
Both differential models use the recorded nonpositive alternating complex.
Ordinary extension of scalars writes the scalar factor first, using symmetry
of tensor products to match the differential-first formula in the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite Simplicial
open scoped ChangeOfRings

namespace Algebra.CotangentResolution

/-- Polynomial differential complexes have flat terms, are K-flat, and have the
canonical derived scalar-extension comparison, even without a resolution.
Source: Stacks Project, Tag 08QQ, proof; Tags 00RX, 00RV and 064K
(blueprint: lem-trf-polynomial-differential-base-change).

The pushout condition specifies `P' = P ⊗_A A'`, including its two inclusions.
`AugmentedMap` specifies the augmentation on the first inclusion, and
`P'.triangle` specifies it on the coefficient inclusion. The simplicial
isomorphism commutes with every operator, hence with faces and degeneracies.
Its formula and the chain formula specify the same comparison on generators.
The last equality says precisely `Θ = Q(θ) c_K`, in composition order in Lean,
where `c_K` is the universal derived-to-ordinary counit at the K-flat complex.

Proof:
1. Apply lem-weil-pbc-polynomial-ring-kahler-basis-any-variables to each term.
After scalar extension to C its differentials have basis dx_i tensor 1.
Tensoring with such a module gives finitely supported families; an injection
remains injective coordinatewise, proving flatness, also for zero positive terms.
2. The same coordinatewise description preserves exact sequences. The complex
is zero in positive degrees, so lem-pc-module-bounded-flat-kflat makes it K-flat.
3. Tensor associativity identifies (Omega tensor C) tensor C' with Omega tensor C':
(omega tensor c) tensor b' goes to omega tensor f(c)b', with inverse
omega tensor b' going to (omega tensor 1) tensor b'. Balancing verifies both maps.
4. Apply lem-trf-simplicial-differential-base-change with coefficient ring C'.
Its generator formula, combined with step 3, is the formula below. For every
simplicial operator both composites send dp to the differential of its image.
The term isomorphisms therefore give the simplicial isomorphism and, by signed
sums of faces and extension by zero, the chain isomorphism theta.
5. Apply lem-pur-derived-change-of-rings to the identity K-flat resolution.
Transport by lem-trf-one-point-derived-ring-identification gives the ordinary
universal counit, invertible at K. Localize theta and compose with this counit
to obtain Theta. Tensor expressions have finite support even for infinite
variable sets; empty sets give zero differential modules. No step uses flatness
of either ring map, surjectivity of the augmentation, or a resolution condition. -/
theorem polynomial_differential_base_change
    {f g : Arrow CommRingCat.{u}} (q : f ⟶ g)
    (P : Augmentation f) (P' : Augmentation g) (h : AugmentedMap q P P')
    (hpolynomial : ∀ n : ℕ, ∃ (I : Type u)
      (e : CommRingCat.of (MvPolynomial I f.left) ≅ P.algebra.obj (op ⦋n⦌)),
      ∀ a : f.left, e.hom (MvPolynomial.C a) = P.base.app (op ⦋n⦌) a)
    (hbase : ∀ n : ℕ, CategoryTheory.IsPushout (P.base.app (op ⦋n⦌)) q.left
      (h.map.app (op ⦋n⦌)) (P'.base.app (op ⦋n⦌)))
    (D : DifferentialModel P) (D' : DifferentialModel P') :
    (∀ i : ℤ, Module.Flat f.right ((differentialComplex D).X i)) ∧
    (HomologicalComplex.quasiIso (ModuleCat.{u} f.right) (.up ℤ)).kFlat
      (differentialComplex D) ∧
    IsIso ((ModuleCat.ordinaryDerivedChangeOfRings q.right.hom).counit.app
      (differentialComplex D)) ∧
    ∃ (s : D.module ⋙ ModuleCat.extendScalars q.right.hom ≅ D'.module)
      (θ : ((ModuleCat.extendScalars q.right.hom).mapHomologicalComplex (.up ℤ)).obj
        (differentialComplex D) ≅ differentialComplex D')
      (Θ : (ModuleCat.ordinaryDerivedExtendScalars q.right.hom).obj
        (DerivedCategory.Q.obj (differentialComplex D)) ≅
          DerivedCategory.Q.obj (differentialComplex D')),
      (∀ (n : ℕ) (c : f.right) (b' : g.right) (p : P.algebra.obj (op ⦋n⦌)),
        s.hom.app (op ⦋n⦌)
            (b' ⊗ₜ[_, q.right.hom] ((D.termIso n).inv (differentialGenerator P n c p))) =
          (D'.termIso n).inv (differentialGenerator P' n (q.right c * b')
            (h.map.app (op ⦋n⦌) p))) ∧
      (∀ (n : ℕ) (c : f.right) (b' : g.right) (p : P.algebra.obj (op ⦋n⦌)),
        θ.hom.f (-(n : ℤ)) (b' ⊗ₜ[_, q.right.hom] (complexGenerator D n c p)) =
          complexGenerator D' n (q.right c * b') (h.map.app (op ⦋n⦌) p)) ∧
      Θ.hom = (ModuleCat.ordinaryDerivedChangeOfRings q.right.hom).counit.app
        (differentialComplex D) ≫ DerivedCategory.Q.map θ.hom := by
  sorry

end Algebra.CotangentResolution
