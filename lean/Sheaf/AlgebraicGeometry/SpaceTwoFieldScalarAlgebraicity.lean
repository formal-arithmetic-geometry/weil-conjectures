/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Basic

/-!
# Algebraicity of scalars from two field structures on an algebraic space

Source: Stacks Project, Varieties, Tag 04MK (proposition-unique-base-field),
with the pointwise application used in Stacks Morphisms, Tag 0DTM
(blueprint: lem-sfb-space-two-field-scalar-algebraicity).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two locally finite type field structures give mutually algebraic scalar images
at every field-valued point. The equations `hj₁` and `hj₂` identify the ring maps
with the composites of that point and the two structure morphisms. Local finite
type is tested on every representable étale scheme chart, without surjectivity.

Source: Stacks Project, Varieties, Tag 04MK (proposition-unique-base-field);
Stacks Morphisms, Tag 0DTM (lemma-universally-injective-point)
(blueprint: lem-sfb-space-two-field-scalar-algebraicity).

Proof:
1. Choose a surjective étale scheme atlas U → E and a point v of its pullback to
   Spec F. Put L = κ(v). The residue-field map gives an embedding h : F → L and
   a lift Spec L → U. The two scalar maps into L are h ∘ jᵢ. This uses
   def-trf-algebraic-space, lem-weil-pbc-morphism-from-spec-field and
   def-weil-affine-spectrum.
2. Choose an affine neighbourhood Spec A of the image in U. The lift factors
   through it and gives ψ : A → L. Both chart maps are locally of finite type,
   so A is finitely generated over each kᵢ, with ψ ∘ αᵢ = h ∘ jᵢ. Use
   lem-weil-pbc-affine-opens-basis, lem-weil-pbc-affine-open-spec-points,
   lem-weil-pbc-morphism-factors-through-open-subscheme,
   lem-weil-pbc-lft-affine-pairs and def-weil-affine-spectrum.
3. The kernel of ψ is prime. Its quotient B is a nonzero domain embedded in L,
   and the images of any finite algebra generating set still generate B over
   kᵢ. Thus Spec B is locally of finite type over both fields, whose scalar maps
   ρᵢ into B are injective. This is the elementary quotient-generator argument
   from def-weil-field, def-weil-affine-spectrum and def-weil-finite-type-morphism.
4. Spec B is reduced, nonempty and irreducible, hence connected. Use
   lem-weil-pbc-affine-scheme-reduced-iff,
   lem-weil-pbc-spec-irreducible-closed-subsets-primes and
   lem-pc-irreducible-space-connected.
5. Apply lem-sfb-connected-reduced-scalar-field-uniqueness (Tag 04MK): the
   integral closures of the two fields in B agree. Since ρ₁(λ) is integral over
   k₁, it is integral over k₂. It therefore satisfies a monic polynomial over
   k₂ of positive degree; degree zero is impossible in the nonzero ring B.
   The affine-global-sections identification is def-weil-affine-spectrum.
6. Map this relation to L, using the embedding B → L, then reflect it along the
   injective h : F → L. The resulting polynomial over k₂ annihilates j₁(λ)
   under evaluation through j₂ and is nonzero because it is monic. Interchange
   the indices for the other assertion. This uses only def-weil-field and
   def-weil-polynomial-ring. No global condition on E is used. -/
theorem scalar_algebraicity_of_two_locallyOfFiniteType
    {S : Scheme.{u}} (E : AlgebraicSpace S)
    (k₁ k₂ F : Type u) [Field k₁] [Field k₂] [Field F]
    (s₁ : Spec (CommRingCat.of k₁) ⟶ S) (s₂ : Spec (CommRingCat.of k₂) ⟶ S)
    (sF : Spec (CommRingCat.of F) ⟶ S)
    (p₁ : E.obj.obj ⟶ yoneda.obj (Over.mk s₁))
    (p₂ : E.obj.obj ⟶ yoneda.obj (Over.mk s₂))
    (hp₁ : ∀ (U : Over S) (a : yoneda.obj U ⟶ E.obj.obj), IsEtale a →
      LocallyOfFiniteType (yoneda.preimage (a ≫ p₁)).left)
    (hp₂ : ∀ (U : Over S) (a : yoneda.obj U ⟶ E.obj.obj), IsEtale a →
      LocallyOfFiniteType (yoneda.preimage (a ≫ p₂)).left)
    (e : yoneda.obj (Over.mk sF) ⟶ E.obj.obj)
    (j₁ : k₁ →+* F) (j₂ : k₂ →+* F)
    (hj₁ : (yoneda.preimage (e ≫ p₁)).left = Spec.map (CommRingCat.ofHom j₁))
    (hj₂ : (yoneda.preimage (e ≫ p₂)).left = Spec.map (CommRingCat.ofHom j₂)) :
    (∀ x : k₁, ∃ P : Polynomial k₂, P ≠ 0 ∧ P.eval₂ j₂ (j₁ x) = 0) ∧
      (∀ x : k₂, ∃ P : Polynomial k₁, P ≠ 0 ∧ P.eval₂ j₁ (j₂ x) = 0) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
