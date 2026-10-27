/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q26
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.AffineFibreSectionsTensor

/-!
# Nonreduced fibres from free annihilator and principal quotients

Source: Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, the argument following the short exact sequence
(blueprint: lem-trf-free-annihilator-nonreduced-fibres).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- A nilpotent on an affine open survives every field base change when its annihilator
quotient is nonzero free and its principal quotient is free. Every whole fibre is nonreduced.

Source: Stacks Project, More on Morphisms, Tag 0575,
`lemma-nonreduced-in-neighbourhood`, after the short exact sequence
(blueprint: lem-trf-free-annihilator-nonreduced-fibres).

Here `Module.annihilator B (Ideal.span {b})` is exactly the ideal of elements killing `b`:
annihilating every multiple of `b` is equivalent to annihilating `b`. The open immersion
`i` presents the affine open `Spec B`, and `hi` specifies its structure map over `Spec A`.

Proof plan:
1. Put C = B/Ann(b) and D = B/bB. Multiplication [x] maps to bx and gives an injective
   A-linear map j : C -> B with image bB, the kernel of the surjective quotient q : B -> D.
2. Choose a basis of free D and lift its elements to B. Finite basis expansions give an
   A-linear section s of q. The identity j(r(x)) = x - s(q(x)) defines an A-linear
   retraction r of j. By def-weil-module-base-change, tensoring rj = id with any field
   gives a retraction, so the base change of j is injective.
3. Since C is nonzero, a basis of C has a nonempty index set. By
   lem-weil-pbc-free-module-base-change-free (Module.Basis.baseChange), its base-changed
   basis makes C tensor k nonzero. If b tensor 1 were zero, the base change of j would
   vanish on all pure tensors and hence everywhere, contradicting injectivity with
   nonzero source. Nilpotence follows by applying the canonical ring map to a power of b.
4. For each t apply step 3 to A -> kappa(t). Use lem-sbc-affine-fibre-sections-tensor
   (affine_fibre_sections_tensor) on the affine open presented by i. The compatibility hi
   identifies its section algebra with the specified A-algebra B. The resulting ring
   isomorphism carries the restricted section b to b tensor 1. Thus an open of f.fiber t
   has a nonzero nilpotent section, contradicting the open-section characterization of
   reducedness in def-pc-reduced-scheme. No domain or finiteness assumption is needed.
-/
theorem free_annihilator_nonreduced_fibres
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (i : Spec (.of B) ⟶ X) [IsOpenImmersion i]
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (b : B) (hb : IsNilpotent b)
    [Nontrivial (B ⧸ Module.annihilator B (Ideal.span ({b} : Set B)))]
    [Module.Free A (B ⧸ Module.annihilator B (Ideal.span ({b} : Set B)))]
    [Module.Free A (B ⧸ Ideal.span ({b} : Set B))] :
    (∀ (k : Type (max u v)) [Field k] [Algebra A k],
      (b ⊗ₜ[A] (1 : k)) ≠ 0 ∧ IsNilpotent (b ⊗ₜ[A] (1 : k))) ∧
    ∀ t : Spec (.of A), ¬ IsReduced (f.fiber t) := by
  sorry

end AlgebraicGeometry
