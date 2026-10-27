/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.RingTheory.CotangentFlatBaseChange
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tor-independent diagonal cotangent comparison

Source: Stacks Project, Cotangent Complex, Tag 08R1 (`lemma-bootstrap`), first
sentence, invoking Tag 08QQ (`lemma-flat-base-change-cotangent-complex`)
(blueprint: lem-trf-cotangent-diagonal-tor-comparison).

The diagonal square below fixes the two factor maps. Its derived multiplication
is the canonical derived-to-ordinary tensor comparison with the second-factor
module action, and its cotangent base-change map extends along the first factor.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Algebra.CotangentResolution

/-- The diagonal base-change square: upper map `A → B`, lower map `ι₂ : B → B ⊗[A] B`,
left vertical map `A → B`, and right vertical map `ι₁ : B → B ⊗[A] B`.
The tensor balancing identity supplies its commutativity, with no flatness assumption.
Source: Stacks, Tags 08R1 and 08QQ
(blueprint: lem-trf-cotangent-diagonal-tor-comparison). -/
def cotangentDiagonalSquare (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Arrow.mk (CommRingCat.ofHom (algebraMap A B)) ⟶
      Arrow.mk (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom) :=
  Arrow.homMk (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B))
    (by
      apply CommRingCat.hom_ext
      change (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom.comp
          (algebraMap A B) =
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] B).comp (algebraMap A B)
      exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm)

/-- For a Tor-independent ring map, both the canonical derived self-tensor comparison
and the specified diagonal cotangent base-change morphism are isomorphisms. The
first morphism is in `D(B)` with `B` acting through `ι₂`; the second is in
`D(B ⊗[A] B)`, extends along `ι₁`, and targets the cotangent complex for `ι₂`.
Its definition is the extension-of-scalars adjunct of the standard square map.
Source: Stacks, Tag 08R1 (`lemma-bootstrap`), first sentence, and Tag 08QQ
(`lemma-flat-base-change-cotangent-complex`)
(blueprint: lem-trf-cotangent-diagonal-tor-comparison).

Proof:
1. Use the standard polynomial resolution of lem-trf-cotangent-resolution-coherence.
Its alternating complex C resolves B[0], has zero positive terms, and is termwise
free on monomials, hence flat, by lem-trf-polynomial-simplicial-tensor-model.
Apply lem-trf-flat-resolution-canonical-tensor-comparison to obtain the computation
isomorphism j from Q(C tensor_A B) to the universal derived scalar extension,
with gamma composed with j equal to Q(q tensor 1). The B-action is on the second factor.
2. Reindex C homologically. The negative cohomology of C tensor_A B is positive Tor
(def-weil-pbc-tor-modules), which vanishes by hypothesis. Positive cohomology is zero
since C is nonpositive. Right exactness (lem-weil-pbc-tensor-right-exact) identifies
H^0(q tensor 1) with the canonical cokernel isomorphism to B tensor_A B. Thus
q tensor 1 is a quasi-isomorphism. Localization (def-weil-abstract-derived-category)
makes its image invertible, so gamma is invertible by Step 1.
3. Apply lem-trf-cotangent-flat-base-change to cotangentDiagonalSquare A B.
Its derived multiplication is gamma: its ordinary tensor map sends b tensor b' to
(b tensor 1)(1 tensor b') = b tensor b'. Its lower map is ι₂ and right map is ι₁.
The theorem therefore makes precisely the adjunct cotangentBaseChange invertible.
No flatness hypothesis is used. -/
theorem isIso_diagonal_cotangent_comparisons
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (C : Coherence.{u}) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor' (ModuleCat.{u} A) i).obj
        (ModuleCat.of A B)).obj (ModuleCat.of A B))) :
    IsIso (derivedSquareMultiplication (cotangentDiagonalSquare A B)) ∧
      IsIso (cotangentBaseChange C (cotangentDiagonalSquare A B)) := by
  sorry

end Algebra.CotangentResolution
