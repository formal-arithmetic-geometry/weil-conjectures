/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Finite-colimit comparisons for matrices and cokernels

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-proper-base-change-unbounded-pullback.proof.md, “Constructible complexes”,
local coefficient models on strata (blueprint: lem-sfb-finite-colimit-matrix-cokernels).

The comparison is constructed from coproduct comparisons, without assuming additivity.
Matrices use Mathlib's source-column, target-row convention; the supplied entries below
are indexed by target row first. Cokernels may be any colimiting cokernel coforks.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory Limits

-- Activate Mathlib's existing consequence of the abelian structure, without new data.
attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Functor

/-- The finite-coproduct comparison, transported from chosen coproducts to chosen
biproducts, followed by the biproduct of copies of the specified object isomorphism.
This is a construction also at rank zero, with no nonemptiness assumption.
Source: blueprint main-20261015, proper-base-change-unbounded pullback proof,
“Constructible complexes”; node proof step 2
(blueprint: lem-sfb-finite-colimit-matrix-cokernels). -/
noncomputable def finiteColimitBiproductIso
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (H : B ⥤ D) [PreservesFiniteColimits H] (X : B) (Y : D)
    (e : H.obj X ≅ Y) (r : ℕ) :
    H.obj (⨁ fun _ : Fin r ↦ X) ≅ (⨁ fun _ : Fin r ↦ Y) :=
  H.mapIso (biproduct.isoCoproduct (fun _ : Fin r ↦ X)) ≪≫
    PreservesCoproduct.iso H (fun _ : Fin r ↦ X) ≪≫
    (biproduct.isoCoproduct (fun _ : Fin r ↦ H.obj X)).symm ≪≫
    biproduct.mapIso (fun _ : Fin r ↦ e)

/-- A finite-colimit-preserving functor preserves zero maps, finite matrix squares,
and their cokernels, with the canonical injection, projection and cokernel equations.
The cokernel isomorphism is unique from its forward projection equation alone.
Source: blueprint main-20261015, proper-base-change-unbounded pullback proof,
“Constructible complexes”, local coefficient models on strata
(blueprint: lem-sfb-finite-colimit-matrix-cokernels).

Proof in words, following the eight steps of the node:
1. The right-exact case of Stacks 010N, implemented by
   rightExactFunctor_le_additiveFunctor (lem-sfb-preserving-colimits-additive), gives
   additivity. Apply cancellation to H(0) = H(0) + H(0) to obtain preservation of zero.
2. Both the image of the source finite coproduct and the target coproduct with legs
   e followed by the target injections are coproducts of copies of H(X). Uniqueness
   of colimits gives exactly finiteColimitBiproductIso and its injection equation.
   For rank zero these are initial objects and the equation family is empty.
3. Test the projection equation on each mapped injection. The biproduct relations
   reduce both sides to e on the matching summand and zero otherwise. Coproduct
   uniqueness gives the equation, with no projection to test in rank zero.
4. The map with entries p_ij is the sum over i,j of projection_j, p_ij, injection_i.
   Inserting the two biproduct identity sums proves uniqueness. This is precisely
   biproduct.matrix with its indices reversed. Empty sums handle either zero rank.
5. Test the asserted matrix square on every mapped input injection and every output
   projection. Steps 2 and 3 reduce it to the given entry equations. The product
   and coproduct universal properties then imply the square, including empty ranks.
6. A cokernel cofork is a coequalizer of the matrix and zero. The parallel-pair
   category is finite, so H preserves its colimit. Step 1 identifies the second
   mapped arrow with zero, making the mapped cokernel projection a cokernel.
7. The square makes E_n followed by the target cokernel projection kill H(p),
   hence gives a unique forward factorization. The inverse square likewise makes
   E_n inverse followed by the mapped source projection kill q, giving a backward
   factorization through the target cokernel.
8. Composing the two factorization equations gives identity on each cokernel
   projection. Uniqueness of cokernel factorization proves the two inverse laws.
   The forward equation alone determines the map and hence the isomorphism.
Only finite discrete and parallel-pair colimits are used; zero objects, zero ranks,
and the zero functor are included. -/
theorem finiteColimit_matrix_cokernels
    {B : Type u₁} [Category.{v₁} B] [Abelian B]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (H : B ⥤ D) [PreservesFiniteColimits H] (X : B) (Y : D)
    (e : H.obj X ≅ Y) :
    H.PreservesZeroMorphisms ∧
    (∀ (r : ℕ) (j : Fin r),
      H.map (biproduct.ι (fun _ : Fin r ↦ X) j) ≫
          (finiteColimitBiproductIso H X Y e r).hom =
        e.hom ≫ biproduct.ι (fun _ : Fin r ↦ Y) j) ∧
    (∀ (r : ℕ) (j : Fin r),
      (finiteColimitBiproductIso H X Y e r).hom ≫
          biproduct.π (fun _ : Fin r ↦ Y) j =
        H.map (biproduct.π (fun _ : Fin r ↦ X) j) ≫ e.hom) ∧
    (∀ (m n : ℕ) (p : Fin n → Fin m → (X ⟶ X))
        (q : Fin n → Fin m → (Y ⟶ Y)),
      (∀ (i : Fin n) (j : Fin m), H.map (p i j) ≫ e.hom = e.hom ≫ q i j) →
      (H.map (biproduct.matrix (fun j i ↦ p i j)) ≫
          (finiteColimitBiproductIso H X Y e n).hom =
        (finiteColimitBiproductIso H X Y e m).hom ≫
          biproduct.matrix (fun j i ↦ q i j)) ∧
      (∀ (cp : CokernelCofork (biproduct.matrix (fun j i ↦ p i j)))
          (cq : CokernelCofork (biproduct.matrix (fun j i ↦ q i j))),
        IsColimit cp → IsColimit cq →
        ∃ u : H.obj cp.pt ≅ cq.pt,
          H.map cp.π ≫ u.hom = (finiteColimitBiproductIso H X Y e n).hom ≫ cq.π ∧
          cq.π ≫ u.inv = (finiteColimitBiproductIso H X Y e n).inv ≫ H.map cp.π ∧
          ∀ u' : H.obj cp.pt ≅ cq.pt,
            H.map cp.π ≫ u'.hom = (finiteColimitBiproductIso H X Y e n).hom ≫ cq.π →
              u' = u)) := by
  sorry

end CategoryTheory.Functor
