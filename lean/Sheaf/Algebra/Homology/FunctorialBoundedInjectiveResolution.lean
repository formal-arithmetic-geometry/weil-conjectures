/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.CategoryTheory.DoubleComplexTotal
import Sheaf.Algebra.Homology.FirstQuadrantAugmentation
import Sheaf.Algebra.Homology.FunctorialObjectResolution

/-!
# Functorial injective resolutions preserving every lower bound

Source: Stacks Project, Derived Categories, Tag 0141, assertion (1) and its construction
(blueprint: lem-weil-pbc-functorial-bounded-injective-resolution).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CochainComplex

/-- Totalize a supplied functorial objectwise injective resolution.

Source: Stacks Project, Derived Categories, Tag 0141, assertion (1) and its construction.
(blueprint: lem-weil-pbc-functorial-bounded-injective-resolution-totalization).

Apply the supplied nonnegative augmented resolutions termwise to an integer-indexed
bounded-below complex, form the first-quadrant bicomplex, and take finite diagonal
biproducts with the signed total differential.  The first-quadrant column augmentation
criterion proves the augmentation is a quasi-isomorphism after choosing a lower bound only
for verification.  Finite biproducts of injectives give injective total terms, and the
vanishing of all columns below the chosen bound gives preservation of every lower bound.
-/
theorem exists_functorial_bounded_injective_resolution_of_object_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : C ⥤ CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C) ⟶ E)
    (hε : ∀ A : C, QuasiIso (ε.app A))
    (hEzero : ∀ (A B : C), E.map (0 : A ⟶ B) = 0)
    (hEobjzero : IsZero (E.obj (0 : C)))
    (hE : ∀ (A : C) (n : ℕ), Injective ((E.obj A).X n)) :
    ∃ (I : Plus C ⥤ Plus C) (α : Plus.ι C ⟶ I ⋙ Plus.ι C),
      (∀ K : Plus C, QuasiIso (α.app K)) ∧
      (∀ (K : Plus C) (n : ℤ), Injective (((I.obj K).obj).X n)) ∧
      (∀ (K : Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
        (I.obj K).obj.IsStrictlyGE a) := by
  sorry

/-- A functorial injective embedding gives one injective replacement functor on all
bounded-below complexes, preserving every termwise lower bound simultaneously.
Source: Stacks Project, `derived.tex`, Tag 0141, assertion (1) and its construction
(blueprint: lem-weil-pbc-functorial-bounded-injective-resolution).

Proof:
1. Normalize J by replacing J(A) with the kernel of J(A) → J(0). The maps induced by
   A → 0 → A split off J(0); the complementary projection retracts J(A) onto this
   kernel. Naturality factors the given monomorphism through that kernel. Kernel
   uniqueness defines the normalized functor and its natural monomorphic embedding.
2. A retract of an injective is injective: extend after inclusion into J(A), then
   project back. The normalized functor sends zero objects and zero morphisms to zero.
3. Fix kernels and cokernels. Starting with Q₀ = id, set E_q = J₀ Q_q and let Q_{q+1}
   be the cokernel of Q_q → E_q. Cokernel uniqueness defines maps functorially.
   Inductively these functors preserve zero objects and zero morphisms. The quotient
   followed by the next embedding gives natural differentials E_q → E_{q+1}.
4. Each augmented column 0 → A → E₀(A) → E₁(A) → ⋯ is exact: the embeddings are
   monic, the quotient maps epic, and their kernel-image identities give exactness.
   Every E_q(A) is injective (`def-sp-injective-resolutions`).
5. Form D_K^{q,p} = E_q(K.X p) for q ≥ 0, and zero for q < 0. Its differentials
   commute by naturality, square to zero, and give a bicomplex functorial in K.
   The column augmentations give a natural augmentation. Every lower bound a of K
   also bounds its p-index, because the E_q preserve zero objects.
6. Totalize with differential v + (-1)^q E_q(d_K), using
   `def-sp-double-complex-total`. Each diagonal has only finitely many nonzero terms
   for bounded-below K, so finite biproducts supply a coproduct of its entire diagonal.
   Choose these coproducts independently of any bound. Their universal properties
   define the maps on morphisms, respecting identities and composition. The mixed
   terms in the squared differential cancel. Naturality of v and functoriality of
   E_q prove the chain-map equation on each coprojection. The (0,n) inclusions after
   the embeddings give a chain map K → I(K), natural by the same equations.
7. For verification only, choose a bound a and reindex p = a+r. Apply
   `lem-sc-first-quadrant-column-augmentation` to the first-quadrant bicomplex:
   its augmented columns are resolutions by step 4. The diagonal bijection identifies
   its total with I(K) in degrees a+m, respecting signs and augmentation. This proves
   quasi-isomorphism above a; below a both complexes and their cohomology are zero.
8. Each total term is a finite biproduct of injectives, hence injective by extending
   each component along a monomorphism. The empty biproduct is zero and injective.
   No diagonal in degree n < a has q ≥ 0 and p ≥ a, so I(K) vanishes there.
   The construction preceded the choice of a and is natural for every chain map.
   Postcomposition therefore resolves any diagram, even without a common bound. -/
theorem exists_functorial_bounded_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (I : Plus C ⥤ Plus C) (α : Plus.ι C ⟶ I ⋙ Plus.ι C),
      (∀ K : Plus C, QuasiIso (α.app K)) ∧
      (∀ (K : Plus C) (n : ℤ), Injective (((I.obj K).obj).X n)) ∧
      (∀ (K : Plus C) (a : ℤ), K.obj.IsStrictlyGE a → (I.obj K).obj.IsStrictlyGE a) := by
  obtain ⟨E, ε, hε, hEzero, hEobjzero, hE⟩ :=
    exists_functorial_object_injective_resolution J η hη hJ
  exact exists_functorial_bounded_injective_resolution_of_object_resolution E ε hε hEzero
    hEobjzero hE

end CochainComplex
