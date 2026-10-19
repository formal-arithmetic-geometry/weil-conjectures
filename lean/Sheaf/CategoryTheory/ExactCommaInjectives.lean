/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Comma
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Injectives in the comma category of an exact left adjoint

Source: the auxiliary exact-comma construction for ILO XVI, printed p.248, relative
cohomology paragraph; Stacks Project, Homology, Tag 015Z, for the adjoint/injective
ingredient (blueprint: lem-per-exact-comma-injectives).

The category of triples is Mathlib's `Comma L (𝟭 B)`, with its componentwise
preadditive structure. Exactness is expressed by preservation of finite limits and
finite colimits, equivalently preservation of short exact sequences for additive
functors between abelian categories (`Functor.exact_tfae`). Preservation by both
projections also expresses that kernels and cokernels are computed componentwise.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/-- The graph functor `P ↦ (P, LP, 𝟙)` into the actual comma category, with
`a ↦ (a, L.map a)`. Source: the exact-comma auxiliary construction for ILO XVI,
printed p.248 (blueprint: lem-per-exact-comma-injectives). -/
def exactCommaGraph (L : A ⥤ B) : A ⥤ Comma L (𝟭 B) where
  obj P := ⟨P, L.obj P, 𝟙 (L.obj P)⟩
  map a := { left := a, right := L.map a }

/-- The comma category of an additive exact left adjoint is abelian with its
componentwise addition, has componentwise kernels and cokernels and enough
injectives, and its two evaluations are exact and preserve injectives. The graph
functor is additive and exact. Source: auxiliary construction for ILO XVI, printed
p.248, and Stacks Project, Homology, Tags 0106, 0109 and 015Z
(blueprint: lem-per-exact-comma-injectives).

Proof plan, following the nine steps of the node:
1. Comma morphisms form additive subgroups of pairs of morphisms. The zero triple
is zero, and componentwise biproducts, with structure map given by the sum of the
two inclusions composed with the structure maps and images of projections, give
finite biproducts (`def-sp-abelian`).
2. For `(a,b)`, take the kernels of `a` and `b`; the induced structure map into
the second kernel exists because the comma square vanishes after `b`. Factor
maps in both components and cancel the second kernel inclusion to check that
the factorization is a comma morphism (`def-sp-abelian`).
3. Take the two cokernels. The adjunction makes `L` preserve the first cokernel
(`lem-weil-pbc-left-adjoint-preserves-colimits`). Its universal property gives
the structure map; cancel the epic image of the first cokernel projection to
verify the comma relation for factorizations.
4. A triple is zero precisely when both components are zero. The kernel and
cokernel tests therefore make monomorphisms and epimorphisms componentwise.
5. In an abelian component category a mono is the kernel of its cokernel and an
epi the cokernel of its kernel. The componentwise constructions give these
properties for triples, verifying the abelian axioms (`def-sp-abelian`).
6. Short exactness is componentwise. Thus both evaluations are exact, and the
graph functor is additive and exact because `L` is exact. The zero-section
`Z(N) = (0,N,0)` is additive and exact as well.
7. The evident natural Hom bijections give graph left adjoint to evaluation
zero, and zero-section left adjoint to evaluation one. Their exactness and
`lem-sp-right-adjoint-preserves-injectives` give injective evaluations.
8. Evaluation zero has right adjoint `I ↦ (I,0,0)`. Evaluation one has right
adjoint `J ↦ (RJ,J,ε_J)`; its Hom bijection uses the adjoint transpose of the
structure map followed by a map to `J`. These right adjoints take injectives
to injectives by the same adjoint-preservation lemma.
9. Choose embeddings `P ↪ I` and `N ↪ J` into injectives
(`def-sp-enough-injectives`, `def-sp-injective-resolutions`). Pair the induced
maps to `(I,0,0)` and `(RJ,J,ε_J)`. The first component is mono since its
projection to `I` is the chosen embedding, and the second is the embedding
into `J`. The target biproduct is injective by separately extending its two
components across any mono. This proves enough injectives. -/
theorem exactComma_injectives [Abelian A] [Abelian B]
    [EnoughInjectives A] [EnoughInjectives B]
    (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (R : B ⥤ A) [R.Additive] (adj : L ⊣ R) :
    ∃ h : Abelian (Comma L (𝟭 B)),
      h.toPreadditive = instPreadditiveComma L (𝟭 B) ∧
      EnoughInjectives (Comma L (𝟭 B)) ∧
      PreservesFiniteLimits (Comma.fst L (𝟭 B)) ∧
      PreservesFiniteColimits (Comma.fst L (𝟭 B)) ∧
      PreservesFiniteLimits (Comma.snd L (𝟭 B)) ∧
      PreservesFiniteColimits (Comma.snd L (𝟭 B)) ∧
      (Comma.fst L (𝟭 B)).PreservesInjectiveObjects ∧
      (Comma.snd L (𝟭 B)).PreservesInjectiveObjects ∧
      (exactCommaGraph L).Additive ∧
      PreservesFiniteLimits (exactCommaGraph L) ∧
      PreservesFiniteColimits (exactCommaGraph L) := by
  sorry

end CategoryTheory
