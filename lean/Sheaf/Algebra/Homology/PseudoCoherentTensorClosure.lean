/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import WeilConjectures.RingTheory.MPseudoCoherent
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.Algebra.Homology.BoundedFlatReplacement
import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Tensor closure of pseudo-coherent complexes over a ring

Source: Stacks Project, More on Algebra, Tag 0DJE, lemma-tensor-pseudo-coherent,
clauses (1) and (2) (blueprint: lem-trf-pseudocoherent-tensor-closure).

The tensor `K ⊗ L` is the existing K-flat derived monoidal tensor on `D(R)`.
`ModuleCat.hasFunctorialFlatResolution` and `DerivedCategory.hasDerivedMonoidalCategory`
supply this structure without an additional hypothesis. On a K-flat representative `P`
of `K` and any representative `N` of `L`, it is represented by
`Q.obj (CochainComplex.mapBifunctor P N (MonoidalCategory.curriedTensor _))`.
This is the direct-sum total complex with differential `d_P ⊗ 1 + (-1)^p 1 ⊗ d_N`;
K-flatness is the recorded `MorphismProperty.kFlat` for quasi-isomorphisms.

## Main statements

* `DerivedCategory.isMPseudoCoherent_tensor`: the finite-stage bound `max (m + a) (n + b)`.
* `DerivedCategory.isPseudoCoherent_tensor`: tensor closure without a finite-stage bound.
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- Tensoring an `n`-pseudo-coherent object supported in degrees at most `a` with an
`m`-pseudo-coherent object supported in degrees at most `b` gives a
`max (m + a) (n + b)`-pseudo-coherent object.

Source: Stacks Project, Tag 0DJE, lemma-tensor-pseudo-coherent, clause (1)
(blueprint: lem-trf-pseudocoherent-tensor-closure).

Proof plan, expanding the source's omitted approximation comparison:
1. For objects supported above by `c,d`, good truncations (def-kun-truncations) and
   lem-pc-kflat-bounded-flat-replacement on the one-point site give flat models with
   the same term bounds. They are K-flat by lem-pc-module-bounded-flat-kflat.
   Their total tensor has no terms above `c+d`, hence no cohomology there.
2. Put `t = max (m+a) (n+b)`. If `n>a` or `m>b`, step 1 gives vanishing in
   degrees at least `t`. The zero finite-free complex witnesses `t`-pseudo-coherence.
   Otherwise `n ≤ a` and `m ≤ b`.
3. Choose bounded finite-free approximations `P → K`, `Q → L` from
   def-pc-ring-m-pseudo-coherent. Their cones have zero cohomology in degrees
   at least `n,m`, respectively, by lem-sf-derived-homology-long-exact.
   Also `Q` has cohomology zero above `b`.
4. Tensor the first cone triangle with `Q`, and the second with `K`, using
   lem-pc-derived-tensor-second-factor-functor. The signed flip on terms of degrees
   `p,q` is multiplication by `(-1)^(pq)` followed by exchange of factors; it is
   a natural chain involution, so also identifies the factor orders after localization.
   Step 1 bounds the two tensor cones above by `n-1+b` and `a+m-1`.
5. Both cones therefore vanish in degrees at least `t`. Their long exact sequences
   (lem-sf-derived-homology-long-exact) show that the two comparison maps, and hence
   their composite, induce isomorphisms above `t` and a surjection at `t`.
6. Finite-free modules are flat by choosing a finite basis. The bounded complexes
   `P,Q` are K-flat (lem-pc-module-bounded-flat-kflat), so their total tensor represents
   their derived tensor (lem-pc-derived-tensor-second-factor-functor). Its terms have
   finite bases given by the finite union, over `p+q=k`, of products of the two bases.
   It is bounded. Step 5 therefore gives the required bounded finite-free witness. -/
theorem isMPseudoCoherent_tensor
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : DerivedCategory (ModuleCat.{u} R)) (n m a b : ℤ)
    (hK : IsMPseudoCoherent n K)
    (hKa : ∀ i : ℤ, a < i → IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj K))
    (hL : IsMPseudoCoherent m L)
    (hLb : ∀ j : ℤ, b < j → IsZero ((homologyFunctor (ModuleCat.{u} R) j).obj L)) :
    IsMPseudoCoherent (max (m + a) (n + b)) (K ⊗ L) := by
  sorry

/-- The derived tensor of two pseudo-coherent objects is pseudo-coherent.

Source: Stacks Project, Tag 0DJE, lemma-tensor-pseudo-coherent, clause (2), and
Tag 064P, definition-pseudo-coherent, clause (2)
(blueprint: lem-trf-pseudocoherent-tensor-closure).

Proof, step 7 of the node: choose bounded-above finite-free models `F,G`, with
upper term bounds `c,d`, using def-pc-ring-pseudo-coherent-complex. Finite-free
modules are flat by the finite-basis argument, so these complexes are K-flat by
lem-pc-module-bounded-flat-kflat. Their direct-sum total tensor represents the
derived tensor by lem-pc-derived-tensor-second-factor-functor. In degree `k`,
nonzero summands have `k-d ≤ p ≤ c`, `q=k-p`; there are finitely many and each has
the finite tensor-product basis. The total tensor is finite free in each degree
and zero above `c+d`. It is thus the bounded-above finite-free representative
required by def-pc-ring-pseudo-coherent-complex. -/
theorem isPseudoCoherent_tensor
    (R : Type u) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K L : DerivedCategory (ModuleCat.{u} R))
    (hK : IsPseudoCoherent K) (hL : IsPseudoCoherent L) :
    IsPseudoCoherent (K ⊗ L) := by
  sorry

end DerivedCategory
