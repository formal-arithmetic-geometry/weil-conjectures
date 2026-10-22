/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.Opens
import WeilConjectures.CategoryTheory.SiteContinuousPushforwardSheaf
import Mathlib.Topology.Sheaves.Flasque
import WeilConjectures.Topology.Sheaves.CechFlasque

/-! # Čech vanishing from surjectivity onto unions of cover intersections

Source: Stacks Project, Cohomology of Sheaves, Tag 0A36, lemma-vanishing-ravi.
(blueprint: lem-sfb-cech-vanishing-surjective-unions)

The complex is the recorded general-site `SiteCechComplex`, specialized to the open site.
Any choice of its universal fibre products is allowed. The index, space, and coefficient
universes are independent. No finiteness or separation condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

/-- Surjectivity of sections onto every union of finite nonempty intersections of a fixed
open cover implies the vanishing of its positive Čech cohomology.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A36, lemma-vanishing-ravi.
(blueprint: lem-sfb-cech-vanishing-surjective-unions)

The set `S` is a family of finite nonempty subsets of `I`. Its union of intersections is
`W`; `hWU` names its inclusion into `U`, which follows from `hU`. Thus this inclusion is
not an additional restriction on `S`. In particular `S = ∅` gives `W = ⊥`.
`K.cohomologyFunctor` uses all ordered tuples, with repetitions, and the alternating
restriction differential. The universal-property data `K` merely choose the intersections.

Proof:
1. Let P be the space of nonempty subsets A of I, with basis B_J consisting of A containing
   the finite nonempty subset J. Then B_J ∩ B_L = B_(J ∪ L), and B_J ⊆ B_L iff L ⊆ J,
   by testing the point J. An open containing J contains B_J. Consequently B_J is contained
   in a union of opens iff it is contained in one member of the union.
2. Send an open Z of P to T(Z), the union of U_J over all J with B_J ⊆ Z. Then
   T(B_J) = U_J, T(∅) = ∅, and T(P) = U, including I empty.
3. T preserves arbitrary unions by step 1. It preserves binary intersections because
   U_J ∩ U_L = U_(J ∪ L) and B_(J ∪ L) = B_J ∩ B_L. Hence it preserves covers and
   their pullbacks along open inclusions.
4. By lem-weil-pbc-site-continuous-pushforward-sheaf, precomposition gives the abelian
   sheaf G(Z) = F(T(Z)) on P. No continuous map of underlying spaces is required.
5. For Z ⊆ Z', hres extends any section of G(Z) to F(U). Restricting this extension to
   T(Z') proves that G is flasque, by def-sc-zariski-flasque. This includes Z empty.
6. The B_{i} cover P. For every ordered tuple, their intersection B_J maps to the
   corresponding intersection U_J, where J is the set of tuple entries. The resulting
   identification of section products respects each omitted-entry restriction, and hence
   the alternating differential. Thus the two Čech complexes are canonically isomorphic;
   the universal properties of K identify its chosen fibre products with these opens.
7. Apply lem-sfb-flasque-open-cover-cech-acyclic (Stacks 09SZ) to G. Transport its vanishing
   across the complex isomorphism of step 6 to obtain the asserted cohomology vanishing.
-/
theorem isZero_siteCech_of_surjective_unions
    (Y : Type u) [TopologicalSpace Y]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w})
    {I : Type v} (V : I → Opens Y) (U : Opens Y) (hU : (⨆ i, V i) = U)
    (hres : ∀ (S : Set {J : Finset I // J.Nonempty}) (W : Opens Y),
      W = (⨆ J : S, J.val.val.inf' J.val.property V) →
      ∀ hWU : W ≤ U, Function.Surjective (F.obj.map (homOfLE hWU).op))
    (K : SiteCechComplex V (fun i ↦ homOfLE ((le_iSup V i).trans hU.le)))
    (p : ℕ) (hp : 0 < p) :
    IsZero ((K.cohomologyFunctor p).obj F.obj) := by
  sorry

end TopCat.Sheaf
