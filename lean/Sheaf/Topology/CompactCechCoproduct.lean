/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Coproducts and finite compact Čech complexes

Source: Stacks Project, Cohomology, Tag 01FF, the comparison of Čech complexes;
the coproduct variant follows by writing a direct sum as the directed union of its
finite subsums (blueprint: lem-sc-compact-cech-cohomology-coproduct).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

/-- Čech cohomology on a finite family with compact chosen intersections preserves
an existing coproduct of abelian sheaves.

Source: Stacks Project, Cohomology, Tag 01FF, comparison of Čech complexes, with
coproducts expressed as directed colimits of finite subsums.
(blueprint: lem-sc-compact-cech-cohomology-coproduct).

Proof: the coproduct sheaf is the sheafification of the sectionwise direct sum.
On a compact open every section is locally represented by finite-support tuples.
Choose a finite subcover of those neighborhoods. The union of their supports is
finite. The coproduct projections give sections of each summand on the whole
open; only those finitely many projections are nonzero, as can be checked locally.
Their sum recovers the section. Conversely, a finite-support tuple mapping to zero
has all its components zero by the projections. Thus evaluation at every compact
chosen intersection identifies the sheaf coproduct with the direct sum of sections,
compatibly with all restrictions. The tuple index in each Čech degree is finite,
so products commute with direct sums. These identifications give an isomorphism
between the Čech complex of the coproduct and the degreewise direct sum of the
Čech complexes. Direct sums of abelian groups are exact (or apply exactness of
directed colimits to the finite subsums), hence homology commutes with that sum.
The comparison respects the coprojections and therefore preserves the colimit
cocone. Empty families give the zero complex; empty coproducts give the zero sheaf.
-/
theorem compact_siteCech_cohomology_preserves_coproduct
    {X : Type u} [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    {T : Type u} [Finite T] {U : TopologicalSpace.Opens X}
    {f : T → TopologicalSpace.Opens X} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom)
    (hcompact : ∀ (p : ℕ) (a : Fin (p + 1) → T),
      IsCompact ((S.W p a : TopologicalSpace.Opens X) : Set X))
    {I : Type w}
    (F : Discrete I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [HasColimit F] (p : ℕ) :
    PreservesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        S.cohomologyFunctor p) := by sorry

end CategoryTheory.Sheaf
