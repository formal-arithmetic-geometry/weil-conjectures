/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Topology.Bases
public import Mathlib.Topology.QuasiSeparated
public import Sheaf.Topology.OpenModuleCohomology
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis
import Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings
import Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.SiteCechComplex
import Sheaf.Paper.PQFCohomology
import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.Topology.SheavesDirectedColimitSections

/-! # Directed colimits and module cohomology on quasi-compact opens

Source: Stacks Project, Cohomology, Lemma 20.19.1, Tag 01FF
(blueprint: lem-weil-pbc-qs-scheme-cohomology-directed-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- On a scheme with a basis of quasi-compact opens stable under binary intersection,
every cohomology class on a quasi-compact open comes from a stage of a directed system,
and a stage class with zero image vanishes at a later stage. Equivalently, the canonical
map from the directed colimit of cohomology groups is bijective.

Source: Stacks Project, Cohomology, Lemma 20.19.1, Tag 01FF
(blueprint: lem-weil-pbc-qs-scheme-cohomology-directed-colimit).

Proof (the node's ten steps):
1. Use pqf-def-cohomology and the right-derived universal delta-functor lemma for the
long exact sequence. Module open restriction is exact, preserves injectives and colimits
(lem-weil-pbc-module-open-restriction-injectives and
lem-weil-pbc-module-restriction-open-immersion-colimits). Thus degree zero is sections,
and injective modules have no positive cohomology on opens.
2. Binary compact intersections give all finite nonempty compact intersections. The basis
and quasi-compactness give finite compact refinements of open covers, including the empty
cover for the empty open (Stacks 0069).
3. Apply lem-weil-pbc-module-directed-colimit-underlying-sets and
lem-weil-pbc-sheaves-directed-colimit-sections to obtain both elementwise assertions for
sections, hence in degree zero by the natural degree-zero identification.
4. Use lem-weil-pbc-scheme-modules-functorial-injective-embeddings to embed the system
functorially into injectives. Cokernels give a system of short exact sequences.
5. Take colimits of the injective and cokernel systems using
lem-weil-pbc-scheme-modules-coproduct-finite-subsums. Universal properties produce the
maps from the original colimit and between these two colimits, with composite zero.
6. Check exactness of this sequence on stalks using lem-weil-pbc-module-stalk-exact,
lem-weil-pbc-module-stalk-filtered-colimit, the filtered-colimit elementwise criterion,
and lem-weil-pbc-filtered-colimit-abelian-groups-exact.
7. The colimit of the injective system is acyclic on every quasi-compact open: finite
Cech terms commute with the colimit by step 3 and directedness; injective Cech complexes
are acyclic by lem-weil-pbc-module-injective-open-cover-cech-acyclic. Exactness of filtered
colimits preserves this acyclicity, and lem-weil-pbc-module-cech-vanishing-basis applies.
8. Compare the long exact sequences of the stage and colimit short exact sequences.
Naturality gives the comparison squares and step 7 gives the terminal zeros.
9. Assuming both assertions in degree n, lift a degree n+1 class through the surjective
connecting map and then from a cokernel stage, proving surjectivity. For a stage class
with zero image, lift through its connecting map; its colimit lift comes from the
injective colimit. Represent that element at a common stage, subtract its cokernel image,
and kill the resulting zero-image degree n class at a later stage by the induction
hypothesis. Exactness then kills the original degree n+1 class at that stage.
10. Induct from step 3 using step 9. The elementwise description of directed colimits of
abelian groups identifies these assertions with bijectivity of the canonical map. -/
theorem openModuleCohomology_directedColimit (X : Scheme.{u})
    (hBasis : IsTopologicalBasis {V : Set X | IsOpen V ∧ IsCompact V})
    [QuasiSeparatedSpace X]
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : I ⥤ SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (c : Cocone D) (hc : IsColimit c) (U : Opens X) (hU : IsCompact (U : Set X))
    (q : ℕ) :
    (∀ x : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj c.pt,
      ∃ (i : I) (y : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj (D.obj i)),
        ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map (c.ι.app i)).hom y = x) ∧
    (∀ (i : I) (y : (RingedSpace.openModuleCohomology X.toRingedSpace q U).obj (D.obj i)),
      ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map (c.ι.app i)).hom y = 0 →
      ∃ (j : I) (hij : i ≤ j),
        ((RingedSpace.openModuleCohomology X.toRingedSpace q U).map
          (D.map (homOfLE hij))).hom y = 0) := by
  sorry

end AlgebraicGeometry
