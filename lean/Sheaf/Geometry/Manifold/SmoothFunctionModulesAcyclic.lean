/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Geometry.Manifold.SmoothDimensionStrata
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Sheaf.Topology.ClosedSectionNeighborhoodExtension
import Sheaf.Topology.SoftAbelianSheafAcyclic

/-!
# Acyclicity of arbitrary modules over smooth functions

Source: Demailly, Complex Analytic and Differential Geometry, IV §4,
Example (4.12), Theorem (4.15), Lemma (4.18), Corollary (4.19), pp.203–205
(blueprint: lem-sfb-smooth-function-modules-acyclic).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace SmoothDimensionStrata

/-- Every Hausdorff second-countable boundaryless smooth real manifold is paracompact,
and every unital module sheaf over its smooth complex functions has zero positive-degree
cohomology as an abelian sheaf. The dimension may vary between components.

Source: Demailly, IV §4, discussion after (4.4), Example (4.12), Theorem (4.15),
Lemma (4.18), Corollary (4.19), pp.203–205
(blueprint: lem-sfb-smooth-function-modules-acyclic).

Proof:
1. A small closed Euclidean ball in a chart is a compact neighborhood. Thus the space is
   locally compact. Apply lem-sfb-locally-compact-countable-paracompact to deduce
   sigma-compactness, paracompactness and normality from Hausdorffness and second countability.
2. Each dimension stratum is open and closed. On each stratum apply
   lem-sfb-smooth-separating-cutoff to disjoint closed sets, obtaining a smooth real
   function zero near the first and one near the second. Assemble on the disjoint open
   strata and regard the resulting smooth function as complex-valued.
3. For a closed set S and a section of the underlying abelian sheaf along S,
   lem-sfb-closed-section-neighborhood-extension extends it to a section t on an open U.
   Choose the preceding cutoff u zero near N minus U and one near S.
4. Multiply t by the restriction of u. It is zero on the overlap with a neighborhood
   W of N minus U, so glue it with zero on W. The resulting global section restricts
   to the original section on S since the module action is unital. Hence the underlying
   abelian sheaf is soft. This uses only the module and sheaf axioms of
   def-weil-sheaf-of-modules-category and def-weil-pbc-sites-and-cohomology.
5. Apply lem-sfb-soft-abelian-sheaf-acyclic. The result is zero cohomology in every
   positive degree, computed in abelian sheaves, with no rank or finiteness assumption.
-/
theorem paracompact_and_modules_acyclic
    (N : Type u) [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
    [D : SmoothDimensionStrata N] :
    ParacompactSpace N ∧
      ∀ (F : ringedSiteModules.{u} D.complexSheaf) (r : ℕ), 0 < r →
        Subsingleton (CategoryTheory.Sheaf.H'
          ((SheafOfModules.toSheaf D.complexSheaf).obj F) r (⊤ : Opens N)) := by
  sorry

end SmoothDimensionStrata
