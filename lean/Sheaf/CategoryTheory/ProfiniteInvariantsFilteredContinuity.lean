/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Sheaf.CategoryTheory.CondensedActionModule
public import Sheaf.Topology.ProfiniteCondensedRing
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.CategoryTheory.SiteFilteredColimitSections
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.CategoryTheory.CohomologyColimitSites
import WeilConjectures.CategoryTheory.ColimitSites
import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence

/-!
# Filtered continuity of internal profinite derived invariants

Source: Stacks Project, Tag 0739, lemma-colim-works-over-collection, specialized via
coherent profinite action spaces; Tags 072W and 0H7B for the sheafified comparison
(blueprint: lem-sfb-profinite-invariants-filtered-continuity).

The invariant functor fixes sections after every profinite base change. The comparison
is `colimit.post`, whose legs are the higher-invariant images of the original coprojections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.CondensedBar

namespace CategoryTheory.CondensedDerivedRestriction

/-- Higher internal invariants mean cohomology of ordinary total derived invariants on
modules placed in degree zero. The output is an internal A-module.
Source: Stacks 072W, ordinary higher direct images
(blueprint: lem-sfb-profinite-invariants-filtered-continuity). -/
def higherInvariants (A : CondensedBar.Ring.{u}) (J : Type u) [Group J]
    [TopologicalSpace J] [IsTopologicalGroup J] (q : ℕ) : Equivariant A J ⥤ Modules A :=
  (DerivedCategory.singleFunctor (Equivariant A J) 0 ⋙ derived A J) ⋙
    DerivedCategory.homologyFunctor (Modules A) (q : ℤ)

/-- Forgetting the action creates every compatible small filtered colimit.
Source: Stacks 0738 and 03CO, with the induced internal action
(blueprint: lem-sfb-profinite-invariants-filtered-continuity).
Proof: finite-cover profinite sheaf colimits are computed on sections by
lem-weil-pbc-site-filtered-colimit-sections-finite-coverings. By
lem-weil-pbc-module-sheaves-colimits-forgetful they carry the original module structure.
For g in C(S,J), set g[m_i]=[gm_i]. Equivariance of transition maps makes this
well-defined. Action laws, linearity and restriction compatibility hold on representatives.
The coprojections are equivariant. The unique underlying map from a colimit into any
other equivariant cocone commutes with g and all restrictions, again on representatives;
thus the underlying colimit lifts and the forgetful functor reflects its universal property.
-/
theorem forgetCreatesFilteredColimit (A : CondensedBar.Ring.{u}) (J : Type u)
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ Equivariant A J) :
    Nonempty (CreatesColimit N (CondensedBar.forgetAction (A := A) (G := J))) := by
  sorry

/-- All nonnegative higher internal invariants commute with filtered colimits, by the
canonical map induced by the original coprojections, without a cohomological bound.
Source: Stacks 0739, 09YP, 072W and 0H7B
(blueprint: lem-sfb-profinite-invariants-filtered-continuity).
Proof:
1. Construct the equivariant filtered colimit on sections as in
   forgetCreatesFilteredColimit, using finite-cover section continuity and module colimits.
2. Use lem-sfb-profinite-action-coherent-presentation to transport the diagram and its
   original colimit coprojections to module sheaves on the finite-cover action-space site.
   The objects tS and all covering fibre products are coherent in that site.
3. Apply lem-weil-pbc-cohomology-colimit-of-sites to the constant system of these sites
   over I.op. The forward-arrow category (i0 downarrow I) is final: filteredness gives
   common targets and equalizes parallel arrows. This identifies the comparison with
   colim_i H^q(tS,F_i) -> H^q(tS,colim_i F_i), with its original coefficient-map legs.
4. An equivariant injective resolution becomes a module-sheaf injective resolution under
   the exact action-site equivalence. Its underlying abelian terms are evaluation-acyclic
   by lem-sc-injective-module-abelian-acyclic-zariski. Enough injectives and
   lemma-weil-pbc-leray-acyclicity compute its evaluation cohomology. The single comparison
   map of sheaf complexes commutes with restrictions and is coefficient-natural by
   lem-sc-acyclic-comparison-natural. Exact sheafification therefore identifies higher
   internal invariants with the sheafification of S |-> H^q(tS,F).
5. Sheafify the presheaf isomorphism of step 3. Sheafification commutes with colimits;
   forgetting module structure creates the abelian colimit. The resulting arrow has
   legs R^q Gamma(N_i -> colim N_i) by naturality in step 4, hence is colimit.post.
   It is linear, and its inverse is linear since applying this injective linear map
   tests the scalar equation. No bound uniform in q enters this argument.
-/
theorem higherInvariants_filteredColimit_isIso
    (A : CondensedBar.Ring.{u}) (J : Type u)
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    [CompactSpace J] [T2Space J] [TotallyDisconnectedSpace J]
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I]
    (N : I ⥤ Equivariant A J) (q : ℕ) :
    IsIso (colimit.post N (higherInvariants A J q)) := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
