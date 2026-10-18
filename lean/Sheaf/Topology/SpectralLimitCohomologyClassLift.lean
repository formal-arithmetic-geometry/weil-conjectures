/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Topology.SpectralLimitCohomologyMap

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Topology.Sheaves.Functors
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Topology.SpectralDirectedLimit
import Sheaf.Topology.SpectralLimitDescendOpens
import Sheaf.Topology.SpectralLimitSheafSections
import Sheaf.Topology.SpectralLimitCohomologyDegreeZero
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion
import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
import WeilConjectures.Topology.Sheaves.Cech
import WeilConjectures.Topology.Sheaves.PushforwardCohomology

/-! # ClassLift

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-class-lift)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Every class of the limit sheaf is the canonical image of a class at a stage.
This is the generation half of continuity and asserts no detection of relations.

Proof: induct on the degree simultaneously for all compatible systems. In degree
zero use the spectral-limit sections comparison over the terminal compact open;
upper-tail inclusion is cofinal. For the successor step embed the system in the
compatible products of pushforwards of injectives from Tag 0A37 and form its
cokernel system. Exact inverse image and exact filtered sheaf colimits give the
short exact sequence on the limit. Every finite compact-open cover descends to a
stage. Sections comparison identifies its Cech complex for the limit of the
injectives with the filtered colimit of the stage Cech complexes: each degree has
finitely many factors. Injective Cech exactness and exact filtered colimits,
followed by the Cech criterion, make the middle limit sheaf positively acyclic.
Thus the target connecting map onto the successor cohomology is surjective.
Lift a class through that connecting map, then apply the lower-degree generation
assertion to the quotient system. The normalized pullback boundary identity and
coefficient naturality identify its stage boundary with the original class.

The compatible embedding used above is explicit: choose monomorphisms
F_k → A_k into injectives, and put G_i = ∏_{k≥i} (f_ik)_* A_k.
The k-component of F_i → G_i is α_ik followed by the pushed-forward embedding.
Its i-component is the chosen monomorphism, so it is monic. The transition from
i to j discards the coordinates with k not ≥ j and uses f_ik = f_ij f_jk on
the retained coordinates. The cocycle equations for α give compatibility of
these embeddings. Continuous direct image preserves injectives because inverse
image is exact, and products of injectives are injective. Cokernels give the
quotient system; exact inverse image and exact filtered colimits of sheaves give
the short exact sequence on X. To justify the asserted positive acyclicity,
compact opens pulled back from stages form a basis closed under intersections.
Every finite compact-open covering descends, with its covering equality, to one
stage. On this cover, sections comparison identifies each term and differential
of the limit Čech complex with the filtered colimit of the stage complexes.
Only finitely many factors occur in any fixed degree, so common upper indices
represent all their sections and detect their relations. Injective Čech
exactness and exact filtered colimits give positive Čech acyclicity. The basis
Čech criterion then gives positive sheaf-cohomology acyclicity on X.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-class-lift) -/
theorem spectralLimit_cohomology_class_lift
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ i : I, f i i le_rfl = 𝟙 (S i))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (X : TopCat.{u}) [SpectralSpace X] (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : X.str = ⨅ i : I, TopologicalSpace.induced (p i) (S i).str)
    (F : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u})
    (α : ∀ (i j : I) (h : i ≤ j),
      F i ⟶ (pushforward AddCommGrpCat.{u} (f i j h)).obj (F j))
    (hαid : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i i le_rfl).hom.app (op U) s) s)
    (hαcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
        ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
          ((α i j hij).hom.app (op U) s)))
    (P : I ⥤ X.Sheaf AddCommGrpCat.{u}) [HasColimit P]
    (eP : ∀ i : I, P.obj i ≅
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i))
    (hP : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
          (op ((Opens.map (p i)).obj U))
        (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
            (F i)).hom.app (op U) s))
        (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
            (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
              ((α i j h).hom.app (op U) s)))
    (cp : ∀ i : I, SiteCohomologyFamily (Opens.grothendieckTopology (S i))
      (Opens.grothendieckTopology X) (Opens.map (p i)))
    (hcp : ∀ i : I, @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)
        (Opens.map (p i)) inferInstance
        (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
          (sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X))
          (Functor.additive_of_preserves_binary_products _))
        inferInstance inferInstance (cp i))
    (q : ℕ) (y : CategoryTheory.Sheaf.H' (colimit P) q ⊤) :
    ∃ (i : I) (x : CategoryTheory.Sheaf.H' (F i) q ⊤),
      (spectralLimitCohomologyMap (p i) (cp i)
      ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
          (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q).hom x = y := by
  sorry

end TopCat.Sheaf
