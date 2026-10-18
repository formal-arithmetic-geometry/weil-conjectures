/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Topology.SpectralLimitCohomologyMap

public import Sheaf.Topology.SpectralLimitCohomologyZeroLaws

import Sheaf.Topology.SpectralLimitCohomologyDegreeZero
import Sheaf.CategoryTheory.SiteCohomologyPullbackComposite
import Sheaf.CategoryTheory.SiteCohomologyPullbackUnique

/-! # Functor and cocone laws for normalized cohomology maps

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-laws)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

/-- Normalized cohomology maps satisfy the diagram and cocone laws.
No limit-space or compactness hypothesis is required.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F7, 01F8 and 0A37.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-laws)

Proof: the degree-zero normalization identifies each map with the corresponding
f-map on global sections. The adjunction triangle identities identify the transpose
of a pullback-and-coprojection with its unit formula. The sectionwise identity and
composition hypotheses therefore give the three equations in degree zero. For a
positive degree, embed the coefficient sheaf into an injective and use the surjective
Yoneda boundary of its cokernel sequence. Exact inverse image makes the pulled-back
sequence short exact. Compatibility of normalized pullback with this boundary,
ordinary naturality in the coefficient arrow, and naturality of restriction in the
open set transfer the degree-zero equations by induction. For the third equation,
hP and the naturality of the colimit coprojections give the needed equality on unit
sections; adjunction makes that equality one of coefficient morphisms. -/
theorem spectralLimit_cohomology_laws
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u})
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (hfid : ∀ i : I, f i i le_rfl = 𝟙 (S i))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (X : TopCat.{u}) (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
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
    (cf : ∀ (i j : I) (h : i ≤ j),
      SiteCohomologyFamily (Opens.grothendieckTopology (S i))
        (Opens.grothendieckTopology (S j)) (Opens.map (f i j h)))
    (hcf : ∀ (i j : I) (h : i ≤ j),
      @SiteCohomologyFamily.IsPullback _ _ _ _ (Opens.grothendieckTopology (S i))
        (Opens.grothendieckTopology (S j)) (Opens.map (f i j h)) inferInstance
        (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
          (sheafAdjunctionContinuous (Opens.map (f i j h)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology (S j)))
          (Functor.additive_of_preserves_binary_products _))
        inferInstance inferInstance (cf i j h))
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
    (q : ℕ) :
    let a := fun (i j : I) (h : i ≤ j) ↦
      spectralLimitCohomologyMap (f i j h) (cf i j h) (α i j h) q
    let b := fun i : I ↦ spectralLimitCohomologyMap (p i) (cp i)
      ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
          (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q
    CohomologyMapLaws a b := by
  sorry

end TopCat.Sheaf
