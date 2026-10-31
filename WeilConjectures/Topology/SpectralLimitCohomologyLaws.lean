/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Topology.SpectralLimitCohomologyMap

public import WeilConjectures.Topology.SpectralLimitCohomologyZeroLaws

import WeilConjectures.Topology.SpectralLimitCohomologyMapIdentity
import WeilConjectures.Topology.SpectralLimitCohomologyMapComposition
import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData

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

attribute [local irreducible] spectralLimitCohomologyMap

private theorem app_heq {X : TopCat.{u}}
    {A B : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : A ⟶ B)
    {U V : Opens X} (e : U = V) {s : A.obj (op U)} {t : A.obj (op V)}
    (h : HEq s t) : HEq ((φ.app (op U)).hom s) ((φ.app (op V)).hom t) := by
  subst V
  cases h
  rfl

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
  dsimp only
  let δ (i : I) :
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i) ⟶
      colimit P := (eP i).inv ≫ colimit.ι P i
  let leg (i : I) : F i ⟶ (pushforward AddCommGrpCat.{u} (p i)).obj (colimit P) :=
    (sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
      (F i) (colimit P) (δ i)
  constructor
  · intro i
    exact spectralLimitCohomologyMap_id (f i i le_rfl) (hfid i) (cf i i le_rfl)
      (hcf i i le_rfl) (α i i le_rfl) (hαid i) q
  · intro i j k hij hjk
    exact spectralLimitCohomologyMap_comp (f i j hij) (f j k hjk) (f i k (hij.trans hjk))
      (hfcomp i j k hij hjk) (cf i j hij) (cf j k hjk) (cf i k (hij.trans hjk))
      (hcf i j hij) (hcf j k hjk) (hcf i k (hij.trans hjk))
      (α i j hij) (α j k hjk) (α i k (hij.trans hjk)) (hαcomp i j k hij hjk) q
  · intro i j h
    refine spectralLimitCohomologyMap_comp (f i j h) (p j) (p i) (hpcomp i j h)
      (cf i j h) (cp j) (cp i) (hcf i j h) (hcp j) (hcp i) (α i j h)
      (leg j) (leg i) ?_ q
    intro U s
    have hu := hP i j h U s
    have e : (Opens.map (p i)).obj U =
        (Opens.map (p j)).obj ((Opens.map (f i j h)).obj U) := by
      change (Opens.map (p i)).obj U = (Opens.map (p j ≫ f i j h)).obj U
      rw [hpcomp]
    have hv := app_heq (δ j).hom e hu
    have hd : ((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom) ≫ δ j = δ i := by
      simp [δ, Category.assoc]
    have he := congrArg (fun τ ↦ (τ.hom.app (op ((Opens.map (p i)).obj U))).hom
      ((((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
        (F i)).hom.app (op U)).hom s)) hd
    have hi := (sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv_unit (f := δ i)
    have hj := (sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
      (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).homEquiv_unit (f := δ j)
    change HEq (((leg i).hom.app (op U)).hom s)
      (((leg j).hom.app (op ((Opens.map (f i j h)).obj U))).hom
        (((α i j h).hom.app (op U)).hom s))
    dsimp only [leg]
    rw [hi, hj]
    exact (heq_of_eq he.symm).trans hv

end TopCat.Sheaf
