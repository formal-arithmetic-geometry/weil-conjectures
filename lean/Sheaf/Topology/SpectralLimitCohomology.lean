/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Topology.Sheaves.Cech
import WeilConjectures.Topology.Sheaves.PushforwardCohomology
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.CategoryTheory.SiteCechVanishingCriterion
import Sheaf.Topology.SpectralDirectedLimit
import Sheaf.Topology.SpectralLimitDescendOpens
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Topology.SpectralLimitSheafSections
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.SiteCechVanishingCriterion

/-!
# Cohomological continuity on directed spectral limits

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, `lemma-colimit`, final sentence
(blueprint: lem-weil-pbc-spectral-limit-cohomology).

## Main definitions

* `TopCat.Sheaf.spectralLimitCohomologyMap`: the canonical map associated to an `f`-map.

## Main statements

* `TopCat.Sheaf.spectralLimit_cohomology`: the canonical colimit comparison is invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace TopCat.Sheaf

/-- The cohomology map of an `f`-map, computed by pullback followed by its adjoint.
The final restriction identifies the inverse image of the terminal open with the terminal
open. The family `c` is normalized by `SiteCohomologyFamily.IsPullback` in the theorem below.
Source: Stacks Project, Cohomology of Sheaves, Tags 01F7 and 0A37
(blueprint: lem-weil-pbc-spectral-limit-cohomology). -/
noncomputable def spectralLimitCohomologyMap {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : SiteCohomologyFamily (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) (Opens.map f))
    {F : Y.Sheaf AddCommGrpCat.{u}} {G : X.Sheaf AddCommGrpCat.{u}}
    (α : F ⟶ (pushforward AddCommGrpCat.{u} f).obj G) (q : ℕ) :
    CategoryTheory.Sheaf.H' F q ⊤ ⟶ CategoryTheory.Sheaf.H' G q ⊤ :=
  c q ⊤ F ≫
    (((CategoryTheory.Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) q).map
      ((sheafAdjunctionContinuous (Opens.map f) AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).homEquiv F G |>.symm α))).app
      (op ((Opens.map f).obj ⊤)) ≫
    (CategoryTheory.Sheaf.cohomologyPresheaf G q).map
      (eqToHom (congrArg op (Opens.map_top f)))


/-- Cohomology of a compatible abelian-sheaf system on a directed spectral inverse limit
is the filtered colimit of its stage cohomology, with the canonical comparison map.
`P` and `eP` present the diagram of inverse images; `hP` specifies its arrows on unit
sections, hence specifies them uniquely by adjunction. `H` and `eH` present the diagram
of stage cohomology, whose existence is asserted. `c` and `ec` present its canonical
cocone to the cohomology of the colimit sheaf, also asserted to exist. The conclusion asserts
invertibility of the stipulated comparison,
independently of all choices of presentations or normalized pullback families.
Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, `lemma-colimit`
(blueprint: lem-weil-pbc-spectral-limit-cohomology).

Proof outline:
1. The spectral inverse-limit theorem makes the projections spectral. Compact opens
   pulled back from stages form a basis, by directedness and finite intersections.
   The open-descent lemma descends compact opens, inclusions and finite covering equalities
   (`lem-weil-pbc-spectral-directed-limit-spectral`,
   `lem-weil-pbc-spectral-limit-descend-opens`).
2. The spectral-limit sheaf-sections lemma identifies sections over every such basis open
   with their filtered colimit, by the canonical pullback-and-coprojection maps
   (`lem-weil-pbc-spectral-limit-sheaf-sections`).
3. Choose embeddings F_i into injectives A_i on the full open-set sites. The sheaves
   G_i(V) = product over k >= i of A_k(f_ik inverse V) are injective: continuous
   pushforward preserves injectives and products of injectives are injective
   (`lem-weil-pbc-site-sheaves-enough-injectives`, `lem-sc-topological-pushforward-injective`,
   `lem-weil-pbc-product-injectives`).
4. The maps F_i -> G_i have components e_k alpha_ik; their i-components are monic.
   Discarding coordinates gives compatible transition maps on G_i, and compatibility
   with F_i follows coordinatewise from the cocycle law
   (`def-weil-pbc-topological-inverse-image`).
5. Form Q_i = coker(F_i -> G_i). Exact inverse image and exact filtered colimits give
   0 -> F -> G -> Q -> 0 on X, where G and Q are the corresponding colimit sheaves
   (`lem-sc-topological-pushforward-injective`,
   `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`).
6. Every finite covering of a compact basis open descends to one stage. Step 2 identifies
   its Cech complex for G with the filtered colimit of the stage Cech complexes for G_i.
   Finite products commute with filtered colimits, so this identification respects all
   differentials. Injective Cech exactness and exact filtered colimits imply positive
   Cech vanishing. The site Cech-vanishing criterion gives H^p(X,G)=0 for p>0
   (`lem-pc-topological-injective-cech-positive-exact`,
   `lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
   `lem-weil-pbc-site-cech-vanishing-criterion`).
7. Induct on q for all compatible systems. Degree zero is step 2. For q=1 compare the
   cokernels of H^0(G)->H^0(Q); for q>1 use dimension shifting and induction for Q_i.
   Pullback commutes with connecting maps by its normalized delta-functor description;
   ordinary cohomological naturality handles the sheaf arrows. The resulting isomorphism
   is therefore precisely the canonical comparison asserted here
   (`lem-weil-pbc-derived-functor-long-exact`,
   `lem-weil-pbc-derived-functor-injective-vanishing`,
   `lem-weil-pbc-right-derived-universal-delta-functor`). -/
theorem spectralLimit_cohomology
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
    ∃ (H : I ⥤ AddCommGrpCat.{u})
      (eH : ∀ i : I, H.obj i ≅ CategoryTheory.Sheaf.H' (F i) q ⊤),
      (∀ (i j : I) (h : i ≤ j),
        (eH i).inv ≫ H.map (homOfLE h) ≫ (eH j).hom =
          spectralLimitCohomologyMap (f i j h) (cf i j h) (α i j h) q) ∧
      ∃ (c : Cocone H) (ec : c.pt ≅ CategoryTheory.Sheaf.H' (colimit P) q ⊤),
        (∀ i : I, c.ι.app i ≫ ec.hom = (eH i).hom ≫
          spectralLimitCohomologyMap (p i) (cp i)
            ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
              (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
                (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q) ∧
        IsIso (colimit.desc H c ≫ ec.hom) := by
  sorry

end TopCat.Sheaf
