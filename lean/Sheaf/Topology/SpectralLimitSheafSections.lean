/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Sheaf.Topology.SpectralDirectedLimit
import Sheaf.Topology.SheavesDirectedColimitSections
import Sheaf.Topology.SpectralLimitPullbackSections

/-!
# Sections of abelian sheaf systems on spectral inverse limits

Source: Stacks Project, Sheaves on Spaces, Tag 0A33, lemma-descend-opens
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

/-- Restrict the existing filtered-colimit preservation to a smaller indexing universe.
This supplies sheafification for abelian coefficients larger than the space universe.
Source: Stacks Project, Sheaves on Spaces, Tag 0A33, passage to abelian sheaves;
Mathlib's `preservesFilteredColimitsOfSize_of_univLE`
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections). -/
noncomputable instance (priority := 90) AddCommGrpCat.forget_preservesSmallerFilteredColimits
    [UnivLE.{u, v}] :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{v}) :=
  preservesFilteredColimitsOfSize_of_univLE.{v, v} (forget AddCommGrpCat.{v})

namespace TopCat.Sheaf

/-- The canonical map from the colimit of finite-stage section groups is an isomorphism.
Source: Stacks Project, Sheaves on Spaces, Tag 0A33, lemma-descend-opens
(blueprint: lem-weil-pbc-spectral-limit-sheaf-sections).

The isomorphisms `eG` and `eB` identify the objects of the two diagrams with their
specified formulas. `hGmap` characterizes the pulled-back transition on every unit
section: this is precisely pullback of the adjoint of `alpha`. `hBmap` specifies the
finite-stage transition, and `hm` specifies the comparison on every coprojection.
Heterogeneous equality only transports across equal inverse-image opens. Thus none
of these maps is an unspecified comparison. The inverse image is the recorded
sheafification construction, allowing the coefficient universe to exceed that of the spaces.

Proof, following the DAG node:
1. Compute abelian sheaf colimits by sheafifying sectionwise abelian group colimits.
   Underlying sets commute with directed group colimits by their representative and
   eventual-equality descriptions. Sheafification commutes with forgetting to sets
   (`lem-pc-sites-sheafification-underlying-sets`). Apply the same argument to the
   neighborhood colimits defining inverse image, including its section unit.
2. The spectral directed-limit theorem makes the limit spectral and the pulled-back
   open compact. Refine any open cover by compact basis opens and take a finite
   subcover; pairwise intersections are compact. Apply directed-colimit sections
   (Tag 009F). Restricting indices to the upper tail is cofinal, by common upper bounds.
3. Apply spectral-limit pullback sections (Tag 0A32) to each stage sheaf and its
   compact inverse-image open. Naturality of the units and composition identifications
   makes this identification natural in the stage sheaf.
4. Write beta for the adjoint of alpha. Map the inner term at indices j,k to the
   section colimit by beta_jk followed by its coprojection. Naturality of units and
   the alpha cocycle give inner and outer compatibility. Conversely insert the
   diagonal terms k,k in the double colimit. The two composites are identities:
   on diagonal terms use beta_kk = id, and on j,k use the outer transition to k,k.
   This does not assert that beta_jk is itself invertible.
5. Combine the preceding colimit identifications. On each stage the resulting map
   is the pullback unit followed by the sheaf-colimit coprojection, exactly `hm`.
   All maps are additive, so the resulting bijection is an abelian group isomorphism. -/
theorem spectralLimit_sheaf_sections
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ j : I, SpectralSpace (S j)]
    (f : ∀ (j k : I), j ≤ k → (S k ⟶ S j))
    (hf : ∀ (j k : I) (h : j ≤ k), IsSpectralMap (f j k h))
    (hfid : ∀ j : I, f j j le_rfl = 𝟙 (S j))
    (hfcomp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l),
      f k l hkl ≫ f j k hjk = f j l (hjk.trans hkl))
    (X : TopCat.{u}) (p : ∀ j : I, X ⟶ S j)
    (hpcomp : ∀ (j k : I) (h : j ≤ k), p k ≫ f j k h = p j)
    (hlimit : ∀ a : ∀ j : I, S j,
      (∀ (j k : I) (h : j ≤ k), f j k h (a k) = a j) →
      ∃! x : X, ∀ j : I, p j x = a j)
    (htop : X.str = ⨅ j : I, TopologicalSpace.induced (p j) (S j).str)
    (F : ∀ j : I, (S j).Sheaf AddCommGrpCat.{max u v})
    (alpha : ∀ (j k : I) (h : j ≤ k),
      F j ⟶ (pushforward AddCommGrpCat.{max u v} (f j k h)).obj (F k))
    (halpha_id : ∀ (j : I) (V : Opens (S j)) (s : (F j).obj.obj (op V)),
      HEq ((alpha j j le_rfl).hom.app (op V) s) s)
    (halpha_comp : ∀ (j k l : I) (hjk : j ≤ k) (hkl : k ≤ l)
        (V : Opens (S j)) (s : (F j).obj.obj (op V)),
      HEq ((alpha k l hkl).hom.app (op ((Opens.map (f j k hjk)).obj V))
          ((alpha j k hjk).hom.app (op V) s))
        ((alpha j l (hjk.trans hkl)).hom.app (op V) s))
    (G : I ⥤ X.Sheaf AddCommGrpCat.{max u v})
    (eG : ∀ j : I, G.obj j ≅
      (Functor.sheafPullbackConstruction.sheafPullback (Opens.map (p j))
        AddCommGrpCat.{max u v} (Opens.grothendieckTopology (S j))
          (Opens.grothendieckTopology X)).obj (F j))
    (hGmap : ∀ (j k : I) (hjk : j ≤ k) (V : Opens (S j))
        (s : (F j).obj.obj (op V)),
      HEq (((G.map (homOfLE hjk)) ≫ (eG k).hom).hom.app
          (op ((Opens.map (p j)).obj V))
        ((eG j).inv.hom.app (op ((Opens.map (p j)).obj V))
          (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (Opens.map (p j)) AddCommGrpCat.{max u v}
            (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
              (F j)).hom.app (op V) s)))
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Opens.map (p k)) AddCommGrpCat.{max u v}
          (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).unit.app
            (F k)).hom.app (op ((Opens.map (f j k hjk)).obj V))
              ((alpha j k hjk).hom.app (op V) s)))
    (c : Cocone G) (hc : IsColimit c)
    (i : I) (U : Opens (S i)) (hU : IsCompact (U : Set (S i)))
    (B : Set.Ici i ⥤ AddCommGrpCat.{max u v})
    (eB : ∀ j : Set.Ici i, B.obj j ≅
      (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U)))
    (hBmap : ∀ (j k : Set.Ici i) (hjk : j ≤ k)
        (s : (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U))),
      HEq ((eB k).hom (B.map (homOfLE hjk) ((eB j).inv s)))
        ((alpha j.val k.val hjk).hom.app
          (op ((Opens.map (f i j.val j.property)).obj U)) s))
    [HasColimit B]
    (m : colimit B ⟶ c.pt.obj.obj (op ((Opens.map (p i)).obj U)))
    (hm : ∀ (j : Set.Ici i)
        (s : (F j.val).obj.obj (op ((Opens.map (f i j.val j.property)).obj U))),
      HEq (m (colimit.ι B j ((eB j).inv s)))
        ((c.ι.app j.val).hom.app
          (op ((Opens.map (p j.val)).obj ((Opens.map (f i j.val j.property)).obj U)))
          ((eG j.val).inv.hom.app
            (op ((Opens.map (p j.val)).obj ((Opens.map (f i j.val j.property)).obj U)))
            (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (Opens.map (p j.val)) AddCommGrpCat.{max u v}
              (Opens.grothendieckTopology (S j.val))
              (Opens.grothendieckTopology X)).unit.app (F j.val)).hom.app
                (op ((Opens.map (f i j.val j.property)).obj U)) s)))) :
    IsIso m := by
  sorry

end TopCat.Sheaf
