/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import all Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! Source-open normalization of compact-support composition. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Keep signature checking from unfolding the compactification and derived constructions.
attribute [local irreducible] lowerStar openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor rightDerivedLowerShriekIso
  rightDerivedLowerShriekOfCompactificationIso unboundedEtaleLowerShriekCompIso

/-- Restricting the source open in a compactification computes the specified composition
comparison. This is the source-open specialization of the compact-support composition law.
Source: Stacks Project, More on Etale Cohomology, Tag 0F7J, the first two equalities in
Lemma `lemma-shriek-composition`, together with the identity normalization of the
proper/open comparison in Tag 0F7B
(blueprint: lem-amb-compact-support-open-source-composition).

Proof: use the triangle with compactifications `(w,id)`, `c`, and `c.precomp w`,
open map `c.i`, and proper map the identity of `c.Z`. Its exchange square has identity
horizontal arrows. The identity-square exchange law and the left unit law for proper
composition reduce its compositor to inverse open composition, preceded by the proper
identity comparison. The every-triangle equation compares these models with the chosen
compactifications. Identify the formalism's open compositor and proper identity map with
the specified derived comparisons. Cancel the comparison for `(w,id)` against the open
identification, and cancel the proper identity factors. Naturality of the comparison for
`c` gives the displayed formula. The same identity laws apply to empty and identity opens. -/
theorem unboundedEtaleLowerShriekCompIso_open_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V X S : Scheme.{u}} [IsNoetherian V] [IsNoetherian X] [IsNoetherian S]
    (w : V ⟶ X) (f : X ⟶ S) [IsOpenImmersion w]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification w] [HasCompactification f] [HasCompactification (w ≫ f)]
    (c : Compactification f) :
    Functor.isoWhiskerRight (rightDerivedLowerShriekIsoOfIsOpenImmersion A w).symm
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
      unboundedEtaleLowerShriekCompIso A w f =
    Functor.isoWhiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) w).mapDerivedCategory
        (rightDerivedLowerShriekIso A c).symm ≪≫
      Functor.isoWhiskerRight
        (mapDerivedCategoryOpenImmersionLowerShriekComp (ModuleCat.{u + 1} A) w c.i).symm
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g) ≪≫
      rightDerivedLowerShriekIso A (c.precomp w) := by
  let T : Compactification.Triangle w f :=
    { cf := Compactification.ofIsOpenImmersion w
      cg := c
      cfg := c.precomp w
      q := c.i
      p := 𝟙 c.Z
      i_q := rfl
      p_g := Category.id_comp _
      isPullback := by
        change IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)
        exact IsPullback.of_horiz_isIso ⟨by simp⟩ }
  let F := unboundedFormalism A
  have : F.HasBaseChange := unbounded_has_base_change A
  have : F.HasProperExchange := unbounded_has_proper_exchange A
  have hT (K : DerivedCategoryModule A V) :
      (F.compIso T).hom.app K =
        (F.pf c.g).map ((F.sh c.i).map
          ((F.pfId X).hom.app ((F.sh w).obj K)) ≫
          (F.shComp' w c.i (w ≫ c.i) rfl).inv.app K) := by
    rw [CompactSupportFormalism.compIso_hom_app]
    dsimp only [T, Compactification.ofIsOpenImmersion, Compactification.precomp]
    rw [F.exchange_id_horiz, F.pfComp'_id_left_inv_app]
    simp only [CategoryTheory.TwoSquare.whiskerTop, CategoryTheory.TwoSquare.whiskerBottom,
      CategoryTheory.TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, Category.comp_id]
    rw [← Functor.map_comp]
    congr 1
    simp only [Category.assoc]
    rw [← (F.pfId c.Z).inv.naturality_assoc]
    simp
  have h := F.lowerShriekCompIso_hom_eq T
  rw [unbounded_chosen_comp] at h
  rw [← F.shriekIso_symm T.cf (HasCompactification.compactification w),
    ← F.shriekIso_symm T.cg (HasCompactification.compactification f)] at h
  simp only [F, unbounded_shriek_iso] at h
  rw [← rightDerivedLowerShriekIso, ← rightDerivedLowerShriekIso,
    ← rightDerivedLowerShriekIso] at h
  simp only [T, Iso.symm_hom] at h
  apply Iso.ext
  ext K
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [h]
  simp only [NatTrans.comp_app, NatTrans.hcomp_app]
  rw [hT]
  simp only [F, unbounded_sh_comp, mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_trans]
  rw [rightDerivedLowerShriekIsoOfIsOpenImmersion, ← unbounded_pf_id]
  simp only [Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Category.id_comp]
  simp only [Category.assoc]
  erw [(rightDerivedLowerShriekIso A c).inv.naturality_assoc]
  simp only [CompactSupportFormalism.shriek, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  dsimp only [unboundedFormalism]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end AlgebraicGeometry.Etale
