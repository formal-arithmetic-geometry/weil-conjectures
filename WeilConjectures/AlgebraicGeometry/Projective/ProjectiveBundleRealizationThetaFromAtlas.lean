/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleRealizationPullbackAtlas

/-! # Gluing a realization base-change theta from a frame atlas
Source: Stacks Project, Tags 01NQ and 01OB.
(blueprint: lem-pur-projective-bundle-realization-theta-from-atlas).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Two maps out of a common source whose local coefficients against matching free generators
agree are intertwined by the glued free-generator isomorphism. -/
private theorem isoOfIsFreeGenerator_comp_eq {X : Scheme.{u}} {P M N : X.Modules} {ι : Type u}
    {U : ι → X.Opens} {s : ∀ i, Γ(M, U i)} {t : ∀ i, Γ(N, U i)} (hU : ⨆ i, U i = ⊤)
    (hs : ∀ i, Scheme.Modules.IsFreeGenerator (s i))
    (ht : ∀ i, Scheme.Modules.IsFreeGenerator (t i))
    (hc : ∀ i j (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (a c : Γ(X, W)),
      a • M.presheaf.map (homOfLE hi).op (s i) = c • M.presheaf.map (homOfLE hj).op (s j) →
        a • N.presheaf.map (homOfLE hi).op (t i) = c • N.presheaf.map (homOfLE hj).op (t j))
    (l : P ⟶ M) (r : P ⟶ N)
    (hlr : ∀ i (V : X.Opens) (hi : V ≤ U i) (m : Γ(P, V)), ∃ c : Γ(X, V),
      l.app V m = c • M.presheaf.map (homOfLE hi).op (s i) ∧
        r.app V m = c • N.presheaf.map (homOfLE hi).op (t i)) :
    l ≫ (Scheme.Modules.isoOfIsFreeGenerator hU hs ht hc).hom = r := by
  refine Scheme.Modules.hom_ext _ _ fun V ↦ ?_
  ext m
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun i ↦ V ⊓ U i) V
    (fun _ ↦ homOfLE inf_le_left) (fun x hx ↦ ?_) _ _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩
  · obtain ⟨c, hl, hr⟩ := hlr i (V ⊓ U i) inf_le_right (P.presheaf.map (homOfLE inf_le_left).op m)
    rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ← Scheme.Modules.Hom.app_presheaf_map_apply, ← Scheme.Modules.Hom.app_presheaf_map_apply,
      ← Scheme.Modules.Hom.app_presheaf_map_apply, hl, hr,
      Scheme.Modules.isoOfIsFreeGenerator_hom_app_smul]

/-- A common frame atlas glues to the line isomorphism carrying the first quotient to the
second quotient, with the canonical tensor-pullback coherence expanded in the quotient law.
Source: Stacks Project, Tags 01NQ and 01OB.
Proof: glue the local maps sending the first frame to the second with
`Scheme.Modules.isoOfIsFreeGenerator`, using the equal transitions of the atlas.  The atlas
coefficient equations say that, on every section over an open of the cover, the pulled-back
source quotient followed by the glued map and the coherence-expanded target quotient are the
same multiple of the target frame; by the sheaf axiom the two morphisms agree, which is
`projectiveBundleThetaQuotientLaw`.
(blueprint: lem-pur-projective-bundle-realization-theta-from-atlas).
-/
theorem projectiveBundleRealizationTheta_of_atlas
    {B B' : Scheme.{u}} {F : B.Modules} {F' : B'.Modules}
    (D : ProjectiveBundleRealization B F) (D' : ProjectiveBundleRealization B' F')
    (g : B' ⟶ B) (e : F' ≅ (Scheme.Modules.tensorPullback g).obj F)
    (b : Scheme.GradedAlgebraData.PullbackData g D.A.data D'.A.data)
    (A : ProjectiveBundleRealizationPullbackAtlas D D' g e b) :
    ∃ theta : (Scheme.Modules.tensorPullback b.relProjComparison).obj D.L ≅ D'.L,
      projectiveBundleThetaQuotientLaw D D' g e b.relProjComparison b.isPullback.w theta :=
  ⟨Scheme.Modules.isoOfIsFreeGenerator A.cover A.s_generator A.t_generator A.transition,
    isoOfIsFreeGenerator_comp_eq A.cover A.s_generator A.t_generator A.transition _ _
      A.coefficients⟩

end AlgebraicGeometry
