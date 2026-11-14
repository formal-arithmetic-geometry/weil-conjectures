/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjQuotientPullbackLocalComparison
import WeilConjectures.AlgebraicGeometry.Modules.FreeGeneratorIso

/-! # Comparison of normalized quotient lines along a fixed Proj comparison

Source: Stacks Project, Constructions, Tags 01NR, 01NQ and 01OB.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

open Scheme.Modules

-- Match the finite-limit instance used by the normalized quotient definitions.
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjι
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

private theorem iso_of_common_frame_coefficients {T : Scheme.{u}}
    {M P Q : T.Modules} (q : M ⟶ P) (q' : M ⟶ Q) {ι : Type u}
    (U : ι → T.Opens) (s : ∀ i, Γ(P, U i)) (t : ∀ i, Γ(Q, U i))
    (hU : (⨆ i, U i) = ⊤) (hs : ∀ i, IsFreeGenerator (s i))
    (ht : ∀ i, IsFreeGenerator (t i))
    (hc : ∀ i j (V : T.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (a c : Γ(T, V)),
      a • P.presheaf.map (homOfLE hi).op (s i) =
        c • P.presheaf.map (homOfLE hj).op (s j) →
      a • Q.presheaf.map (homOfLE hi).op (t i) =
        c • Q.presheaf.map (homOfLE hj).op (t j))
    (hq : ∀ i (V : T.Opens) (hi : V ≤ U i) (m : Γ(M, V)),
      ∃ c : Γ(T, V), q.app V m = c • P.presheaf.map (homOfLE hi).op (s i) ∧
        q'.app V m = c • Q.presheaf.map (homOfLE hi).op (t i)) :
    ∃ w : P ≅ Q, q ≫ w.hom = q' := by
  let w := isoOfIsFreeGenerator hU hs ht hc
  refine ⟨w, Scheme.Modules.hom_ext _ _ fun V ↦ ?_⟩
  ext m
  have hcover : V ≤ ⨆ i, U i ⊓ V := by
    rw [← iSup_inf_eq, hU, top_inf_eq]
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨Q.presheaf, Q.isSheaf⟩
    (fun i ↦ U i ⊓ V) V (fun _ ↦ homOfLE inf_le_right) hcover
  intro i
  rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map]
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  obtain ⟨c, hcs, hct⟩ := hq i (U i ⊓ V) inf_le_left
    (M.presheaf.map (homOfLE inf_le_right).op m)
  rw [hcs, hct]
  exact isoOfIsFreeGenerator_hom_app_smul hU hs ht hc i inf_le_left c

/-- For fixed normalized quotients and a fixed generator-preserving graded pullback
comparison, the quotient lines agree along its induced relative Proj map.

Source: Stacks Project, Constructions, Tag 01NQ, the degree-one part of theta; Tag 01NR, uniqueness;
Tag 01OB, the quotient normalization. -/
theorem quotient_comparison_of_normalized_pullbackData
    {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (D' : ProjectiveBundleQuotientGeometry.TautologicalQuotient
      ((Scheme.Modules.tensorPullback g).obj E))
    (b : Scheme.GradedAlgebraData.PullbackData g (SymmetricAlgebraSheaf.gradedAlgebraData E)
      (SymmetricAlgebraSheaf.gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)))
    (hb : ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
      (m : E.val.obj (op U.1)),
      b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
        SymmetricAlgebra.ι Γ(X, W.1) _
          (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
            (Scheme.Modules.tensorPullbackSection g E U.1 m)))
    (e : (Scheme.Modules.tensorPullback
        (b.relProjComparison ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom)).obj E =
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData
          ((Scheme.Modules.tensorPullback g).obj E)).relProjHom ≫ g)).obj E) :
    ∃ w : (Scheme.Modules.tensorPullback b.relProjComparison).obj D.line ≅ D'.line,
      (Scheme.Modules.tensorPullbackSectionComp b.relProjComparison
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).hom.app E ≫
          (Scheme.Modules.tensorPullback b.relProjComparison).map D.quotient ≫ w.hom =
        (eqToIso e).hom ≫
        (Scheme.Modules.tensorPullbackSectionComp
          (SymmetricAlgebraSheaf.gradedAlgebraData
            ((Scheme.Modules.tensorPullback g).obj E)).relProjHom g).hom.app E ≫
          D'.quotient := by
  obtain ⟨ι, U, s, t, hU, hs, ht, hc, hq⟩ :=
    exists_normalized_pullback_frame_atlas g E D D' b hb e
  exact iso_of_common_frame_coefficients _ _ U s t hU hs ht hc hq

end AlgebraicGeometry.SymmetricProjTautologicalCharts
