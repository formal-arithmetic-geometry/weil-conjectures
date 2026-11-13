/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting

/-! # Side-square pasting for a shrinking graph neighborhood

Source: Stacks Project, Tag 0F7J, graph neighborhood pasting.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

private theorem cancel_side₂
    {C : Type*} [Category C] {A B B' D D' E E' : C}
    (a : A ≅ B) (a' : A ≅ B') (m : B ≅ D) (m' : B' ≅ D')
    (s : E ≅ D) (s' : E' ≅ D') (F : B ≅ B') (T : D ≅ D')
    (K : E ≅ E')
    (ha : a.hom ≫ F.hom = a'.hom)
    (hm : m.hom ≫ T.hom = F.hom ≫ m'.hom)
    (h : (a ≪≫ m ≪≫ s.symm).hom ≫ K.hom =
      (a' ≪≫ m' ≪≫ s'.symm).hom) :
    s.hom ≫ T.hom = K.hom ≫ s'.hom := by
  have hp := congrArg (fun q => q ≫ s'.hom) h
  have hmt : (a.hom ≫ m.hom) ≫ T.hom = a'.hom ≫ m'.hom := by
    calc
      (a.hom ≫ m.hom) ≫ T.hom = a.hom ≫ (m.hom ≫ T.hom) := by
        simp only [Category.assoc]
      _ = a.hom ≫ (F.hom ≫ m'.hom) := by rw [hm]
      _ = a'.hom ≫ m'.hom := by rw [← Category.assoc, ha]
  have hc : s.inv ≫ K.hom ≫ s'.hom = T.hom := by
    apply (cancel_epi (a.hom ≫ m.hom)).1
    calc
      (a.hom ≫ m.hom) ≫ s.inv ≫ K.hom ≫ s'.hom = a'.hom ≫ m'.hom := by
        simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
          Iso.inv_hom_id, Category.comp_id] using hp
      _ = (a.hom ≫ m.hom) ≫ T.hom := by simpa only [Category.assoc] using hmt.symm
  apply (cancel_epi s.inv).1
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc,
    Category.comp_id] using hc.symm

/-- The side comparison respects an open shrinking of its proper graph (Stacks, Tag 0F7J). -/
theorem etaleGraphShrinkSidePasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Z W : Scheme.{u}} {h : X ⟶ Z} (c : Compactification h)
    (H : EtaleGraphPresentation h) (a' : X ⟶ W) (v : W ⟶ H.U)
    [IsProper a'] [IsOpenImmersion v] (fac : a' ≫ v = H.a) :
    (H.graphSide₂ c A).hom ≫ (H.graphNeighborhoodTriangle c A a' v fac).hom =
      (etaleGraphShrinkInterchange A H a' v fac).hom ≫
        ((H.shrink a' v fac).graphSide₂ c A).hom := by
  have hfrom (t : EtaleGraphPresentation h) :
      etaleGraphComparisonFromOpen A c t =
        t.graphSide₁ c A ≪≫ t.graphMiddle c A ≪≫ (t.graphSide₂ c A).symm := by
    apply Iso.ext
    simp only [etaleGraphComparisonFromOpen, locallyClosedGraphIso,
      EtaleGraphPresentation.graphSide₁, EtaleGraphPresentation.graphSide₂,
      EtaleGraphPresentation.graphMiddle, Iso.trans_hom, Category.assoc]
  have hopen := etaleGraphComparisonFromOpen_openShrink A c H a' v (v ≫ H.e) fac rfl
  dsimp at hopen
  change _ = etaleGraphComparisonFromOpen A c (H.shrink a' v fac) at hopen
  rw [hfrom H, hfrom (H.shrink a' v fac)] at hopen
  have hopen_h := congrArg Iso.hom hopen
  exact cancel_side₂ (H.graphSide₁ c A)
    ((H.shrink a' v fac).graphSide₁ c A)
    (H.graphMiddle c A) ((H.shrink a' v fac).graphMiddle c A)
    (H.graphSide₂ c A) ((H.shrink a' v fac).graphSide₂ c A)
    (H.graphFirstShrinkIso c A a' v fac)
    (H.graphNeighborhoodTriangle c A a' v fac)
    (etaleGraphShrinkInterchange A H a' v fac)
    (by simp [EtaleGraphPresentation.graphFirstShrinkIso])
    (etaleGraphShrinkMiddlePasting A c H a' v fac)
    (by simpa [etaleGraphShrinkInterchange,
      mapDerivedCategoryOpenImmersionLowerShriekCongr,
      Functor.isoWhiskerLeft_trans, Iso.trans_hom, Category.assoc] using hopen_h)

end AlgebraicGeometry.Etale
