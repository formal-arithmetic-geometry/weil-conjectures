/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity

import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.OrderedTateExponentPullback
import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates

/-! # Root transitions of the ordinary local vector trace

Source: vector-bundle integration, local chart construction; Stacks 03PK.
(blueprint: lem-pur-vector-local-trace-exponent)
-/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

private theorem coefficient_square_core
    {C D H J : Type*} [Category C] [Category D] [Category H] [Category J]
    (U : C ⥤ D) (V : D ⥤ H) (W : C ⥤ J) (P : J ⥤ H)
    (c : U ⋙ V ≅ W ⋙ P) {Ks Kr : C} {Ls Lr : J} {Rs Rr : H}
    (B : Ks ⟶ Kr) (b : Ls ⟶ Lr)
    (bs : W.obj Ks ≅ Ls) (br : W.obj Kr ≅ Lr)
    (ds : Rs ≅ P.obj Ls) (dr : Rr ≅ P.obj Lr)
    (hb : W.map B ≫ br.hom = bs.hom ≫ b) :
    V.map (U.map B) ≫ (c.app Kr ≪≫ P.mapIso br ≪≫ dr.symm).hom =
      (c.app Ks ≪≫ P.mapIso bs ≪≫ ds.symm).hom ≫
        (ds.hom ≫ P.map b ≫ dr.inv) := by
  have hn := c.hom.naturality B
  simp only [Functor.comp_map] at hn
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% hn, ← P.map_comp_assoc, hb, P.map_comp]
  simp only [Category.assoc]

private theorem coefficient_square
    {C D H J : Type*} [Category C] [Category D] [Category H] [Category J]
    (U : C ⥤ D) (V : D ⥤ H) (W : C ⥤ J) (P : J ⥤ H)
    {F₁ F₂ : C ⥤ H} (c₁ : U ⋙ V ≅ F₁) (c₂ : F₁ ≅ F₂) (c₃ : F₂ ≅ W ⋙ P)
    {Ks Kr : C} {Ls Lr : J} {Rs Rr : H}
    (B : Ks ⟶ Kr) (b : Ls ⟶ Lr)
    (bs : W.obj Ks ≅ Ls) (br : W.obj Kr ≅ Lr)
    (ds : Rs ≅ P.obj Ls) (dr : Rr ≅ P.obj Lr)
    (hb : W.map B ≫ br.hom = bs.hom ≫ b) :
    V.map (U.map B) ≫
        (c₁.app Kr ≪≫ c₂.app Kr ≪≫ c₃.app Kr ≪≫ P.mapIso br ≪≫ dr.symm).hom =
      (c₁.app Ks ≪≫ c₂.app Ks ≪≫ c₃.app Ks ≪≫ P.mapIso bs ≪≫ ds.symm).hom ≫
        (ds.hom ≫ P.map b ≫ dr.inv) := by
  simpa only [NatIso.trans_app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, NatTrans.comp_app, Category.assoc] using
    coefficient_square_core U V W P (c₁ ≪≫ c₂ ≪≫ c₃) B b bs br ds dr hb

private theorem paste_trace_square
    {C D : Type*} [Category C] [Category D] (R T : C ⥤ D)
    {Xs Xr Ys Yr : C} {Ms Mr U : D}
    (m : Ms ⟶ Mr) (er : Mr ⟶ R.obj Xr) (es : Ms ⟶ R.obj Xs)
    (f : Xs ⟶ Xr) (cr : Xr ⟶ Yr) (cs : Xs ⟶ Ys) (z : Ys ⟶ Yr)
    (kr : R.obj Yr ⟶ T.obj Yr) (ks : R.obj Ys ⟶ T.obj Ys)
    (tr : T.obj Yr ⟶ U) (ts : T.obj Ys ⟶ U)
    (he : m ≫ er = es ≫ R.map f) (hc : f ≫ cr = cs ≫ z)
    (hk : R.map z ≫ kr = ks ≫ T.map z) (ht : T.map z ≫ tr = ts) :
    m ≫ er ≫ R.map cr ≫ kr ≫ tr = es ≫ R.map cs ≫ ks ≫ ts := by
  rw [reassoc_of% he, ← R.map_comp_assoc, hc, R.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hk, ht]

private theorem compact_comparison_naturality
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hA : (N : A) = 0) (hB : (M : A) = 0)
    (T : Scheme.{u}) [IsNoetherian T]
    (hT : IsUnit (N : Γ(T, ⊤))) (hT' : IsUnit (M : Γ(T, ⊤))) (d : ℕ)
    (z : (Etale.affineTraceRight A M hB T d).obj (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.affineTraceRight A N hA T d).obj (Etale.ordinaryFiniteUnit A T)) :
    (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (affineTraceProjection T d)).map z ≫
      (Etale.affineLinearCompactComparison N hN A hA T hT d).inv =
    (Etale.affineLinearCompactComparison M hM A hB T hT' d).inv ≫
      (Etale.affineTraceLeft A T d).map z := by
  let Kr : DerivedCategory.Plus
      (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace N hN A hA) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 T hT d).2.1))⟩
  let Ks : DerivedCategory.Plus
      (Sheaf (affineTraceTower T d).smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    ⟨_, Exists.elim (Etale.exists_affineSpaceTopTrace M hM A hB) (fun _ ht ↦
      Exists.elim ht (fun _ hD ↦ (hD.2 T hT' d).2.1))⟩
  let c := (Etale.affineTracePlusCompatibility A T d).symm ≪≫
    Functor.isoWhiskerRight (Etale.affineTraceCompactSupportComparison A T d)
      DerivedCategory.Plus.ι ≪≫
    Etale.rightDerivedLowerShriekPlusCompatibility (ModuleCat.{u + 1} A)
      (affineTraceProjection T d)
  change (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (affineTraceProjection T d)).map z ≫ c.inv.app Kr =
    c.inv.app Ks ≫ (Etale.affineTraceLeft A T d).map z
  exact c.inv.naturality (ObjectProperty.homMk (X := Ks) (Y := Kr) z)

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
