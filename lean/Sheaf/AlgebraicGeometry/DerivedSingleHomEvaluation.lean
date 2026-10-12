/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMap

/-! # Derived single-source Hom evaluation

Source: Stacks Project, duality.tex, Tags 0BUZ, 0BV0, and 0AX3.
-/

@[expose] public section
universe u wY
open CategoryTheory Opposite AlgebraicGeometry
namespace AlgebraicGeometry
private noncomputable def evaluationIso
    {C E : Type*} [Category* C] [Category* E]
    (Q : C ⥤ E) (H : Cᵒᵖ ⥤ C ⥤ C) (D : Eᵒᵖ × E ⥤ E)
    (F : C ⥤ C) (L : C) (e : H.obj (op L) ≅ 𝟭 C)
    (d : Q.op.prod Q ⋙ D ≅ (𝟭 _).prod F ⋙ Functor.uncurry.obj H ⋙ Q)
    (r : Q ≅ F ⋙ Q) :
    Q ⋙ (Functor.curry.obj D).obj (op (Q.obj L)) ≅ Q ⋙ 𝟭 E :=
  let a := (Functor.curryObjProdComp Q.op Q D).app (op L)
  let b : (Functor.curry.obj
      ((𝟭 _).prod F ⋙ Functor.uncurry.obj H ⋙ Q)).obj (op L) ≅
      F ⋙ H.obj (op L) ⋙ Q :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (by intro M N f; simp)
  a.symm ≪≫ (Functor.curry.mapIso d).app (op L) ≪≫ b ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight e Q) ≪≫
      (Functor.associator F (𝟭 _) Q).symm ≪≫
      Functor.isoWhiskerRight F.rightUnitor Q ≪≫ r.symm ≪≫ Q.rightUnitor.symm

private lemma evaluationIso_hom_app
    {C E : Type*} [Category* C] [Category* E]
    (Q : C ⥤ E) (H : Cᵒᵖ ⥤ C ⥤ C) (D : Eᵒᵖ × E ⥤ E)
    (F : C ⥤ C) (L : C) (e : H.obj (op L) ≅ 𝟭 C)
    (d : Q.op.prod Q ⋙ D ≅ (𝟭 _).prod F ⋙ Functor.uncurry.obj H ⋙ Q)
    (r : Q ≅ F ⋙ Q) (M : C) :
    (evaluationIso Q H D F L e d r).hom.app M =
      d.hom.app (op L, M) ≫ Q.map (e.hom.app (F.obj M)) ≫ r.inv.app M := by
  simp [evaluationIso]

private lemma evaluation_compatibility
    {C E : Type*} [Category* C] [Category* E]
    (Q : C ⥤ E) (H : Cᵒᵖ ⥤ C ⥤ C) (D : Eᵒᵖ × E ⥤ E)
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) (L : C) (e : H.obj (op L) ≅ 𝟭 C)
    (d : Q.op.prod Q ⋙ D ≅ (𝟭 _).prod F ⋙ Functor.uncurry.obj H ⋙ Q)
    (B M : C) (t : L ⟶ B) [IsIso (Q.map (η.app M))] :
    Q.map ((H.obj (op B)).map (η.app M)) ≫
      d.inv.app (op B, M) ≫ D.map (X := (op (Q.obj B), Q.obj M)) (Y := (op (Q.obj L), Q.obj M))
        ((Q.map t).op, 𝟙 (Q.obj M)) ≫
      d.hom.app (op L, M) ≫ Q.map (e.hom.app (F.obj M)) ≫
      inv (Q.map (η.app M)) = Q.map ((H.map t.op).app M ≫ e.hom.app M) := by
  have hd : D.map (X := (op (Q.obj B), Q.obj M)) (Y := (op (Q.obj L), Q.obj M))
        ((Q.map t).op, 𝟙 (Q.obj M)) ≫ d.hom.app (op L, M) =
      d.hom.app (op B, M) ≫ Q.map ((H.map t.op).app (F.obj M)) := by
    simpa using d.hom.naturality (X := (op B, M)) (Y := (op L, M)) (t.op, 𝟙 M)
  have hh := (H.map t.op).naturality (η.app M)
  have he := e.hom.naturality (η.app M)
  rw [reassoc_of% hd]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Q.map_comp_assoc, hh, ← Q.map_comp_assoc]
  change (H.obj (op L)).map (η.app M) ≫ e.hom.app (F.obj M) =
    e.hom.app M ≫ η.app M at he
  rw [Category.assoc, he, Q.map_comp, Q.map_comp]
  simp

set_option maxHeartbeats 800000 in
-- Functorial K-injective replacement and the localization comparison have large types.
/-- A natural unit-Hom identification descends to the derived category together
with K-injective comparisons compatible with every map out of the unit.

Source: Stacks Project, sites-cohomology.tex, Section 08J7 and Lemma 0A95;
the localization calculation in lem-sc-affine-hom-kinjective-evaluation, step 1.
(blueprint: lem-sc-derived-single-hom-evaluation).

Proof:
1. Write I0 for the functorial K-injective replacement and eta for its augmentation.
   Use derivedInternalHom_comparison for this replacement. Fixing its first
   variable at O_Y[0], compose it with e on I0 and the inverse of Q(eta).
   This gives a natural isomorphism after precomposition by Q. Fully faithful
   precomposition by Q descends it to j on the derived category.
2. For a K-injective complex I, eta_I is a quasi-isomorphism between K-injectives.
   Hence Hom(B[0], eta_I) is a quasi-isomorphism by quasiIso_homComplex_map.
   Compose Q of this map with the inverse of the comparison at (B[0], I) to
   obtain c from the unresolved Hom complex to derived internal Hom.
3. Naturality of the comparison in the first variable moves precomposition by
   k[0] across it. The comparison at O_Y[0] cancels against its inverse in j.
   Naturality of the Hom-complex bifunctor moves eta across precomposition by k.
   Finally naturality of e moves eta across evaluation, and Q(eta) cancels
   with its inverse. The resulting composite is Q of precomposition by k[0]
   followed by e_I, as asserted. No finiteness or boundedness hypothesis is used;
   the zero map k, zero B, zero ring and empty scheme obey the same identities. -/
theorem derived_single_hom_evaluation (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (e : (homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) :
    ∃ j : (Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _,
      ∀ (B : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
        (k : SheafOfModules.unit Y.ringCatSheaf ⟶ B)
        (I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
        (_ : I.IsKInjective),
      ∃ c : DerivedCategory.Q.obj
          (homComplex (R := Y.toRingedSpace.sheaf)
            ((CochainComplex.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B) I) ≅
          (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
            (op ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj B),
              DerivedCategory.Q.obj I),
        c.hom ≫ (derivedInternalHom (Opens.grothendieckTopology Y)
            Y.toRingedSpace.sheaf).map
          (((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op,
            𝟙 (DerivedCategory.Q.obj I)) ≫
          j.hom.app (DerivedCategory.Q.obj I) =
            DerivedCategory.Q.map
              (((homComplexFunctor (R := Y.toRingedSpace.sheaf)).map
                (((CochainComplex.singleFunctor
                  (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op)).app I ≫
                    e.hom.app I) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  have : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I₀ := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let L := (CochainComplex.singleFunctor A 0).obj (SheafOfModules.unit Y.ringCatSheaf)
  let H : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
    homComplexFunctor (R := Y.toRingedSpace.sheaf)
  let D : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A :=
    derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
  obtain ⟨d₀⟩ := derivedInternalHom_comparison.{u, wY}
    (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf I₀ η
    (fun M ↦ ⟨(CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2,
      CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A M⟩)
  let d : Q.op.prod Q ⋙ D ≅
      (𝟭 _).prod I₀ ⋙ Functor.uncurry.obj H ⋙ Q := d₀
  change H.obj (op L) ≅ 𝟭 (CochainComplex A ℤ) at e
  have hη (M : CochainComplex A ℤ) : IsIso (Q.map (η.app M)) := by
    have : QuasiIso (η.app M) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A M).2
    infer_instance
  let r : Q ≅ I₀ ⋙ Q :=
    NatIso.ofComponents (fun M ↦ asIso (Q.map (η.app M))) (by
      intro M N f
      simpa only [Functor.comp_map, Functor.id_map, asIso_hom, Functor.map_comp] using
        congrArg Q.map (η.naturality f))
  let p := evaluationIso Q H D I₀ L e d r
  let ff := Localization.fullyFaithfulWhiskeringLeft Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory A)
  let j := ff.preimageIso p
  refine ⟨j, ?_⟩
  intro B k I hI
  let LB := (CochainComplex.singleFunctor A 0).obj B
  let t := (CochainComplex.singleFunctor A 0).map k
  have : I.IsKInjective := hI
  have : (I₀.obj I).IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A I
  have : QuasiIso (η.app I) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A I).2
  have hm : QuasiIso ((H.obj (op LB)).map (η.app I)) := by
    have h := quasiIso_homComplex_map (I' := I) (I := I₀.obj I) (η.app I) (𝟙 LB)
    change QuasiIso ((H.map (𝟙 (op LB))).app I ≫ (H.obj (op LB)).map (η.app I)) at h
    rw [H.map_id (op LB), NatTrans.id_app, Category.id_comp] at h
    exact h
  have : IsIso (Q.map ((H.obj (op LB)).map (η.app I))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hm
  let c := asIso (Q.map ((H.obj (op LB)).map (η.app I))) ≪≫
    (d.app (op LB, I)).symm
  refine ⟨c, ?_⟩
  have hj := congr_app (ff.map_preimage p.hom) I
  change j.hom.app (Q.obj I) = p.hom.app I at hj
  have hj' : j.hom.app (Q.obj I) =
      d.hom.app (op L, I) ≫ Q.map (e.hom.app (I₀.obj I)) ≫
        inv (Q.map (η.app I)) := by
    exact hj.trans (evaluationIso_hom_app Q H D I₀ L e d r I)
  rw [hj']
  dsimp only [c, Iso.trans_hom, asIso_hom, Iso.symm_hom]
  have : IsIso (Q.map (η.app I)) := hη I
  rw [Category.assoc]
  change Q.map ((H.obj (op LB)).map (η.app I)) ≫
      d.inv.app (op LB, I) ≫
      D.map (X := (op (Q.obj LB), Q.obj I)) (Y := (op (Q.obj L), Q.obj I))
        ((Q.map t).op, 𝟙 (Q.obj I)) ≫
      d.hom.app (op L, I) ≫ Q.map (e.hom.app (I₀.obj I)) ≫
      inv (Q.map (η.app I)) = Q.map ((H.map t.op).app I ≫ e.hom.app I)
  exact evaluation_compatibility Q H D I₀ η L e d LB I t

end AlgebraicGeometry
