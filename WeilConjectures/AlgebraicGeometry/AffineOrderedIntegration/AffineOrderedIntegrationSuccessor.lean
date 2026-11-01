/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedEvaluationContraction
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedTransposeCounit
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedFirstLineCounit

/-! # Successor calculation for the ordered integration transpose

Source: current blueprint, projection-purity agreement, final paragraph; the expanded
ordered-transpose proof, Steps 3--7.
(blueprint: lem-pur-affine-ordered-integration-successor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] orderedSource exceptional lineSource twistAction
attribute [local implicit_reducible] iteratedAffineLine iteratedAffineLineProj
attribute [local implicit_reducible] compactification proCategory etaleCategory
attribute [local implicit_reducible] rightDerivedLowerShriek
attribute [local irreducible] rightDerivedUpperShriekHomEquiv
  rightDerivedUpperShriekCounit

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

private theorem map_identity_sandwich {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (X : C) {U V W : D} (i : U ⟶ F.obj X)
    (g : F.obj X ⟶ V) (c : V ⟶ W) (f : X ⟶ X) (hf : f = 𝟙 X) :
    i ≫ F.map f ≫ g ≫ c = i ≫ g ≫ c := by
  rw [hf, F.map_id, Category.id_comp]

private theorem map_comp_postcomp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {X Y Z : C} {W : D}
    (i : X ⟶ Y) (g : Y ⟶ Z) (e : F.obj Z ⟶ W) :
    F.map i ≫ F.map g ≫ e = F.map (i ≫ g) ≫ e :=
  (Category.assoc (F.map i) (F.map g) e).symm.trans
    (congrArg (fun z ↦ z ≫ e) (F.map_comp i g).symm)

private theorem orderedSource_origin
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
      (iteratedAffineLine Y d) ((orderedSource P Y d).obj K.obj) :=
  (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (AffineLinePurity.Ring P)) _).prop_of_iso
    (sourceComparison P Y K.obj d).symm (source_origin P Y aY K Ke hKe eK d)

private theorem firstTranspose_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    letI : IsNoetherian Y := tower_noetherian P Y aY 0
    letI : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
    letI : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    integrationTranspose P Y aY K Ke hKe eK 1 =
      (sourceReassociation P Y aY K.obj 0).hom ≫
        lineComparison P Y aY K Ke hKe eK ≫
        identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  have hcon := orderedEvaluation_contraction P Y aY K Ke hKe eK
  have htrans := integrationTranspose_counit P Y aY K Ke hKe eK
  simp only [AffineLineEvaluation.counit] at htrans
  apply (rightDerivedUpperShriekHomEquiv (iteratedAffineLineProj Y 1)
    (orderedSource_origin P Y aY K Ke hKe eK 1) K.property).symm.injective
  simp only [rightDerivedUpperShriekHomEquiv_symm_apply]
  let H := AffineLineEvaluation.support P aY (iteratedAffineLineProj Y 1)
  let i := (sourceReassociation P Y aY K.obj 0).hom
  let g := lineComparison P Y aY K Ke hKe eK
  let c := identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj
  let w := (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} (AffineLinePurity.Ring P))
    (Category.comp_id (lastProjection Y 0)).symm).inv.app ((lineSource P Y).obj K.obj)
  let b := AffineLineEvaluation.standingEvaluation P Y aY K.obj Ke hKe eK
  let e := rightDerivedUpperShriekCounit (iteratedAffineLineProj Y 1) K.obj K.property
  have hce : H.map (g ≫ c) ≫ e = w ≫ b :=
    lineComposite_counit P Y aY K Ke hKe eK
  change H.map (integrationTranspose P Y aY K Ke hKe eK 1) ≫ e =
    H.map (i ≫ g ≫ c) ≫ e
  calc
    _ = H.map (sourceComparison P Y K.obj 1).hom ≫
        augmentation P Y aY K Ke hKe eK 1 := htrans 0
    _ = H.map i ≫ w ≫ b := hcon.1
    _ = H.map i ≫ (H.map (g ≫ c) ≫ e) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ H.map i ≫ z) hce.symm
    _ = H.map (i ≫ g ≫ c) ≫ e := map_comp_postcomp H i (g ≫ c) e

private theorem successor_zero (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) :
    integrationTranspose P Y aY K Ke hKe eK 1 =
      (sourceReassociation P Y aY K.obj 0).hom ≫
        (lineSource P (iteratedAffineLine Y 0)).map
          (integrationTranspose P Y aY K Ke hKe eK 0) ≫
        exceptionalLine P Y aY K Ke hKe eK 0 ≫ exceptionalComposite P Y aY K 0 := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  let : IsNoetherian (iteratedAffineLine Y 0) := tower_noetherian P Y aY 0
  let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
    HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
  have hz : integrationTranspose P Y aY K Ke hKe eK 0 = 𝟙 K.obj := by
    unfold integrationTranspose
    exact eq_of_heq
      (integrationTranspose_existsUnique P Y aY K Ke hKe eK 0).exists.choose_spec
  have he : exceptionalComposite P Y aY K 0 =
      identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj := by
    unfold exceptionalComposite
    exact eq_of_heq (exceptionalComposite_existsUnique P Y aY K 0).exists.choose_spec
  have hline0 : exceptionalLine P Y aY K Ke hKe eK 0 =
      lineComparison P Y aY K Ke hKe eK := by
    unfold exceptionalLine
    (simp only [towerBase, iteratedAffineLineProj]; rfl)
  rw [hline0, he]
  refine Eq.trans ?_ (map_identity_sandwich
    (lineSource P (iteratedAffineLine Y 0)) K.obj
    (sourceReassociation P Y aY K.obj 0).hom
    (lineComparison P Y aY K Ke hKe eK)
    (identityCompositeMap (AffineLinePurity.Ring P) (lastProjection Y 0) K.obj)
    (integrationTranspose P Y aY K Ke hKe eK 0) hz).symm
  exact firstTranspose_eq P Y aY K Ke hKe eK

private theorem successor_positive (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    integrationTranspose P Y aY K Ke hKe eK (d + 2) =
      (sourceReassociation P Y aY K.obj (d + 1)).hom ≫
        (lineSource P (iteratedAffineLine Y (d + 1))).map
          (integrationTranspose P Y aY K Ke hKe eK (d + 1)) ≫
        exceptionalLine P Y aY K Ke hKe eK (d + 1) ≫ exceptionalComposite P Y aY K (d + 1) := by
  let : IsNoetherian Y := tower_noetherian P Y aY 0
  have hcon := orderedEvaluation_contraction P Y aY K Ke hKe eK
  have htrans := integrationTranspose_counit P Y aY K Ke hKe eK
  simp only [AffineLineEvaluation.counit] at htrans
  let : IsNoetherian (iteratedAffineLine Y (d + 1)) :=
    tower_noetherian P Y aY (d + 1)
  let : IsSeparated (iteratedAffineLineProj Y (d + 1)) :=
    (projection_geometry Y (d + 1)).1
  let : HasCompactification (iteratedAffineLineProj Y (d + 1)) :=
    (projection_geometry Y (d + 1)).2
  let : HasCompactification (iteratedAffineLineProj Y (d + 2)) :=
    (projection_geometry Y (d + 2)).2
  let : HasCompactification
      (lastProjection Y (d + 1) ≫ iteratedAffineLineProj Y (d + 1)) :=
    HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2))
      (iteratedAffineLineProj_succ Y (d + 1))
  let : LocallyOfFiniteType (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).1
  let : QuasiCompact (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.1
  let : IsSeparated (towerBase aY (d + 1)) := (tower_geometry aY (d + 1)).2.2
  have he : exceptionalComposite P Y aY K (d + 1) =
      compositionInverse (AffineLinePurity.Ring P) (lastProjection Y (d + 1))
        (iteratedAffineLineProj Y (d + 1)) K := by
    unfold exceptionalComposite
    exact eq_of_heq
      (exceptionalComposite_existsUnique P Y aY K (d + 1)).exists.choose_spec
  have hc := AffineLineEvaluation.composite_transpose P aY
    (iteratedAffineLineProj Y (d + 1)) ((orderedSource P Y (d + 1)).obj K.obj)
    (sourceEtale P Y Ke (d + 1)) (source_applicability P Y aY K Ke hKe eK (d + 1)).2
    (sourceRealization P Y K.obj Ke eK (d + 1)) K Ke hKe eK
    (integrationTranspose P Y aY K Ke hKe eK (d + 1))
  simp only [AffineLineEvaluation.counit] at hc
  have hw : (lineSource P (iteratedAffineLine Y (d + 1))).map
        (integrationTranspose P Y aY K Ke hKe eK (d + 1)) ≫
      exceptionalLine P Y aY K Ke hKe eK (d + 1) ≫
      exceptionalComposite P Y aY K (d + 1) =
    AffineLineEvaluation.theta P aY (iteratedAffineLineProj Y (d + 1))
      ((orderedSource P Y (d + 1)).obj K.obj) K Ke hKe eK
      (integrationTranspose P Y aY K Ke hKe eK (d + 1)) := by
    rw [he]
    unfold AffineLineEvaluation.theta AffineLineEvaluation.inverseConjugate
    rfl
  rw [hw]
  apply (rightDerivedUpperShriekHomEquiv (iteratedAffineLineProj Y (d + 2))
    (orderedSource_origin P Y aY K Ke hKe eK (d + 2)) K.property).symm.injective
  simp only [rightDerivedUpperShriekHomEquiv_symm_apply]
  let H := AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 2))
  let G := AffineLineEvaluation.support P aY (iteratedAffineLineProj Y (d + 1))
  let i := (sourceReassociation P Y aY K.obj (d + 1)).hom
  let theta := AffineLineEvaluation.theta P aY (iteratedAffineLineProj Y (d + 1))
    ((orderedSource P Y (d + 1)).obj K.obj) K Ke hKe eK
    (integrationTranspose P Y aY K Ke hKe eK (d + 1))
  let alpha := (AffineLineEvaluation.compositor P aY (iteratedAffineLineProj Y (d + 1))
    ((orderedSource P Y (d + 1)).obj K.obj) (sourceEtale P Y Ke (d + 1))
    (source_applicability P Y aY K Ke hKe eK (d + 1)).2
    (sourceRealization P Y K.obj Ke eK (d + 1))).inv
  let b := G.map (AffineLineEvaluation.standingEvaluation P (iteratedAffineLine Y (d + 1))
    (towerBase aY (d + 1)) ((orderedSource P Y (d + 1)).obj K.obj)
    (sourceEtale P Y Ke (d + 1)) (source_applicability P Y aY K Ke hKe eK (d + 1)).2
    (sourceRealization P Y K.obj Ke eK (d + 1)))
  let s := G.map (sourceComparison P Y K.obj (d + 1)).hom
  let t := G.map (integrationTranspose P Y aY K Ke hKe eK (d + 1))
  let e := rightDerivedUpperShriekCounit (iteratedAffineLineProj Y (d + 1)) K.obj K.property
  let e' := rightDerivedUpperShriekCounit (iteratedAffineLineProj Y (d + 2)) K.obj K.property
  change H.map (integrationTranspose P Y aY K Ke hKe eK (d + 2)) ≫ e' =
    H.map (i ≫ theta) ≫ e'
  calc
    _ = H.map (sourceComparison P Y K.obj (d + 2)).hom ≫
        augmentation P Y aY K Ke hKe eK (d + 2) := htrans (d + 1)
    _ = H.map i ≫ alpha ≫ b ≫ s ≫ augmentation P Y aY K Ke hKe eK (d + 1) :=
      hcon.2 d
    _ = H.map i ≫ alpha ≫ b ≫ t ≫ e := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ H.map i ≫ alpha ≫ b ≫ z) (htrans d).symm
    _ = H.map i ≫ (H.map theta ≫ e') := by
      simpa only [H, G, theta, alpha, b, t, e, e', AffineLineEvaluation.support,
        towerBase, iteratedAffineLineProj, iteratedAffineLine, Category.assoc] using
        congrArg (fun z ↦ H.map i ≫ z) hc.symm
    _ = H.map (i ≫ theta) ≫ e' := map_comp_postcomp H i theta e'

/-- Adding the last coordinate transposes the ordered trace contraction using the actual
compact-support compositor. This is only the successor equation: it assumes neither
agreement with the recursively defined comparison nor invertibility or naturality.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-smooth-purity/
lem-pur-projection-purity-agreement.proof.md, final paragraph, expanded ordered-transpose
proof Steps 3--7 (blueprint: lem-pur-affine-ordered-integration-successor).

Proof: use the inverse of the existing restricted exceptional Hom bijection. The
unique-HEq specification of integrationTranspose and the inverse-Hom formula identify
its image at each positive stage with sourceComparison followed by augmentation.
Transport of source_origin supplies the Hom bijection at the ordered source. For a
positive preceding dimension, composite_transpose identifies the inverse transpose
of the displayed composite with the compact-support composite of the line evaluation
and the preceding transpose. The second equation of orderedEvaluation_contraction,
functoriality, and the preceding inverse-transpose formula identify this with the
next augmentation. At zero the preceding transpose is the identity. The first
contraction equation, lineComparison_counit, and compatibility of the counit with
equality transport give the required identityCompositeMap normalization. This last
compatibility is proved by substitution. Injectivity of the inverse Hom bijection
concludes in both cases. The two evaluation identities retain their independent
ordinary-site coefficient and site-comparison proofs as named lower obligations. -/
theorem integrationTranspose_successor (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (AffineLinePurity.Ring P) Y)
    (Ke : Etale.DerivedCategoryModule (AffineLinePurity.Ring P) Y)
    (hKe : etaleFiniteTor (AffineLinePurity.Ring P) Y Ke)
    (eK : (comparison (AffineLinePurity.Ring P) Y).obj Ke ≅ K.obj) (d : ℕ) :
    integrationTranspose P Y aY K Ke hKe eK (d + 1) =
      (sourceReassociation P Y aY K.obj d).hom ≫
        (lineSource P (iteratedAffineLine Y d)).map
          (integrationTranspose P Y aY K Ke hKe eK d) ≫
        exceptionalLine P Y aY K Ke hKe eK d ≫ exceptionalComposite P Y aY K d := by
  cases d with
  | zero => exact successor_zero P Y aY K Ke hKe eK
  | succ d => exact successor_positive P Y aY K Ke hKe eK d

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
