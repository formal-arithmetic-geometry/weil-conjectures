/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection
import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
import all Sheaf.SixFunctors.EtaleOpenTensorDefs

/-! # Local tensor normalization of the canonical étale scalar comparisons

Source: Stacks Project, etale-cohomology.tex, Tags 03S3 and 03S4;
sites-modules.tex, Tags 03EL and 0GMW.
(blueprint: lem-sp-etale-scalar-section-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The sum/scalar comparison determined by the two composite adjunctions.
Its right-adjoint comparison is the specified inverse-image/restriction-of-scalars
isomorphism. No section or existential witness is chosen.
Source: Stacks, Tags 03S3, 03S4 and 03EL
(blueprint: lem-sp-etale-scalar-section-normalization). -/
def etaleSumScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance ⋙
        ProEtale.etaleSheafExtendScalars φ V ≅
      ProEtale.etaleSheafExtendScalars φ U ⋙
        etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance :=
  ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
      (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
        (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) e inferInstance)).ofNatIsoRight
          (upperStarRestrictScalarsIsoSheaf φ e).symm)

open MonoidalCategory

private lemma tensor_section_map (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {M M' N N' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : M ⟶ M') (g : N ⟶ N') (W : T.Etale)
    (m : M.obj.obj (op W)) (n : N.obj.obj (op W)) :
    (f ⊗ₘ g).hom.app (op W) (etaleSheafTensorSection A M N W m n) =
      etaleSheafTensorSection A M' N' W (f.hom.app (op W) m) (g.hom.app (op W) n) := by
  let := (sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  have h := Functor.LaxMonoidal.μ_natural
    (F := sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) f g
  have hW := congrArg (fun t ↦ t.app (op W) (m ⊗ₜ[A] n)) h
  change (Functor.LaxMonoidal.μ
    (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) M' N').app (op W)
      ((f.hom.app (op W) ⊗ₘ g.hom.app (op W)) (m ⊗ₜ[A] n)) =
    (f ⊗ₘ g).hom.app (op W) (etaleSheafTensorSection A M N W m n) at hW
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul] at hW
  exact hW.symm

private lemma restrict_tensor_section
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T : Scheme.{u}}
    (M N : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) (W : T.Etale)
    (m : M.obj.obj (op W)) (n : N.obj.obj (op W)) :
    (Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) M N).hom.app
        (op W) (etaleSheafTensorSection A
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj M)
          ((Sheaf.restrictScalars T.smallEtaleTopology φ).obj N) W m n) =
      etaleSheafTensorSection B M N W m n := by
  let := (sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} A)).rightAdjointLaxMonoidal
  let := (sheafificationAdjunction T.smallEtaleTopology
    (ModuleCat.{u + 1} B)).rightAdjointLaxMonoidal
  have h := μ_sheafToPresheaf_comp_map_μ_sheafCompose T.smallEtaleTopology
    (ModuleCat.restrictScalars φ) M N
  have hW := congrArg (fun t ↦ t.app (op W) (m ⊗ₜ[A] n)) h
  change _ = ((ModuleCat.restrictScalars φ).map
    ((Functor.LaxMonoidal.μ (sheafToPresheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} B)) M N).app (op W)))
        ((Functor.LaxMonoidal.μ (ModuleCat.restrictScalars φ)
          (M.obj.obj (op W)) (N.obj.obj (op W))) (m ⊗ₜ[A] n)) at hW
  rw [ModuleCat.restrictScalars_μ_tmul] at hW
  exact hW

private lemma scalar_tensor_section
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {T : Scheme.{u}}
    (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : T.Etale)
    (m : M.obj.obj (op W)) (b : (scalarCoefficientSheaf φ T).obj.obj (op W)) :
    compactificationScalarTensorSection φ M W m b =
      (ρ_ ((ProEtale.etaleSheafExtendScalars φ T).obj M)).hom.hom.app (op W)
        (etaleSheafTensorSection B ((ProEtale.etaleSheafExtendScalars φ T).obj M)
          (𝟙_ _) W
          (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M).hom.app (op W) m)
          b) := by
  unfold compactificationScalarTensorSection scalarSheafTensorMap
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply]
  rw [show (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M ▷
      scalarCoefficientSheaf φ T =
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M ⊗ₘ
        𝟙 (scalarCoefficientSheaf φ T) from (tensorHom_id _ _).symm]
  have ht := tensor_section_map A
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M)
      (𝟙 (scalarCoefficientSheaf φ T)) W m b
  let L := (ProEtale.etaleSheafExtendScalars φ T).obj M
  let r := (Sheaf.restrictScalars T.smallEtaleTopology φ).map (ρ_ L).hom
  let μ := Functor.LaxMonoidal.μ (Sheaf.restrictScalars T.smallEtaleTopology φ) L (𝟙_ _)
  exact (congrArg (fun z ↦ r.hom.app (op W) (μ.hom.app (op W) z)) ht).trans
    (congrArg (r.hom.app (op W))
      (restrict_tensor_section φ L (𝟙_ _) W
        (((ProEtale.etaleSheafExtendScalarsAdjunction φ T).unit.app M).hom.app (op W) m) b))

private def foldRestrictionScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    upperStar (ModuleCat.{u + 1} B) j ⋙ Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙ upperStar (ModuleCat.{u + 1} A) j :=
  Functor.isoWhiskerRight
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} B) j inferInstance) _ ≪≫
    (show localizationRestriction (ModuleCat.{u + 1} B) j inferInstance ⋙
        Sheaf.restrictScalars U.smallEtaleTopology φ ≅
      Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        localizationRestriction (ModuleCat.{u + 1} A) j inferInstance from
      NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)) ≪≫
    Functor.isoWhiskerLeft _
      (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) j inferInstance).symm

private theorem localization_scalar_comparison
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (foldRestrictionScalarIso φ j).inv = (upperStarRestrictScalarsIsoSheaf φ j).hom := by
  let a := Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ
  let b := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j
  let c := upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) j
  let d := Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ
  let b' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j inferInstance
  let c' := localizationRestrictionLowerStarAdjunction (ModuleCat.{u + 1} B) j inferInstance
  have hadj : a.comp b' = c'.comp d := by
    apply Adjunction.ext
    apply NatTrans.ext
    funext M
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change ((a.comp b').unit.app M).hom.app V = ((c'.comp d).unit.app M).hom.app V
    simp only [Adjunction.comp_unit_app]
    dsimp only [a, b', c', d]
    let siteAdj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j
      (inferInstance : Etale j) trivial
    let t := M.obj.map (siteAdj.counit.app V.unop).op
    change ((Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.app M).hom.app V ≫
        (ModuleCat.coextendScalars φ).map ((ModuleCat.restrictScalars φ).map t) =
      t ≫ ((Sheaf.restrictCoextendScalarsAdj U.smallEtaleTopology φ).unit.app
        ((localizationRestriction (ModuleCat B) j inferInstance).obj M)).hom.app _
    rw [restrictCoextendScalarsAdj_unit_app_hom_app,
      restrictCoextendScalarsAdj_unit_app_hom_app]
    exact ((ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).unit.naturality t).symm
  change _ = ((a.comp b).leftAdjointUniq (c.comp d)).hom
  calc
    (foldRestrictionScalarIso φ j).inv =
        ((a.comp b).leftAdjointUniq (a.comp b')).hom ≫
          ((c'.comp d).leftAdjointUniq (c.comp d)).hom := by
      have hleft := leftUniq_whiskerLeft a b b'
      have hright := leftUniq_whiskerRight c' c d
      have hcomp := congrArg₂ (fun f g ↦ f ≫ g) hleft hright
      refine Eq.trans ?_ hcomp.symm
      ext M
      simp only [foldRestrictionScalarIso, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerRight_inv, Iso.symm_inv, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatIso.ofComponents_inv_app,
        Iso.refl_inv, upperStarIsoLocalizationRestriction]
      rfl
    _ = _ := by
      rw [← hadj, Adjunction.leftAdjointUniq_trans]


/-- The canonical sum/scalar and scalar/pullback comparisons preserve local pure
sections, including arbitrary sections of the constant coefficient sheaf.
Source: Stacks, Tags 03S3, 03S4, 03EL and 0GMW
(blueprint: lem-sp-etale-scalar-section-normalization).

Proof: Identify geometric inverse image along the étale map with restriction along
composition of étale test objects. Under this identification, restriction of scalars
commutes with restriction of test objects by the identity. The comparison used in
etaleSumScalarIso is this identity transported through the inverse-image isomorphisms:
this follows by uniqueness of left adjoints, using the restriction/coextension
adjunction and the naturality of its sectionwise unit.

The unit equation for left-adjoint uniqueness now says that the sum/scalar comparison
sends the scalar unit of a single sum section to the sum of the scalar unit of that
section. The scalar tensor map is the scalar unit tensored with the coefficient
sheaf, followed by the lax monoidal map for restriction of scalars and the right
unitor. These operations commute with restriction of test objects and with the sum
unit. Applying the unit equation to that bilinear pairing gives the first formula.
Equivalently, extend the pairing from individual summands through sheafification;
bilinear sheafification uniqueness identifies it with this adjunction comparison.

The scalar/pullback comparison is the inverse scalar mate of the same restriction
identity. Its unit equation, applied to the same bilinear pairing, gives the second
formula. The coefficient factor is the specified inverse-image comparison at the
unit object, followed by the inverse monoidal unit map; hence it is exactly
compactificationCoefficientPullbackIso, rather than a choice of coefficient
identification. Naturality of the sheaf tensor pairing and of the scalar unit gives
both formulas for arbitrary local coefficient sections. Empty tests and zero rings
are covered by these linear identities; no flatness or finiteness is used. -/
theorem etaleSumScalarIso_tensorSections
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
      (∀ (H : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (x : H.obj.obj (op W))
        (b : (scalarCoefficientSheaf φ V).obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
        ((etaleSumScalarIso φ e).hom.app H).hom.app
            (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))
            (compactificationScalarTensorSection φ _
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)
              (etaleSumSection A e H W x) b) =
          etaleSumSection B e ((ProEtale.etaleSheafExtendScalars φ U).obj H) W
            (compactificationScalarTensorSection φ H W x
              ((compactificationCoefficientPullbackIso φ e).hom.hom.app (op W)
                (etaleLiftSection A e (scalarCoefficientSheaf φ V) W b)))) ∧
      (∀ (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (x : F.obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W)))
        (b : (scalarCoefficientSheaf φ V).obj.obj
          (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W))),
        ((scalarSheafPullbackIso φ e).inv.app F).hom.app (op W)
            (compactificationScalarTensorSection φ _ W (etaleLiftSection A e F W x)
              ((compactificationCoefficientPullbackIso φ e).hom.hom.app (op W)
                (etaleLiftSection A e (scalarCoefficientSheaf φ V) W b))) =
          etaleLiftSection B e ((ProEtale.etaleSheafExtendScalars φ V).obj F) W
            (compactificationScalarTensorSection φ F
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale e)).obj W) x b)) := by
  sorry

end AlgebraicGeometry.Etale
