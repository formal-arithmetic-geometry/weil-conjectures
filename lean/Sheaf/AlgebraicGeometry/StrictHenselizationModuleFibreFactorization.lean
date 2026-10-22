/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.BaseChange.GlobalSections
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Sheaf.AlgebraicGeometry.EtaleUnitSectionRestriction
import Sheaf.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison

/-! # Factoring fibre restrictions through strict henselization sections

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Etale
open Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The compatible marked maps give a ring cocone and hence a map to its spectrum.
The colimit coprojection formula gives the pointed limit-leg equations (Stacks Tag 04HX). -/
private theorem pointedStrictHenselizationLift
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Y) :
    ∃ t : Spec (.of Ω) ⟶ strictHenselizationScheme s,
      t ≫ strictHenselizationStructuralMap s = s ∧
      ∀ j : SmallModel.{u} (strictHenselizationNeighbourhoods s),
        t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
          Spec.map (ΓSpecIso
            ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
              j).1.left.unop).inv =
          ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj
            j).2.left := by
  classical
  let N := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
  let c : Cone ((strictHenselizationAffineDiagram s).op ⋙ Scheme.Spec) :=
    { pt := Spec (.of Ω)
      π :=
        { app := fun j ↦ (N.obj j.unop.unop).2.left ≫
            (Spec (N.obj j.unop.unop).1.left.unop).toSpecΓ
          naturality := by
            intro j k a
            dsimp
            rw [Category.id_comp]
            symm
            change (N.obj j.unop.unop).2.left ≫
              (Spec (N.obj j.unop.unop).1.left.unop).toSpecΓ ≫
                Spec.map (Spec.map (N.map a.unop.unop).1.left.unop).appTop = _
            let g := Spec.map (N.map a.unop.unop).1.left.unop
            have hw : (N.obj j.unop.unop).2.left ≫ g = (N.obj k.unop.unop).2.left :=
              congrArg Over.Hom.left (N.map a.unop.unop).2
            exact (congrArg (fun h ↦ (N.obj j.unop.unop).2.left ≫ h)
              (Scheme.toSpecΓ_naturality g).symm).trans
                ((Category.assoc _ _ _).symm.trans
                  (congrArg
                    (fun v ↦ v ≫ (Spec (N.obj k.unop.unop).1.left.unop).toSpecΓ) hw)) } }
  let hc := (strictHenselization_properties s).2.2.some
  let t : Spec (.of Ω) ⟶ strictHenselizationScheme s := hc.lift c
  have hpoint (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      t ≫ (strictHenselizationCone s).π.app (op (op j)) ≫
        Spec.map (ΓSpecIso (N.obj j).1.left.unop).inv = (N.obj j).2.left := by
    rw [← Category.assoc, hc.fac c]
    change ((N.obj j).2.left ≫ _) ≫ _ = _
    rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv]
    exact Category.comp_id _
  refine ⟨t, ?_, hpoint⟩
  let := (strictHenselization_properties s).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods s)))
  have hstruct := (exists_strictHenselizationStructuralMap s).choose_spec j
  change _ = strictHenselizationStructuralMap s at hstruct
  rw [← hstruct]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg
      (fun v ↦ v ≫ ((AffineEtale.Spec Y).obj (N.obj j).1).hom) (hpoint j)).trans
        (N.obj j).2.w)

-- The existing existential witness `ht` is intentionally unused in the statement.
set_option linter.unusedVariables false in
set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- The module stalk comparison with strict henselization sections, together with
its compatibility with restriction to the given geometric fibre. This assertion
uses no integral or proper hypothesis.

Source: Stacks Project, Tags 03Q9, 03Q1 and 04HX.
(blueprint: lem-sbc-strict-henselization-module-fibre-factorization).

Proof: The marked maps from Spec Omega to all affine pointed neighbourhoods form
a cone. Its unique lift t to their limit is compatible with the structural map.
The closed-fibre theorem for the strict henselization applies to t's image:
its composite with the structural map has image s's point, so that image is the
closed point of the strict henselization.
Pull back X to this limit. Tag 03Q9 identifies its sections with the direct-image
stalk. Apply the module-to-set inverse-image comparison and its unit equation to
the set-valued stalk formula. Since the set comparison and all restriction maps
commute with addition and scalar multiplication, the bijective comparison is a
module isomorphism Theta. Affine pointed neighbourhoods are cofinal, so its
formula extends to every V and v. The pullback lift i has composite g' with the
projection to X. The inverse-image composition isomorphism therefore identifies
i^* q^* F with g'^* F. Global sections followed by the canonical isomorphism to
evaluation at the identity object gives b. Naturality of the units and their
composition equation show that b after restriction along i after Theta takes a
representative z to the unit image restricted along geometricFibreSectionLift:
both lifts have projections f' followed by v and g', so pullback uniqueness makes
them equal. This is the displayed formula, without any injectivity assertion
about restriction along i. All constructions also apply to an empty X. -/
theorem strictHenselizationModuleFibre_factorization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s)
    [QuasiCompact f] [QuasiSeparated f]
    [IsLocalRing (strictHenselizationRing s)]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ (t : Spec (.of Ω) ⟶ strictHenselizationScheme s)
      (ht : t ≫ strictHenselizationStructuralMap s = s),
      t (IsLocalRing.closedPoint Ω) =
        IsLocalRing.closedPoint (strictHenselizationRing s) ∧
      ∃ (i : X' ⟶ pullback f (strictHenselizationStructuralMap s)),
        IsPullback i f' (pullback.snd f (strictHenselizationStructuralMap s)) t ∧
        i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g' ∧
      ∃ Θ : (pointSmallEtale s).sheafFiber.obj ((f)_*[ModuleCat.{u + 1} Λ].obj F) ≅
          (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F),
      ∃ b : (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).obj
          ((i)^*[ModuleCat.{u + 1} Λ].obj
            ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)) ≅
          ((g')^*[ModuleCat.{u + 1} Λ].obj F).obj.obj (op (Scheme.Etale.mk (𝟙 X'))),
      ∀ (V : Y.Etale) (v : (pointSmallEtale s).fiber.obj V)
        (z : F.obj.obj (op (f.Etale.obj V))),
        b.hom.hom ((globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((pullback.fst f (strictHenselizationStructuralMap s))^*[ModuleCat.{u + 1} Λ].obj F)).hom
          (Θ.hom.hom ((pointSmallEtale s).toPresheafFiber V v
            ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj z))) =
        (geometricFibreSectionRestriction Λ sq.toCommSq F V v).hom z := by
  classical
  obtain ⟨t, ht, hpoint⟩ := pointedStrictHenselizationLift s
  have htclosed : t (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint (strictHenselizationRing s) := by
    apply strictHenselizationStructuralMap_fiber_eq_closedPoint_compat
      (A := strictHenselizationRing s) s (Iso.refl _)
      (t (IsLocalRing.closedPoint Ω))
    change (t ≫ strictHenselizationStructuralMap s) (IsLocalRing.closedPoint Ω) = _
    rw [ht]
  let i := pullback.lift g' (f' ≫ t) (sq.w.trans (by rw [Category.assoc, ht]))
  have hi : i ≫ pullback.fst f (strictHenselizationStructuralMap s) = g' :=
    pullback.lift_fst _ _ _
  have hit : i ≫ pullback.snd f (strictHenselizationStructuralMap s) = f' ≫ t :=
    pullback.lift_snd _ _ _
  have hcart : IsPullback i f'
      (pullback.snd f (strictHenselizationStructuralMap s)) t := by
    apply IsPullback.of_right (s := ?_) hit (IsPullback.of_hasPullback _ _)
    simpa only [hi, ht] using sq
  obtain ⟨Θ₀, hΘ₀⟩ := exists_qcqsStrictLocalModuleComparison Λ f s F
  let ps := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let pb := pullback.fst f (Scheme.strictLocalizationToBase s)
  let τ := pullback.map f (Scheme.strictHenselizationStructuralMap s)
    f (Scheme.strictLocalizationToBase s) (𝟙 X)
    (Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv) (𝟙 Y)
    (by simp) (by simpa using (Scheme.smallStrictLocalization_toBase s).symm)
  have : IsIso τ := by dsimp [τ]; infer_instance
  have hp : ps = τ ≫ pb := by simp [τ, ps, pb]
  let eΓ := globalSectionsUpperStarIso (ModuleCat.{u + 1} Λ) τ
    ((upperStar (ModuleCat.{u + 1} Λ) pb).obj F) ≪≫
    (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).mapIso
      (((upperStarComp (ModuleCat.{u + 1} Λ) τ pb ps hp).app F).symm)
  let Θ := Θ₀ ≪≫ eΓ
  have hΘ (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)) :
      (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2
        ((lowerStar (ModuleCat.{u + 1} Λ) f).obj F).obj ≫ Θ.hom =
      unitSectionRestriction Λ ps F
        (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
        ((pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
          Scheme.smallStrictHenselizationBaseChangeMap f s j)
        (by
          change _ ≫ pullback.snd _ f =
            pullback.fst f (Scheme.strictHenselizationStructuralMap s)
          simp only [Category.assoc, Scheme.smallStrictHenselizationBaseChangeMap_snd,
          pullbackSymmetry_hom_comp_snd]) := by
    have hj := hΘ₀ j
    have hu : qcqsStrictLocalSectionRestriction Λ f s F j =
        unitSectionRestriction Λ pb F
          (f.Etale.obj ((Scheme.AffineEtale.Spec Y).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1))
          ((pullbackSymmetry f (Scheme.strictLocalizationToBase s)).hom ≫
            Scheme.strictHenselizationBaseChangeMap f s j)
          (by
            change _ ≫ pullback.snd _ f = pullback.fst f (Scheme.strictLocalizationToBase s)
            simp [Scheme.strictHenselizationBaseChangeMap, Category.assoc]) := by rfl
    rw [hu] at hj
    simp only [Θ, Iso.trans_hom]
    rw [reassoc_of% hj]
    change unitSectionRestriction Λ pb F _ _ _ ≫
      globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) τ _ ≫
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) τ pb ps hp).inv.app F) = _
    rw [unitSectionRestriction_comp]
    congr 1
    simp only [Scheme.smallStrictHenselizationBaseChangeMap]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [τ, Category.assoc]
  let H := (upperStar (ModuleCat.{u + 1} Λ)
    (pullback.fst f (strictHenselizationStructuralMap s))).obj F
  let H' := (upperStar (ModuleCat.{u + 1} Λ) g').obj F
  let P := (lowerStar (ModuleCat.{u + 1} Λ) f').obj H'
  let eX := (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
      (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).app H'
  let eΩ := (Sheaf.ΓNatIsoSheafSections _ _
    (IsTerminal.isTerminalOfObj
      (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).app P
  let j := (pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
    (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
    (Over.homMk (𝟙 _) (Category.comp_id _)) P.obj
  have : IsIso j := by
    let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
    let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
    let v : Φ.fiber.obj T := Over.homMk (𝟙 _) (Category.comp_id _)
    let n := Functor.elementsMk Φ.fiber T v
    let lift (m : Φ.fiber.Elements) : n ⟶ m :=
      ⟨MorphismProperty.Over.homMk m.2.left m.2.w, by
        apply Over.OverMorphism.ext
        exact Category.id_comp _⟩
    have hn : IsInitial n := IsInitial.ofUniqueHom lift (fun m a ↦ by
      apply Subtype.ext
      apply MorphismProperty.Over.Hom.ext
      have h := congrArg Over.Hom.left a.2
      change (𝟙 _) ≫ a.1.left = m.2.left at h
      exact (Category.id_comp _).symm.trans h)
    exact (Φ.isColimitPresheafFiberCocone P.obj).isIso_ι_app_of_isTerminal (op n) hn.op
  let d := eX.symm ≪≫ ((lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').app
    H').symm ≪≫ eΩ ≪≫ asIso j
  let b := (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).mapIso
    (((upperStarComp (ModuleCat.{u + 1} Λ) i
      (pullback.fst f (strictHenselizationStructuralMap s)) g' hi.symm).app F).symm) ≪≫ eX
  refine ⟨t, ht, htclosed, i, hcart, hi, Θ, b, ?_⟩
  have hpoint' : ∀ k : SmallModel.{u} (strictHenselizationNeighbourhoods s),
      t ≫ (strictHenselizationCone s).π.app (op (op k)) ≫
        (Spec (unop ((equivSmallModel.{u}
          (strictHenselizationNeighbourhoods s)).inverse.obj k).1.left)).isoSpec.inv =
        ((equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse.obj k).2.left := by
    simpa only [Scheme.isoSpec_Spec_inv] using hpoint
  let e := geometricPointSourceStalkIso Λ s ((f)_*[ModuleCat.{u + 1} Λ].obj F)
  have hc' : (pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.map
      ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F) =
      e.hom ≫ Θ.hom ≫ globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i H ≫
        b.hom ≫ d.hom := by
    simp only [b, d, eX, eΩ, j, H, H', P,
      Functor.mapIso_hom, Iso.symm_hom, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
      asIso_hom, Category.assoc, Iso.hom_inv_id_app_assoc]
    let P := (lowerStar (ModuleCat.{u + 1} Λ) f).obj F
    let e := geometricPointSourceStalkIso Λ s P
    let r := globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i
          ((upperStar (ModuleCat.{u + 1} Λ)
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj F) ≫
        (Sheaf.Γ _ (ModuleCat.{u + 1} Λ)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) i
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) g' hi.symm).inv.app F)
    let b := (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} Λ) f').inv.app
          ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) ≫
        (Sheaf.ΓNatIsoSheafSections _ _
          (IsTerminal.isTerminalOfObj
            (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ (Spec (.of Ω)))
            (Scheme.Etale.mk (𝟙 (Spec (.of Ω)))) Over.mkIdTerminal)).hom.app
              ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
                ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)) ≫
        (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
          (Over.homMk (𝟙 _) (Category.comp_id _))
          ((lowerStar (ModuleCat.{u + 1} Λ) f').obj
            ((upperStar (ModuleCat.{u + 1} Λ) g').obj F)).obj
    change _ = e.hom ≫ Θ.hom ≫ r ≫ b
    apply (Iso.inv_comp_eq e).1
    let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    have : N.Initial := (Scheme.strictHenselization_properties s).1
    let c := ((Scheme.pointSmallEtale s).presheafFiberCocone P.obj).whisker N.op
    let hc : IsColimit c :=
      (Functor.Final.isColimitWhiskerEquiv N.op _).symm
        ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone P.obj)
    apply hc.hom_ext
    intro j
    change (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫
      (e.inv ≫ _) = (Scheme.pointSmallEtale s).toPresheafFiber _ _ P.obj ≫ (Θ.hom ≫ r ≫ b)
    have he := exchange_pointed_representative Λ sq.toCommSq F
      ((Scheme.AffineEtale.Spec Y).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1)
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2
    let V := (Scheme.AffineEtale.Spec Y).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).1
    let v := ((equivSmallModel.{u}
      (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j.unop).2
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let l := (pullbackSymmetry f (Scheme.strictHenselizationStructuralMap s)).hom ≫
      Scheme.smallStrictHenselizationBaseChangeMap f s j.unop
    have hl : l ≫ (f.Etale.obj V).hom = p := by
      change l ≫ pullback.snd _ f = p
      simp only [l, p, Category.assoc,
        Scheme.smallStrictHenselizationBaseChangeMap_snd, pullbackSymmetry_hom_comp_snd]
    have hr := unitSectionRestriction_comp Λ i p g' hi.symm F (f.Etale.obj V) l hl
    have hg : etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
        (by rw [Category.assoc, hl, ← hi]) = geometricFibreSectionLift sq.toCommSq V v := by
      apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext
      · simp only [etaleSectionGraph, geometricFibreSectionLift,
          MorphismProperty.Over.homMk_hom, Over.homMk_left, pullback.lift_fst]
        apply pullback.hom_ext
        · simp only [l, Category.assoc, pullback.lift_fst]
          rw [Scheme.smallStrictHenselizationBaseChangeMap_fst]
          simp only [← Category.assoc, pullbackSymmetry_hom_comp_fst]
          rw [hit]
          simp only [Category.assoc]
          rw [← Scheme.isoSpec_Spec_inv, hpoint' j.unop]
        · simp only [pullback.lift_snd]
          change (i ≫ l) ≫ (f.Etale.obj V).hom = g'
          rw [Category.assoc, hl, hi]
      · exact (etaleSectionGraph g' (f.Etale.obj V) (i ≫ l)
          (by rw [Category.assoc, hl, ← hi])).w.trans
          (geometricFibreSectionLift sq.toCommSq V v).w.symm
    have heq : unitSectionRestriction Λ g' F (f.Etale.obj V) (i ≫ l)
        (by rw [Category.assoc, hl, ← hi]) =
        geometricFibreSectionRestriction Λ sq.toCommSq F V v ≫
          (Sheaf.ΓNatIsoSheafSections _ _
            (IsTerminal.isTerminalOfObj
              (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ X')
              (Scheme.Etale.mk (𝟙 X')) Over.mkIdTerminal)).inv.app
                ((upperStar (ModuleCat.{u + 1} Λ) g').obj F) := by
      unfold unitSectionRestriction
      rw [hg]
      rfl
    have hr := hr.trans heq
    have h := congrArg (fun k ↦ k ≫ r ≫ b) (hΘ j.unop)
    simpa only [r, b, e, P, N, Scheme.strictHenselizationAffineInclusion,
      Functor.comp_obj, Functor.op_obj, ObjectProperty.ι, ObjectProperty.lift,
      Functor.Elements.precomp, inducedFunctor, Functor.elementsMk, Category.assoc] using
      (he.trans (congrArg (fun k ↦ k ≫ b) hr).symm).trans h.symm
  intro V v z
  have hrep := exchange_pointed_representative Λ sq.toCommSq F V v
  change (pointSmallEtale s).toPresheafFiber V v
    ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj ≫ e.inv ≫ _ =
      geometricFibreSectionRestriction Λ sq.toCommSq F V v ≫ d.hom at hrep
  rw [hc'] at hrep
  simp only [Iso.inv_hom_id_assoc] at hrep
  have h : (pointSmallEtale s).toPresheafFiber V v
      ((f)_*[ModuleCat.{u + 1} Λ].obj F).obj ≫ Θ.hom ≫
        globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) i H ≫ b.hom =
      geometricFibreSectionRestriction Λ sq.toCommSq F V v := by
    apply (cancel_mono d.hom).1
    simpa only [Category.assoc] using hrep
  exact congrArg (fun k ↦ k.hom z) h

end AlgebraicGeometry.Etale
