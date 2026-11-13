/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Sites.LocallySurjective

import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAbelianLiftHom
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageSmallUniverse
import Mathlib.Algebra.Category.Grp.Ulift

/-! # The underlying-set Kan comparison for an abelian inverse image

Source: Stacks Project, Tags 00YV, 09XN, and 00WK. -/

@[expose] public section

universe u
open CategoryTheory Opposite AlgebraicGeometry

/-- Underlying sections, lifted to the universe of the small etale category. -/
abbrev etaleAbelianLargeSections {X : Scheme.{u + 1}}
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  F.obj ⋙ forget AddCommGrpCat.{u + 1} ⋙ uliftFunctor.{u + 2, u + 1}

/-- The pointwise set-valued Kan extension before sheafification. -/
noncomputable abbrev etaleAbelianSetKan {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  p.Etale.op.leftKanExtension (etaleAbelianLargeSections F)

/-- The comparison induced by the supplied adjunction unit, by the Kan universal property. -/
noncomputable def etaleAbelianKanComparison
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    etaleAbelianSetKan p F ⟶ etaleAbelianLargeSections (H.obj F) :=
  Functor.descOfIsLeftKanExtension _
    (p.Etale.op.leftKanExtensionUnit (etaleAbelianLargeSections F)) _
    (Functor.whiskerRight (Functor.whiskerRight (hH.unit.app F).hom
      (forget AddCommGrpCat.{u + 1})) uliftFunctor.{u + 2, u + 1})

private theorem smallAbelianSheaf_essImage
    {T : Scheme.{u + 1}} (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 2})
    [∀ B : T.Etaleᵒᵖ, Small.{u + 1} (G.obj.obj B)] :
    (sheafCompose T.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 2, u + 1}).essImage
      G := by
  let P : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    { obj B := AddCommGrpCat.of (Shrink.{u + 1} (G.obj.obj B))
      map {B C} f := AddCommGrpCat.ofHom
        (Shrink.addEquiv.symm.toAddMonoidHom.comp
          ((G.obj.map f).hom.comp Shrink.addEquiv.toAddMonoidHom))
      map_id B := by ext x; simp
      map_comp f g := by ext x; simp }
  let e : P ⋙ AddCommGrpCat.uliftFunctor.{u + 2, u + 1} ≅ G.obj :=
    NatIso.ofComponents
      (fun B ↦ (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso)
      (fun f ↦ by
        ext x
        change Shrink.addEquiv (Shrink.addEquiv.symm
          (G.obj.map f (Shrink.addEquiv x.down))) = _
        exact Shrink.addEquiv.apply_symm_apply _)
  have hP : Presheaf.IsSheaf T.smallEtaleTopology P :=
    Presheaf.isSheaf_of_isSheaf_comp T.smallEtaleTopology P
      AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
      ((Presheaf.isSheaf_of_iso_iff e).mpr G.property)
  exact ⟨⟨P, hP⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

private theorem etaleSetPullback_unit_hom
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (G : Sheaf X.smallEtaleTopology (Type (u + 2))) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p.Etale
      (Type (u + 2)) X.smallEtaleTopology T.smallEtaleTopology).unit.app G).hom =
        p.Etale.op.leftKanExtensionUnit G.obj ≫
          Functor.whiskerLeft p.Etale.op (toSheafify T.smallEtaleTopology
            (p.Etale.op.leftKanExtension G.obj)) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    ((p.Etale.op.lanAdjunction (Type (u + 2))).comp
      (sheafificationAdjunction T.smallEtaleTopology (Type (u + 2))))
    (fullyFaithfulSheafToPresheaf X.smallEtaleTopology (Type (u + 2)))
    (Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback p.Etale
      (Type (u + 2)) X.smallEtaleTopology T.smallEtaleTopology)
    (R := p.Etale.sheafPushforwardContinuous (Type (u + 2))
      X.smallEtaleTopology T.smallEtaleTopology)
    (Iso.refl _) (Iso.refl _) G
  simp only [Iso.refl_hom, NatTrans.id_app] at h
  rw [Adjunction.comp_unit_app] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The underlying-set Kan comparison is locally surjective (Stacks, Tags 09XN and 00YV). -/
theorem etaleAbelianKanComparison_locally_surjective
    {X T : Scheme.{u + 1}} (p : T ⟶ X)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology T.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective T.smallEtaleTopology
      (etaleAbelianKanComparison p H hH F) := by
  classical
  let UX := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let UT := sheafCompose T.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 2, u + 1}
  let La := Etale.upperStar AddCommGrpCat.{u + 2} p
  let Ra := Etale.lowerStar AddCommGrpCat.{u + 2} p
  let FaX := sheafForget (D := AddCommGrpCat.{u + 2}) X.smallEtaleTopology
  let FaT := sheafForget (D := AddCommGrpCat.{u + 2}) T.smallEtaleTopology
  let Ls := Scheme.etaleSetPullback p
  let aa := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 2} p
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous p.Etale
    (Type (u + 2)) X.smallEtaleTopology T.smallEtaleTopology
  have hLex : CategoryTheory.Limits.PreservesFiniteLimits Ls := by
    unfold Ls Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
    let : AB5OfSize.{u + 1, u + 2} (Type (u + 2)) :=
      AB5OfSize_of_univLE.{u + 1, u + 2, u + 2, u + 2} (Type (u + 2))
    infer_instance
  obtain ⟨ea, hea⟩ := etaleInverseImageAbelianLift_hom T X p hLex
  -- The large inverse image of a small sheaf has small section groups.
  let K := UX ⋙ La
  have hK : ∀ G, UT.essImage (K.obj G) := by
    intro G
    have hsmall (B : T.Etaleᵒᵖ) : Small.{u + 1} ((K.obj G).obj.obj B) := by
      have hs := Scheme.etale_setPullback_small p
        ((sheafForget (D := AddCommGrpCat.{u + 1}) X.smallEtaleTopology).obj G) B.unop
      have hs' : Small.{u + 1}
          ((Ls.obj (FaX.obj (UX.obj G))).obj.obj B) := by
        convert hs using 1
        rfl
      exact @small_of_injective _ _ hs' _
        (asIso ((ea.hom.app (UX.obj G)).hom.app B)).toEquiv.injective
    let := hsmall
    exact smallAbelianSheaf_essImage (K.obj G)
  -- Restrict the adjunction to small coefficients and compare it with the supplied one.
  let L := Functor.essImage.liftFunctor K UT hK
  let e := Functor.essImage.liftFunctorCompIso K UT hK
  let ar : L ⊣ p.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology T.smallEtaleTopology :=
    aa.restrictFullyFaithful
      (fullyFaithfulSheafCompose _ AddCommGrpCat.uliftFunctorFullyFaithful)
      (fullyFaithfulSheafCompose _ AddCommGrpCat.uliftFunctorFullyFaithful)
      e.symm (Iso.refl _)
  let c := ar.leftAdjointUniq hH
  let d : Ls.obj (FaX.obj (UX.obj F)) ≅ FaT.obj (UT.obj (H.obj F)) :=
    (ea.app (UX.obj F)).symm ≪≫ FaT.mapIso (e.app F).symm ≪≫
      FaT.mapIso (UT.mapIso (c.app F))
  -- Track the unit through the restriction and the uniqueness isomorphism.
  have hrest : UX.map (ar.unit.app F) =
      aa.unit.app (UX.obj F) ≫ Ra.map (e.inv.app F) := by
    dsimp only [ar]
    rw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Iso.refl_hom, Iso.symm_hom, NatTrans.id_app]
    rfl
  let z := e.inv.app F ≫ UT.map (c.hom.app F)
  have hz : aa.homEquiv (UX.obj F) (UT.obj (H.obj F)) z =
      UX.map (hH.unit.app F) := by
    rw [Adjunction.homEquiv_unit]
    change aa.unit.app (UX.obj F) ≫ Ra.map (e.inv.app F ≫ UT.map (c.hom.app F)) = _
    rw [Ra.map_comp, ← Category.assoc, ← hrest]
    change UX.map (ar.unit.app F) ≫ UX.map
      ((p.Etale.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        X.smallEtaleTopology T.smallEtaleTopology).map (c.hom.app F)) = _
    rw [← UX.map_comp, Adjunction.unit_leftAdjointUniq_hom_app]
  have hu := hea (UX.obj F) (UT.obj (H.obj F)) z
  rw [hz, Adjunction.homEquiv_unit] at hu
  have hd : ea.inv.app (UX.obj F) ≫ FaT.map z = d.hom := by
    simp [d, z]
  rw [hd] at hu
  -- Kan uniqueness identifies the concrete map with the locally surjective factorization.
  let q : etaleAbelianSetKan p F ⟶ etaleAbelianLargeSections (H.obj F) :=
    toSheafify T.smallEtaleTopology (etaleAbelianSetKan p F) ≫ d.hom.hom
  have hq : etaleAbelianKanComparison p H hH F = q := by
    apply Functor.leftKanExtension_hom_ext p.Etale.op (etaleAbelianLargeSections F)
    dsimp only [etaleAbelianKanComparison]
    rw [Functor.descOfIsLeftKanExtension_fac]
    have hut := congrArg (fun t ↦ t.hom) hu
    change _ = (a.unit.app (FaX.obj (UX.obj F))).hom ≫
      Functor.whiskerLeft p.Etale.op d.hom.hom at hut
    rw [etaleSetPullback_unit_hom p (FaX.obj (UX.obj F))] at hut
    simp only [q, Functor.whiskerLeft_comp]
    simp only [Category.assoc] at hut
    convert hut using 1 <;> rfl
  rw [hq]
  infer_instance
