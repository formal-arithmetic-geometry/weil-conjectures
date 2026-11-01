/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence

/-! # Identity normalization of the ordinary exceptional Hom correspondence

Source: latest blueprint sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, rank-zero normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u u'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

private theorem star_identity_comp
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp (𝟙 X)).symm).app M =
    ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctor).map
      ((rightDerivedLowerStarIdIso A X).hom.app M) := by
  have h := (unboundedFormalism A).pfComp'_id_left_inv_app (𝟙 X) M
  rw [unbounded_pf_id] at h
  have hc : ((unboundedFormalism A).pfComp' (𝟙 X) (𝟙 X) (𝟙 X)
      (Category.id_comp (𝟙 X))).inv =
      rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp (𝟙 X)).symm := by
    rw [ExchangeFormalism.pfComp', conjugateIsoEquiv_apply_inv, Iso.symm_inv,
      unbounded_pb_comp']
    simpa only [rightDerivedLowerStarCompHom, exact_pb_comp,
      Functor.mapDerivedCategoryTriangleIso, unboundedFormalism] using
      (conjugateEquiv_leftDerivedUpperStarComp_hom (ModuleCat.{u + 1} A)
        (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp (𝟙 X)).symm).symm
  rw [hc] at h
  exact h

private theorem identity_forget_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 X)) ≪≫
      rightDerivedLowerStarIdIso A X = unboundedEtaleLowerShriekId A X := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  let c := Compactification.ofIsProper (𝟙 X)
  have hc := model_forget_chosen A c M
  have hf : (rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} A) (𝟙 X)).hom =
      compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification (𝟙 X)) := by
    rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
      rightDerivedLowerShriekToLowerStarComp_comp_eq]
    rfl
  simp only [Iso.trans_hom, NatTrans.comp_app]
  rw [hf]
  apply (cancel_epi ((rightDerivedLowerShriekIso A c).hom.app M)).1
  rw [← Category.assoc, hc]
  simp only [unboundedEtaleLowerShriekId, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  rw [Iso.hom_inv_id_app_assoc]
  simp only [compactificationForgetSupports, NatTrans.comp_app,
    Functor.whiskerRight_app]
  dsimp only [c, Compactification.ofIsProper]
  rw [Category.assoc]
  change ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctor).map
      ((derivedOpenImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) (𝟙 X)).app M) ≫
      (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} A) (𝟙 X) (𝟙 X) (𝟙 X)
        (Category.id_comp (𝟙 X)).symm).app M ≫
      (rightDerivedLowerStarIdIso A X).hom.app M = _
  rw [star_identity_comp, ← Functor.map_comp_assoc, identity_derived_open_inclusion]
  let O := (openImmersionLowerShriek (ModuleCat.{u + 1} A) (𝟙 X)).mapDerivedCategory
  let o : O ≅ 𝟭 (DerivedCategoryModule A X) := Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X))
      (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫ Functor.mapDerivedCategoryIdIso _
  have ht :
      (Functor.isoWhiskerLeft O (rightDerivedLowerStarIdIso A X) ≪≫
        Functor.rightUnitor O ≪≫ o).hom.app M =
      (identityEtaleCompactSupportComparison A X ≪≫
        Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 X)
              inferInstance) (upperStarId (ModuleCat.{u + 1} A) X)) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app M := by
    exact NatTrans.congr_app (congrArg Iso.hom (identity_tail_eq A X)) M
  have hn := identity_naturality_unitor (rightDerivedLowerStarIdIso A X) o M
  simpa only [o, O, Iso.trans_hom, NatTrans.comp_app] using
    hn.trans ht

private lemma inverse_star_identity (B : Type u') [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [HasSmallSiteSheafify B] (T : Scheme.{u}) :
    upperStarInvIsoLowerStarHom B (Iso.refl T) ≪≫ lowerStarId B T = upperStarId B T := by
  let R := lowerStar B (𝟙 T)
  let b := lowerStarId B T
  let a := upperStarId B T
  let e : upperStar B (𝟙 T) ≅ lowerStar B (𝟙 T) :=
    upperStarInvIsoLowerStarHom B (Iso.refl T)
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hc := Adjunction.leftAdjointUniq_hom_app_counit
    (upperStarLowerStarAdjunction B (𝟙 T))
    (lowerStarEquivalenceOfIso B (Iso.refl T)).toAdjunction K
  change e.hom.app (R.obj K) ≫
    (lowerStarComp B (𝟙 T) (𝟙 T) (𝟙 T) (by simp) ≪≫ b).hom.app K =
    (upperStarLowerStarAdjunction B (𝟙 T)).counit.app K at hc
  rw [lowerStarComp_id_left] at hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.id_obj, Category.comp_id] at hc
  have ha := upperStarId_inv_app_counit_app B T K
  have hh := congrArg (fun z ↦ a.inv.app (R.obj K) ≫ z) hc
  rw [ha] at hh
  have hh' : e.hom.app (R.obj K) ≫ R.map (b.hom.app K) = a.hom.app (R.obj K) := by
    apply (cancel_mono (b.hom.app K)).1
    apply (cancel_epi (a.inv.app (R.obj K))).1
    simpa only [R, b, a, Category.assoc, Category.id_comp, Category.comp_id,
      Functor.comp_obj, Functor.id_obj, Iso.inv_hom_id_app_assoc] using hh
  change e.hom.app K ≫ b.hom.app K = a.hom.app K
  apply (cancel_epi ((upperStar B (𝟙 T)).map (b.hom.app K))).1
  calc
    _ = e.hom.app (R.obj K) ≫ R.map (b.hom.app K) ≫ b.hom.app K := by
      simpa only [R, Functor.id_obj, Category.assoc] using
        congrArg (fun z ↦ z ≫ b.hom.app K) (e.hom.naturality (b.hom.app K))
    _ = a.hom.app (R.obj K) ≫ b.hom.app K := by rw [← Category.assoc, hh']
    _ = _ := by
      simpa only [Functor.id_map, Functor.id_obj] using
        (a.hom.naturality (b.hom.app K)).symm

private lemma derived_inverse_star_identity (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) :
    rightDerivedLowerStarIsoLeftDerivedUpperStarInv (ModuleCat.{u + 1} A) (Iso.refl T) ≪≫
      leftDerivedUpperStarId (ModuleCat.{u + 1} A) T = rightDerivedLowerStarIdIso A T := by
  let B := ModuleCat.{u + 1} A
  have hi : leftDerivedUpperStarIsoMapDerivedCategory B (𝟙 T) ≪≫
      (Functor.mapDerivedCategoryNatIso (upperStarId B T) ≪≫
        Functor.mapDerivedCategoryIdIso _) = leftDerivedUpperStarId B T := by
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact (leftDerivedUpperStarId_hom_app B T K).symm
  have he : (upperStarInvIsoLowerStarHom B (Iso.refl T)).symm ≪≫ upperStarId B T =
      lowerStarId B T := by
    rw [← inverse_star_identity B T]
    exact Iso.symm_self_id_assoc _ _
  dsimp only [B] at hi he ⊢
  rw [← hi]
  dsimp only [rightDerivedLowerStarIsoLeftDerivedUpperStarInv, Iso.refl_hom, Iso.refl_inv]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [← Category.assoc (Functor.mapDerivedCategoryNatIso _).hom,
    ← Functor.mapDerivedCategoryNatIso_trans, he]
  simp only [rightDerivedLowerStarIdIso, Iso.trans_hom]

private lemma identity_adjunct_of_normalized_comparisons
    {C : Type*} [Category C] {F G L R : C ⥤ C}
    (a : F ⊣ G) (b : L ⊣ R) (c : F ≅ R) (d : R ≅ L)
    (l : L ≅ 𝟭 C) (r : R ≅ 𝟭 C)
    (hd : d ≪≫ l = r)
    (hb : conjugateEquiv Adjunction.id b l.hom = r.inv)
    (v : F ≅ 𝟭 C) (hv : c ≪≫ r = v) (K : C) :
    a.homEquiv K K (v.hom.app K) =
      (((a.ofNatIsoLeft (c ≪≫ d)).rightAdjointUniq (b.ofNatIsoRight d) ≪≫ l).app K).inv := by
  let a' := a.ofNatIsoLeft (c ≪≫ d)
  let b' := b.ofNatIsoRight d
  have hu : (a'.homEquiv _ K) (b'.counit.app K) =
      (a'.rightAdjointUniq b').inv.app K := by
    apply (a'.homEquiv _ K).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.rightAdjointUniq_inv_app,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app]
  have hh := congrArg (fun z ↦ l.inv.app K ≫ z) hu
  rw [← a'.homEquiv_naturality_left] at hh
  have he : l.inv.app K ≫ d.inv.app K = r.inv.app K := by
    exact NatTrans.congr_app (congrArg Iso.inv hd) K
  have hn : L.map (r.inv.app K) ≫ b.counit.app K = l.hom.app K := by
    have h := conjugateEquiv_counit Adjunction.id b l.hom K
    rw [hb] at h
    simpa only [Adjunction.id_counit, NatTrans.id_app, Functor.id_obj,
      Functor.comp_obj, Category.comp_id] using h
  have ht : L.map (l.inv.app K) ≫ b'.counit.app K = l.hom.app K := by
    change L.map (l.inv.app K) ≫ L.map (d.inv.app K) ≫ b.counit.app K = _
    rw [← Functor.map_comp_assoc, he, hn]
  rw [ht, Adjunction.homEquiv_ofNatIsoLeft_apply] at hh
  have hc : (c ≪≫ d).hom.app K ≫ l.hom.app K = (c ≪≫ r).hom.app K := by
    rw [← hd]
    simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  dsimp only [Functor.id_obj] at hh
  rw [hc, hv] at hh
  exact hh

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] rightDerivedLowerShriek rightDerivedUpperShriek
  rightDerivedUpperShriekAdjunction derivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIsoRightDerivedLowerStar rightDerivedLowerStarIsoLeftDerivedUpperStarInv
  leftDerivedUpperStarId rightDerivedLowerStarIdIso unboundedEtaleLowerShriekId

private lemma identity_exceptional_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u}) [IsNoetherian T] :
    rightDerivedUpperShriekIsoOfIso A (Iso.refl T) =
      ((rightDerivedUpperShriekAdjunction A (𝟙 T)).ofNatIsoLeft
        (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} A) (𝟙 T) ≪≫
          rightDerivedLowerStarIsoLeftDerivedUpperStarInv
            (ModuleCat.{u + 1} A) (Iso.refl T))).rightAdjointUniq
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) (𝟙 T)).ofNatIsoRight
          (rightDerivedLowerStarIsoLeftDerivedUpperStarInv
            (ModuleCat.{u + 1} A) (Iso.refl T))) := by
  dsimp only [rightDerivedUpperShriekIsoOfIso, Iso.refl_hom, Iso.refl_inv]
  rfl

set_option maxRecDepth 4096 in
/-- The identity compact-support map has the inverse exceptional identity as its
ordinary adjunct, for every complex, independently of any affine tower or site
comparison.
Source: latest blueprint sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, rank-zero normalization; Stacks Tag 0F7K.
(blueprint: lem-pur-etale-identity-exceptional-adjunct).

Proof: for the identity morphism the proper forget-supports comparison followed
by the ordinary direct-image identity is the unbounded compact-support identity.
To see this with the chosen compactification, transport to the identity
compactification by the graph-normalized refinement map. Naturality of the
open extension/direct-image counit and the proper direct-image compositor
identifies both composites with exact identity extension. The latter is
Adjunction.leftAdjointIdIso for the identity pullback. Derived-functor comparison
preserves this identity, since all identity functors here are exact.
The isomorphism rightDerivedUpperShriekIsoOfIso is rightAdjointUniq after this
proper comparison. Its counit equation says exactly that the inverse exceptional
identity is sent by inverse transposition to the compact-support identity.
The inverse-direct-image/identity-pullback comparison used there is normalized
by the derived upper/lower-star adjunction; the identity unit and counit triangle
cancel its two occurrences. Apply injectivity of the inverse Hom equivalence.
The calculation is natural in K and also valid on the empty scheme. -/
theorem identityExceptionalAdjunct (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsNoetherian T]
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (rightDerivedUpperShriekAdjunction A (𝟙 T)).homEquiv K K
      ((unboundedEtaleLowerShriekId A T).hom.app K) =
      (((rightDerivedUpperShriekIsoOfIso A (Iso.refl T)) ≪≫
        leftDerivedUpperStarId (ModuleCat.{u + 1} A) T).app K).inv := by
  rw [identity_exceptional_comparison]
  let B := ModuleCat.{u + 1} A
  exact identity_adjunct_of_normalized_comparisons
    (rightDerivedUpperShriekAdjunction A (𝟙 T))
    (derivedUpperStarLowerStarAdjunction B (𝟙 T))
    (rightDerivedLowerShriekIsoRightDerivedLowerStar B (𝟙 T))
    (rightDerivedLowerStarIsoLeftDerivedUpperStarInv B (Iso.refl T))
    (leftDerivedUpperStarId B T) (rightDerivedLowerStarIdIso A T)
    (derived_inverse_star_identity A T) (derived_identity_conjugate A T)
    (unboundedEtaleLowerShriekId A T) (identity_forget_normalization A T) K

end AlgebraicGeometry.Etale
