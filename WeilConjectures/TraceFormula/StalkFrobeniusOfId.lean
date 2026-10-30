/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Sections
public import WeilConjectures.TraceFormula.BaseChange.WeilObject
public import WeilConjectures.TraceFormula.WeilTrace

/-!
# The Frobenius on the stalks of a module object with the identity Weil structure

A module object `M` on a scheme `X` over `Spec k` is a Weil sheaf for the identity of `X`, with
the identity structure `(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.WeilSheaf.ofId`). For the base
`X = Spec k`, at a geometric point `x̄ : Spec k̄ ⟶ Spec k`, the `(n + 1)`-st Frobenius of the
stalk `x̄^* M` acts on the global sections `𝟙_ ⟶ x̄^* M` by pullback along `σⁿ⁺¹`
(`ProEtale.CondensedRing.comp_frobeniusStalk_ofId_str_hom`): it sends `v` to
`𝟙_ ≅ (σⁿ⁺¹)^* 𝟙_ ⟶ (σⁿ⁺¹)^* x̄^* M ≅ (σⁿ⁺¹ ≫ x̄)^* M = x̄^* M`
(`ProEtale.CondensedRing.upperStarSectionMap`).

## Implementation notes

The transports along equalities of morphisms are written as `eqToHom` of objects
(`congrArg (fun s ↦ s^* M)`), and the identities `g = 𝟙` are never substituted: comparing the
components of transports of pullback functors along different equalities makes the kernel
unfold the pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]

section OfId

variable {X : Over (Spec (.of k))}

/-- A module object `M` on `X` as a Weil sheaf for the identity of `X`, with the identity
structure isomorphism `(𝟙)^* M ≅ M` (`ProEtale.CondensedRing.upperStarId`). -/
noncomputable def WeilSheaf.ofId
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    WeilSheaf ℓ (Iso.refl X) :=
  IsoAlgebra.mk M ((upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).app M)

/-- The structure isomorphism of `WeilSheaf.ofId M` is the identity isomorphism `(𝟙)^* M ≅ M`. -/
lemma WeilSheaf.ofId_str
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (WeilSheaf.ofId ℓ M).str = (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).app M :=
  IsoAlgebra.mk_str _ _

/-- The structure isomorphism of `WeilSheaf.ofId M` is the identity isomorphism `(𝟙)^* M ≅ M`. -/
lemma WeilSheaf.ofId_str_hom
    (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)) :
    (WeilSheaf.ofId ℓ M).str.hom =
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left).hom.app (WeilSheaf.ofId ℓ M).carrier :=
  congrArg Iso.hom (WeilSheaf.ofId_str ℓ M)

end OfId

section Identity

variable {Y : Scheme.{u}}
  (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))

set_option maxHeartbeats 400000 in
-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- The composition isomorphism `(a ≫ b)^* ≅ b^* ⋙ a^*`, followed by the identifications
`b^* ≅ (𝟙)^* ≅ 𝟭` and `a^* ≅ (𝟙)^* ≅ 𝟭`, for `a = 𝟙` and `b = 𝟙`, is the identification
`(a ≫ b)^* ≅ (𝟙)^* ≅ 𝟭`; the composition isomorphism may be transported along `a ≫ b = t`. -/
lemma upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId_of_eq (a b : Y ⟶ Y) {t : Y ⟶ Y}
    (ht : a ≫ b = t)
    (c : (t)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅
      (b)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hc : c = eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) ht.symm) ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) a b)
    (ha : a = 𝟙 Y) (hb : b = 𝟙 Y) (htt : t = 𝟙 Y) :
    c.hom.app M ≫ (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hb) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) ≫
        eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) ha) ≫
          (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) htt) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M := by
  subst ht hc
  have hn := upperStarComp_hom_app_map_upperStarCongr_hom_app
    (Profinite.padicAlgClRingObj ℓ) a hb M
  rw [upperStarCongr_hom_app_eq_eqToHom, upperStarCongr_hom_app_eq_eqToHom] at hn
  have e : (upperStarComp (Profinite.padicAlgClRingObj ℓ) a (𝟙 Y)).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (Category.comp_id a)) ≫
        (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) := by
    rw [upperStarComp_id_right, upperStarCongr_eq_upperStarEqToIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
      upperStarEqToIso_hom_app]
  have hi : (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) ≫
      (a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) = 𝟙 _ :=
    ((a)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso
      ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).app M)).inv_hom_id
  rw [eqToIso_refl, Iso.refl_trans, Functor.map_comp, Category.assoc, reassoc_of% hn, e,
    Category.assoc, reassoc_of% hi, eqToHom_trans_assoc, eqToHom_trans_assoc]

set_option maxHeartbeats 400000 in
-- the composite of the transports and composition isomorphisms takes some time to elaborate
/-- The composition isomorphism `(x ≫ g)^* ≅ g^* ⋙ x^*`, followed by the identification
`g^* ≅ (𝟙)^* ≅ 𝟭`, for `g = 𝟙`, is the transport along `x ≫ g = x`. -/
lemma upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId {S : Scheme.{u}} (x : S ⟶ Y)
    {g : Y ⟶ Y} (hg : g = 𝟙 Y) (h : x ≫ g = x) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x g).hom.app M ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          (eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) hg) ≫
            (upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M) h) := by
  have hn := upperStarComp_hom_app_map_upperStarCongr_hom_app
    (Profinite.padicAlgClRingObj ℓ) x hg M
  rw [upperStarCongr_hom_app_eq_eqToHom, upperStarCongr_hom_app_eq_eqToHom] at hn
  have e : (upperStarComp (Profinite.padicAlgClRingObj ℓ) x (𝟙 Y)).hom.app M =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (Category.comp_id x)) ≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
          ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) := by
    rw [upperStarComp_id_right, upperStarCongr_eq_upperStarEqToIso]
    simp only [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp,
      upperStarEqToIso_hom_app]
  have hi : (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).inv.app M) ≫
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map
        ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).hom.app M) = 𝟙 _ :=
    ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso
      ((upperStarId (Profinite.padicAlgClRingObj ℓ) Y).app M)).inv_hom_id
  rw [Functor.map_comp, reassoc_of% hn, e, Category.assoc, hi]
  simp only [Functor.id_obj, Category.comp_id, eqToHom_trans]

end Identity

section Point

/-- Every endomorphism of the base point `Spec k` over itself is the identity. -/
lemma point_hom_left_eq_id (g : point k ⟶ point k) : g.left = 𝟙 (point k).left :=
  (Category.comp_id _).symm.trans (Over.w g)

variable (M : CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (point k).left) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (point k).left))

/-- The identification `M ≅ (𝟙)^* M ≅ g^* M` for an endomorphism `g` of the base point, which is
the identity. -/
noncomputable def pointUpperStarIdIso (g : point k ⟶ point k) :
    M ≅ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M :=
  ((upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left).app M).symm ≪≫
    eqToIso (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
      (point_hom_left_eq_id g).symm)

lemma pointUpperStarIdIso_inv (g : point k ⟶ point k) :
    (pointUpperStarIdIso ℓ M g).inv =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (point_hom_left_eq_id g)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left).hom.app M := by
  rw [pointUpperStarIdIso, Iso.trans_inv, eqToIso.inv, Iso.symm_inv, Iso.app_hom]

/-- **The iterated identity structure of the base point is the identity structure**: the
`(n + 1)`-st iterate of the identity structure isomorphism `(𝟙)^* M ≅ M` of a module object on
the base point is the transport along `(𝟙ⁿ⁺¹).left = 𝟙` followed by the identity structure
isomorphism. -/
lemma WeilSheaf.pow_ofId_str_hom (n : ℕ) :
    (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).str.hom =
      eqToHom (congrArg (fun s ↦ (s)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M)
          (point_hom_left_eq_id ((Iso.refl (point k)).pow (n + 1)).hom)) ≫
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left).hom.app M := by
  have hφ : (WeilSheaf.ofId ℓ M).str =
      (pointUpperStarIdIso ℓ M (Iso.refl (point k)).hom).symm := by
    ext1
    rw [Iso.symm_hom, pointUpperStarIdIso_inv, eqToHom_refl, Category.id_comp,
      WeilSheaf.ofId_str_hom]
    rfl
  have hs : (WeilSheaf.pow ℓ (WeilSheaf.ofId ℓ M) (n + 1)).str =
      (Iso.refl (point k)).powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (upperStarId (Profinite.padicAlgClRingObj ℓ) (point k).left)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
        (WeilSheaf.ofId ℓ M).str (n + 1) :=
    IsoAlgebra.mk_str _ _
  rw [hs, powStr_succ_upperStar_eq_powSuccStr, hφ,
    (Iso.refl (point k)).powSuccStr_symm_hom_eq_inv _ _ (pointUpperStarIdIso ℓ M)
      (fun f g ↦ ?_) n, pointUpperStarIdIso_inv]
  rw [pointUpperStarIdIso_inv, pointUpperStarIdIso_inv, pointUpperStarIdIso_inv]
  exact upperStarComp_hom_app_comp_map_eqToHom_comp_upperStarId_of_eq ℓ M f.left g.left
    (Over.comp_left _ _ _ f g).symm _ (upperStarComp_left_eq ℓ f g) (point_hom_left_eq_id f)
    (point_hom_left_eq_id g) (point_hom_left_eq_id (f ≫ g))

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
