/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TateTwist.ProEtale
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportTateLevelRepresentation
import all WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit

/-! # Inverse image of the integral Tate limit cone

Source: Bhatt--Scholze, Section 6.8, the integral root tower; the integral
comparison clause of `sk-thm-purity-transport` in the current blueprint.
(blueprint: lem-pur-transport-tate-limit-cone).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- Ordinary condensed-module pullback preserves the particular Tate limit cone.

Source: Bhatt--Scholze, Section 6.8, construction of the integral Tate line.
(blueprint: lem-pur-transport-tate-limit-cone).

Proof: each finite free integral root module has underlying abelian sheaf the
finite root sheaf, since reduction of the continuous integral coefficient is
the constant finite residue ring. These identifications commute with the
power transitions. The tower of representing finite etale schemes has an
affine inverse limit, weakly etale over Y, hence an object of the pro-etale
site. Yoneda computes its sheaf limit. Base change preserves that representing
limit and inverse image of its representable sheaf is the representable sheaf
of its base change. Therefore inverse image preserves this tower's limit of
underlying set sheaves. Forgetting abelian groups commutes with inverse image
and preserves and reflects limits, giving the abelian assertion. Internal
module forgetting also preserves and reflects limits; finally extension along
the invertible coefficient comparison is an equivalence, so preserves limits.
These arguments include level zero, the empty scheme and arbitrary f; no
preservation of unrelated infinite limits by inverse image is asserted. -/
theorem tateLimitCone (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    Nonempty (IsLimit
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).mapCone
        (limit.cone (tateModuleSystem Y ell)))) := by
  let T := tateModuleSystem Y ell
  let R := Profinite.continuousMapRingObj.{u} ℤ_[ell]
  let V := Mod.forget
    (C := Sheaf (ProEt.topology Y) Ab.{u + 1})
    (D := Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj R Y)
  let Ry := sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})
  let Rx := sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})
  let L := upperStar AddCommGrpCat.{u + 1} f
  let P := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  classical
  choose W hfin het e using tateLevelRepresentation Y ell
  obtain ⟨D, hD, ⟨e⟩⟩ := lift_representable_diagram
    (Scheme.ProEt.topology Y).uliftYoneda.{u + 1} (T ⋙ V ⋙ Ry)
    (fun n ↦ W n.unop) (fun n ↦ (e n.unop).some)
  have hfinD (n : ℕᵒᵖ) : IsFinite (D.obj n).hom := by rw [hD]; exact hfin _
  have hetD (n : ℕᵒᵖ) : Etale (D.obj n).hom := by rw [hD]; exact het _
  let liftIndex : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ := AsSmall.equiv
  let : IsCofiltered (AsSmall.{u} ℕᵒᵖ) := IsCofiltered.of_equivalence liftIndex
  obtain ⟨hlim, hpres⟩ := finiteEtale_geometric_limit f
    (liftIndex.inverse ⋙ D) (fun i ↦ hfinD (ULift.down i)) (fun i ↦ hetD (ULift.down i))
  let := hlim
  let := hpres
  let : HasLimit D := Functor.Initial.hasLimit_of_comp liftIndex.inverse
  let : PreservesLimit D (Scheme.proEtaleBaseChange f) :=
    Functor.Initial.preservesLimit_of_comp liftIndex.inverse
  let Ly := (Scheme.ProEt.topology Y).uliftYoneda.{u + 1}
  let Lx := (Scheme.ProEt.topology X).uliftYoneda.{u + 1}
  let : PreservesLimit D (Scheme.proEtaleBaseChange f ⋙ Lx) := inferInstance
  let : PreservesLimit D (Ly ⋙ P) :=
    preservesLimit_of_natIso D (representableInverseImageIso f)
  let : PreservesLimit (D ⋙ Ly) P := by
    exact preservesLimit_of_preserves_limit_cone
      (isLimitOfPreserves Ly (limit.isLimit D))
      (isLimitOfPreserves (Ly ⋙ P) (limit.isLimit D))
  let : PreservesLimit ((T ⋙ V) ⋙ Ry) P :=
    preservesLimit_of_iso_diagram P (e ≪≫ (Functor.associator T V Ry).symm)
  let : PreservesLimitsOfShape ℕᵒᵖ (Ry ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Ry :=
    preservesLimitsOfShape_of_reflects_of_preserves Ry (sheafToPresheaf _ _)
  let : PreservesLimitsOfShape ℕᵒᵖ (Rx ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (sheafToPresheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} ⋙
        (Functor.whiskeringRight _ _ _).obj (forget AddCommGrpCat.{u + 1})))
  let : PreservesLimitsOfShape ℕᵒᵖ Rx :=
    preservesLimitsOfShape_of_reflects_of_preserves Rx (sheafToPresheaf _ _)
  let : ReflectsLimitsOfShape ℕᵒᵖ Rx := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let : PreservesLimit (T ⋙ V) (Ry ⋙ P) :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit (T ⋙ V))
      (isLimitOfPreserves P (isLimitOfPreserves Ry (limit.isLimit (T ⋙ V))))
  let : PreservesLimit (T ⋙ V) (L ⋙ Rx) :=
    preservesLimit_of_natIso (T ⋙ V) (abelianForgetInverseImageIso f).symm
  let : PreservesLimit (T ⋙ V) L := preservesLimit_of_reflects_of_preserves L Rx
  let U := CondensedRing.upperStar R f
  let W := Mod.forget
    (C := Sheaf (ProEt.topology X) Ab.{u + 1})
    (D := Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)
  let : ReflectsLimitsOfShape ℕᵒᵖ W := reflectsLimitsOfShape_of_reflectsIsomorphisms
  let eU : U ⋙ W ≅ V ⋙ L := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (L.mapMod (condensedRingObj R Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom R f))) W
  let : PreservesLimit T (U ⋙ W) := preservesLimit_of_natIso T eU.symm
  let : PreservesLimit T U := preservesLimit_of_reflects_of_preserves U W
  exact ⟨isLimitOfPreserves U (limit.isLimit T)⟩


end AlgebraicGeometry.ProEtale.PurityTransport
