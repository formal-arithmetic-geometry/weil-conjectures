/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteAdjunction
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs

/-!
# A presheaf formula for the inverse image along a closed immersion

Let `X = Spec A` be affine and `i : Z ⟶ X` a closed immersion. On the affine pro-étale sites, base
change `u : X.AffineProEt ⥤ Z.AffineProEt` has the left adjoint `v`, `Spec C̄ ↦ Spec H_A(C̄)`
(`AlgebraicGeometry.Scheme.AffineProEt.closedLiftAdjunction`). This file shows that the inverse
image `i^* F` of a pro-étale sheaf `F` on `X`, restricted to the affine pro-étale site of `Z`, is
the sheafification of the presheaf `P_F(V) = F(v(V))`
(`AlgebraicGeometry.ProEtale.upperStarClosedRestrictionIso`, blueprint
`lem-exc-closed-inverse-image-formula`).

## Main results

- `AlgebraicGeometry.Scheme.AffineProEt.isContinuous_baseChange`: base change along an affine
  morphism is continuous for the topologies of the affine pro-étale sites.
- `AlgebraicGeometry.Scheme.AffineProEt.closedLiftSheafAdjunction`: on sheaves on the affine
  pro-étale sites, `G ↦ (V ↦ G(v(V)))^a` is left adjoint to `u_*`.
- `AlgebraicGeometry.ProEtale.upperStarClosedRestrictionIso`: the presheaf formula for `i^*`.

## Implementation notes

The formula is proved by uniqueness of left adjoints: under the equivalences between sheaves on
the pro-étale sites and on the affine pro-étale sites, `i_*` becomes `u_*`, whose left adjoint is
sheafification after precomposition with `v`, since precomposition with `v` is left adjoint to
precomposition with `u` (`CategoryTheory.Adjunction.whiskerLeft`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Scheme.AffineProEt

instance essentiallySmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.AffineProEt :=
  have : LocallySmall.{u + 1} X.AffineProEt := ⟨fun _ _ ↦ ⟨ULift.{u + 1} _, ⟨Equiv.ulift.symm⟩⟩⟩
  essentiallySmall_of_small_of_locallySmall _

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsAffineHom i]

/-- Base change commutes with the inclusions of the affine pro-étale sites into the pro-étale
sites. -/
noncomputable def baseChangeCompToProEtIso :
    toProEt X ⋙ MorphismProperty.Over.pullback @WeaklyEtale ⊤ i ≅
      baseChange i ⋙ toProEt Z :=
  NatIso.ofComponents (fun _ ↦ MorphismProperty.Over.isoMk (Iso.refl _)) fun _ ↦ by
    refine MorphismProperty.Over.Hom.ext ?_
    simp

/-- Base change along an affine morphism is continuous for the topologies of the affine pro-étale
sites: a sheaf on the affine pro-étale site of `Z` is the restriction of a pro-étale sheaf, and
base change is continuous on the pro-étale sites. -/
instance isContinuous_baseChange :
    (baseChange i).IsContinuous (topology X) (topology Z) where
  op_comp_isSheaf_of_types G := by
    let Φ := (toProEt Z).sheafPushforwardContinuous (Type (u + 1)) (topology Z)
      (ProEt.topology Z)
    have := Scheme.ProEt.isContinuous_overPullback i
    have := Functor.isContinuous_comp (toProEt X)
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i)
      (topology X) (ProEt.topology X) (ProEt.topology Z)
    have := Functor.isContinuous_of_iso (baseChangeCompToProEtIso i) (topology X)
      (ProEt.topology Z)
    rw [← isSheaf_iff_isSheaf_of_type]
    refine (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerLeft (baseChange i).op
      ((sheafToPresheaf _ _).mapIso (Φ.objObjPreimageIso G)))).1 ?_
    exact (baseChange i ⋙ toProEt Z).op_comp_isSheaf (topology X) (ProEt.topology Z)
      (Φ.objPreimage G)

variable [IsClosedImmersion i] [IsAffine X]
variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- On sheaves on the affine pro-étale sites, the functor `G ↦ (V ↦ G(v(V)))^a` is left adjoint
to the pushforward along base change `u`, since precomposition with `v` is left adjoint to
precomposition with `u` (`AlgebraicGeometry.Scheme.AffineProEt.closedLiftAdjunction`). -/
noncomputable def closedLiftSheafAdjunction :
    sheafToPresheaf (topology X) A ⋙ (Functor.whiskeringLeft _ _ A).obj (closedLift i).op ⋙
        presheafToSheaf (topology Z) A ⊣
      (baseChange i).sheafPushforwardContinuous A (topology X) (topology Z) :=
  (((closedLiftAdjunction i).op.whiskerLeft A).comp
    (sheafificationAdjunction (topology Z) A)).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ A) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Scheme.AffineProEt

namespace ProEtale

open AffineProEt

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X]

/-- The presheaf `P_F(V) = F(v(V))` on the affine pro-étale site of `Z` attached to a pro-étale
sheaf `F` on `X`, where `v` is `AlgebraicGeometry.Scheme.AffineProEt.closedLift`. -/
noncomputable def closedInverseImagePresheaf :
    Sheaf (ProEt.topology X) A ⥤ Z.AffineProEtᵒᵖ ⥤ A :=
  sheafToPresheaf (ProEt.topology X) A ⋙
    (Functor.whiskeringLeft _ _ A).obj (closedLift i ⋙ AffineProEt.toProEt X).op

/-- Under the restrictions to the affine pro-étale sites, `i_*` is the pushforward along base
change `u`. -/
noncomputable def lowerStarCompSheafPushforwardIso :
    (i)_*[A] ⋙ (AffineProEt.toProEt X).sheafPushforwardContinuous A (topology X)
        (ProEt.topology X) ≅
      (AffineProEt.toProEt Z).sheafPushforwardContinuous A (topology Z) (ProEt.topology Z) ⋙
        (baseChange i).sheafPushforwardContinuous A (topology X) (topology Z) :=
  have := Scheme.ProEt.isContinuous_overPullback i
  have := Functor.isContinuous_comp (baseChange i) (AffineProEt.toProEt Z) (topology X)
    (topology Z)
    (ProEt.topology Z)
  Functor.sheafPushforwardContinuousComp' (baseChangeCompToProEtIso i) A (topology X)
    (ProEt.topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ A (topology X) (topology Z)
      (ProEt.topology Z)).symm

/-- Blueprint `lem-exc-closed-inverse-image-formula`: let `X = Spec A` be affine and
`i : Z ⟶ X` a closed immersion. For a pro-étale sheaf `F` on `X`, the restriction of `i^* F` to
the affine pro-étale site of `Z` is the sheafification of the presheaf `P_F(V) = F(v(V))`, where
`v(Spec C̄) = Spec H_A(C̄)` (`AlgebraicGeometry.Scheme.AffineProEt.closedLift`). The formula
includes the sheafification. -/
noncomputable def upperStarClosedRestrictionIso :
    (i)^*[A] ⋙ (AffineProEt.toProEt Z).sheafPushforwardContinuous A (topology Z)
        (ProEt.topology Z) ≅
      closedInverseImagePresheaf A i ⋙ presheafToSheaf (topology Z) A :=
  have : HasLimitsOfSize.{u, u + 1} A := hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} A
  let EX := ((AffineProEt.toProEt X).sheafPushforwardContinuous A (topology X)
    (ProEt.topology X)).asEquivalence
  let EZ := ((AffineProEt.toProEt Z).sheafPushforwardContinuous A (topology Z)
    (ProEt.topology Z)).asEquivalence
  let adj₁ := (upperStarLowerStarAdjunction A i).comp EZ.toAdjunction
  let adj₂ := EX.toAdjunction.comp (closedLiftSheafAdjunction i A)
  -- the right adjoints agree: `u_* ⋙ EX⁻¹ ≅ EZ⁻¹ ⋙ i_*`
  let ρ : (baseChange i).sheafPushforwardContinuous A (topology X) (topology Z) ⋙ EX.inverse ≅
      EZ.inverse ⋙ (i)_*[A] :=
    Functor.isoWhiskerRight (Functor.leftUnitor _).symm _ ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerRight EZ.counitIso.symm _) _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EZ.inverse
        (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerLeft EZ.inverse
        (Functor.isoWhiskerRight (lowerStarCompSheafPushforwardIso A i).symm _) ≪≫
      Functor.isoWhiskerLeft EZ.inverse (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft EZ.inverse
        (Functor.isoWhiskerLeft _ EX.unitIso.symm) ≪≫
      Functor.isoWhiskerLeft EZ.inverse (Functor.rightUnitor _)
  Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight ρ)

end ProEtale

end AlgebraicGeometry
