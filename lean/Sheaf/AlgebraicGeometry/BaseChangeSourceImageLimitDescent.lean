/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.Transition
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Descent of base-change source images

Source: Stacks Project Tag 09Z1 and the limit step of Tag 0F07.
(blueprint: lem-sbc-source-image-limit-descent)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {X S T : Scheme.{u}} [IsAffine S]
variable (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
variable (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X)
variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over T)
variable [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
variable [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]

/-- The image under base change of a source element at the limit comes from a stage.

Source: Stacks Tag 09Z1, applied to the source side in Tag 0F07 condition (2).
(blueprint: lem-sbc-source-image-limit-descent)

Proof: The maps from the qcqs stages to the affine scheme S are qcqs. The limit is qcqs
and its projections are affine. Apply higher-direct-image continuity to the sheaves
pulled back from F on the stages, and then apply the exact inverse image along p and the
geometric stalk functor at x. These two left adjoints preserve colimits; inverse image
is exact and hence commutes with degree-q homology. Thus every element of the source
stalk at the limit is the restriction of a source element at some stage. In negative
degrees both source stalks vanish, so choose any stage and its zero element. Apply the
base-change map to a representative of the given element. Compatibility of base change
with restriction, followed by naturality for the inverse-image composition isomorphism,
identifies its restriction with the base-change image at the limit. This proves the
asserted equality; no injectivity or nonzero hypothesis is needed.
-/
theorem baseChange_source_image_limit_descent (c : Cone D)
    (hc : IsLimit ((Over.forget T).mapCone c))
    (η : baseChangeSourceStalk Λ p g q F x c.pt) :
    ∃ (i : I) (ηi : baseChangeSourceStalk Λ p g q F x (D.obj i)),
      (baseChangeTargetStalkMap Λ p g q F x (c.π.app i)).hom
        ((baseChangeStalkMap Λ p g q F x (D.obj i)).hom ηi) =
          (baseChangeStalkMap Λ p g q F x c.pt).hom η := by sorry

end AlgebraicGeometry.Etale
