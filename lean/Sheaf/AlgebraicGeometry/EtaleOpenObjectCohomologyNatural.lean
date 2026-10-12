/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit
import Sheaf.Paper.SiteRestrictionInjectives
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
/-! # Natural comparison for cohomology over open étale objects

Source: Stacks Project, Cohomology on Sites, Tag 03F3, and Étale Cohomology, Tag 09AX.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- Object cohomology over an open is the cohomology of its inverse-image sheaf,
naturally for inclusions of opens.
Source: Stacks Project, Cohomology on Sites, Tag 03F3; Étale Cohomology, Tag 09AX.
(blueprint: lem-weil-pbc-etale-open-object-cohomology-natural).

Proof: Take an injective resolution of F. Restriction along an open immersion preserves
injectives, since extension by zero is an exact left adjoint. The natural isomorphism
between inverse image and localization restriction identifies the section complex of
the restricted resolution with the original resolution evaluated at that open. Taking
cohomology gives e. For V contained in U, naturality of this isomorphism and the
inverse-image adjunction unit identify evaluation restriction with pullback along V to U.
More explicitly, evaluate open_restriction_pullback_unit for g equal to the inclusion
of U into X and W equal to V. The fibre product V times_X U is V. The identity unit
cancels with the identity inverse-image comparison. The unit for U followed by its
restriction comparison is the identity on sections over V. Substitution identifies
the direct comparison for V with the two successive restriction comparisons followed
by inverse-image composition. Apply this identity in each degree of the resolution,
then take cohomology. Ext via injective resolutions identifies the resulting maps with
the Ext definitions of P and Sheaf.H and makes them resolution-independent. Thus the
stated naturality identity holds, including degree zero and the empty open. -/
theorem etaleOpenObjectCohomology_natural
    {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ)
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (hP : P = (Functor.flip ((uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).op ⋙
        Abelian.extFunctor q)).obj F)
 :
    ∃ e : ∀ U : X.Opens, P.obj
        (op (Scheme.Etale.mk U.ι)) ≅
        AddCommGrpCat.of (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q),
      (∀ (U V : X.Opens) (h : V ≤ U),
        P.map
            (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (X := X)
              (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk U.ι) (X.homOfLE h)
              (X.homOfLE_ι h) trivial).op ≫
            (e V).hom =
          (e U).hom ≫ AddCommGrpCat.ofHom
            (Etale.cohomologyMap (X.homOfLE h)
              ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F) q) ≫
            AddCommGrpCat.ofHom (Sheaf.H.map
              ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
                (X.homOfLE_ι h).symm).inv.app F) q)) := by sorry

end AlgebraicGeometry
