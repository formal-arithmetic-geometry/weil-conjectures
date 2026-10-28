/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.SixFunctors.ScalarSixDirectImage
public import Sheaf.Paper.FiniteConstantRingedLocalModel
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import Sheaf.SixFunctors.ScalarSixCtf
import Sheaf.Paper.FiniteProperBaseChange
import Sheaf.Paper.IntegralProperBaseChange
import Sheaf.Paper.ProperBaseChangeRational

/-! # Proper direct-image coefficient comparison under open restriction

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Independence and Composition.
(blueprint: lem-sfb-proper-direct-image-coefficient-restriction).

The exchange is the existing counit-normalized derived mate. All coefficient and
geometric operations act on the ordinary unbounded internal-module derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Both open-restriction exchange maps are invertible, and the proper direct-image
coefficient comparison commutes with them after the two specified pullback comparisons.
The final two equations give identity-square normalization over both coefficient rings.

Source: blueprint latest, compact-support coefficient proof, Independence and Composition.
(blueprint: lem-sfb-proper-direct-image-coefficient-restriction).

Proof:
1. The exchange of RootCoordinateFace.exchange is the adjunct of the pulled-back
counit, using its canonical squareUpper comparison. Apply proper base change:
det-thm-sfb-proper-base-change-finite (2), integral (3), or rational (3).
Taking E = Q_ell includes the Z_ell and Q_ell stages. By det-prop-scalar-six-ctf
(3), scalar extension of M is again bounded constructible of finite Tor amplitude,
so the second exchange is invertible as well.
2. Use det-prop-scalar-six-pullback (1) at v and u. Its composition coherence
identifies transport around the square, giving exactly the displayed endpoints.
3. By lem-sfb-proper-open-coefficient-left-transpose, the inverse adjoint transpose
of the left composite under q at the new coefficients is T(t) after c_q, where
t is squareUpper followed by u-pullback of the p-counit.
4. By lem-sfb-proper-open-coefficient-right-transpose the right composite has the
same inverse transpose. Injectivity of the adjunction Hom bijection proves equality.
For the identity square, the pullback identity and composition coherences reduce
the defining adjunct to the counit, whose adjunct is the identity by the triangle law.
-/
theorem properDirectImageCoefficientRestriction
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (_ha : ListedCoefficientMap ell a)
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left]
    {ZV V : Scheme.{u}} (v : V ⟶ Y.left) [IsOpenImmersion v]
    (u : ZV ⟶ Z.left) (q : ZV ⟶ V) (sq : IsPullback u q p.left v)
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Z.left))
    (_hM : constantModelBoundedConstructible Λ.X Z.left M ∧
      DerivedCategory.finiteTorAmplitude _ M) :
    IsIso ((RootCoordinateFace.exchange Λ.X u q p.left v sq.w).app M) ∧
    IsIso ((RootCoordinateFace.exchange Λ'.X u q p.left v sq.w).app
      ((scalarSixChange a Z.left).obj M)) ∧
    ((scalarDirectImagePullbackData.theta a v).hom.app
          ((RootCoordinateFace.lower Λ.X p.left).obj M) ≫
        (scalarSixPull Λ' v).map ((scalarDirectImageMate a p.left).app M) ≫
        (RootCoordinateFace.exchange Λ'.X u q p.left v sq.w).app
          ((scalarSixChange a Z.left).obj M) ≫
        (RootCoordinateFace.lower Λ'.X q).map
          ((scalarDirectImagePullbackData.theta a u).inv.app M) =
      (scalarSixChange a V).map
          ((RootCoordinateFace.exchange Λ.X u q p.left v sq.w).app M) ≫
        (scalarDirectImageMate a q).app ((scalarSixPull Λ u).obj M)) ∧
    ((RootCoordinateFace.exchange Λ.X (𝟙 Z.left) p.left p.left (𝟙 Y.left)
          ((Category.id_comp p.left).trans (Category.comp_id p.left).symm)).app
          M ≫
        (RootCoordinateFace.lower Λ.X p.left).map
          ((Functor.mapDerivedCategoryNatIso
              (AlgebraicGeometry.ProEtale.CondensedRing.upperStarId Λ.X Z.left) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app M) =
      (Functor.mapDerivedCategoryNatIso
          (AlgebraicGeometry.ProEtale.CondensedRing.upperStarId Λ.X Y.left) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((RootCoordinateFace.lower Λ.X p.left).obj M)) ∧
    ((RootCoordinateFace.exchange Λ'.X (𝟙 Z.left) p.left p.left (𝟙 Y.left)
          ((Category.id_comp p.left).trans (Category.comp_id p.left).symm)).app
          ((scalarSixChange a Z.left).obj M) ≫
        (RootCoordinateFace.lower Λ'.X p.left).map
          ((Functor.mapDerivedCategoryNatIso
              (AlgebraicGeometry.ProEtale.CondensedRing.upperStarId Λ'.X Z.left) ≪≫
            Functor.mapDerivedCategoryIdIso _).hom.app ((scalarSixChange a Z.left).obj M)) =
      (Functor.mapDerivedCategoryNatIso
          (AlgebraicGeometry.ProEtale.CondensedRing.upperStarId Λ'.X Y.left) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app
          ((RootCoordinateFace.lower Λ'.X p.left).obj ((scalarSixChange a Z.left).obj M))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
