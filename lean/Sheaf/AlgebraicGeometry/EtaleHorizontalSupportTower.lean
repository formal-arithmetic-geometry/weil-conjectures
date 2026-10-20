/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F9
-/
module

public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso

/-! # The normalized compactification tower for etale horizontal composition

Source: Stacks Project, Tags 0F7B, 0F7F, 0F7J and 0F7L
(blueprint: lem-pur-etale-horizontal-support-tower).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- The statement uses these constructions through their interfaces.
attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- The canonical graph comparisons put compact-support composition in the proper/open
compactification normal form. This identity is before either horizontal counit is applied.
The proper factor is the right-adjoint mate of inverse etale sum exchange under the
inverse-image/direct-image adjunctions. In particular it does not involve inverse proper
base change, or the full compact-support exchange for f.
Source: Stacks Project, Tags 0F7B and 0F7F for proper/quasi-finite interchange,
Tag 0F7J for composition, and Tag 0F7L, item (3), for its base-change compatibility;
Tag 0F4L for the canonical graph comparison
(blueprint: lem-pur-etale-horizontal-support-tower).

Proof in words:
1. Choose a compactification d of v' followed by f, and set e=d.ofComp c. For the
   other factorization use d transported by sq.w, a compactification q of v, and its
   ofComp tower. Expand both composition maps by their proper/open tower equations.
   The comparison cocycles and the equality of the two composites identify their
   terminal models through a common proper refinement.
2. For an etale map the inverse canonical comparison is the explicit derived graph
   map. At the sheaf level its composite into direct image extends a sheet section
   by zero from its clopen graph. Restricting this graph along j and along j' gives
   the same graph. Its section is unchanged there and zero on the complement.
   Transpose under the two sum/evaluation adjunctions: the resulting open factor is
   the unique composite-left-adjoint comparison a for the inverse-image square.
3. The remaining proper/quasi-finite interchange is the map of Tag 0F7B. On a
   K-injective complex I on the upper left scheme, resolve the extension by zero
   along the upper horizontal arrow by a K-injective complex K. The map is the
   composite of the common proper-support identification on I with the direct
   image of that resolution map. The sheaf identification is specified by the common
   proper-support inclusion. Its inverse-image transpose is inverse etale sum
   exchange: restriction pulls a sheet and its section to the pulled-back sheet.
   On that graph both constructions are the same section, and off it both are zero.
   The sheaf axiom and sum-presheaf sheafification prove equality of these sheaf
   arrows. Thus transposition under the two proper inverse-image/direct-image
   adjunctions gives precisely gam, with the direction in the statement.
4. Apply the equal sheaf arrows degreewise, followed by the total-derived units.
   The formula compactSupportDerivedComparison_app fixes the derived graph maps on
   every homotopy representative. Represent proper direct images by K-injectives
   and resolve each open or sum extension before its next direct image. Naturality
   of the units and the unit characterization of derived direct-image composition
   identify the two resulting morphisms. Localization makes this an equality of
   natural transformations on the entire unbounded categories.
5. Canonical graph refinement coherence and the normalized proper-refinement
   equation cancel the refining towers. Associate the surviving factors to obtain
   S_v(t' inverse), gam at J'(M), P(a at M), and t at S_v'(M). Identity graphs use
   the graph identity and direct-image right unit; empty graphs and zero
   coefficients give zero on both sides. No equality of derived morphisms is
   inferred merely from agreement of their stalk maps. -/
theorem etaleHorizontalSupport_tower
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {v : Y' ⟶ Y} {v' : X' ⟶ X}
    [IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    [LocallyOfFiniteType v] [LocallyOfFiniteType v']
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification f] [HasCompactification f'] [HasCompactification v]
    [HasCompactification v'] [HasCompactification (v' ≫ f)]
    [HasCompactification (f' ≫ v)] [QuasiCompact (v' ≫ f)]
    [QuasiCompact (f' ≫ v)] (sq : IsPullback v' f' f v)
    (c : Compactification f)
    [IsIso (((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g v) inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).hom)).natTrans)]
    (M : DerivedCategoryModule A X') :
    let cs := c.ofIsPullback sq
    let va := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v' inferInstance
    let ba := derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      (pullback.fst c.g v) inferInstance
    let ja := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) c.i
    let j'a := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) cs.i
    let a := (conjugateIsoEquiv (va.comp ja) (j'a.comp ba)).symm
      (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (c.isPullback_i_ofIsPullback sq).toCommSq.flip)
    let sumEx := ((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.fst c.g v) inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        (IsPullback.of_hasPullback c.g v).toCommSq).hom)).natTrans
    let gam := (mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A)
        (pullback.snd c.g v))
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
      (TwoSquare.mk _ _ _ _ (inv sumEx))).natTrans
    let dv' := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v')).symm ≪≫
        canonicalEtaleCompactSupportComparison A v' (HasCompactification.compactification v')
    let dv := (rightDerivedLowerShriekIso A
      (HasCompactification.compactification v)).symm ≪≫
        canonicalEtaleCompactSupportComparison A v (HasCompactification.compactification v)
    let delta := Functor.isoWhiskerRight dv'.symm
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f) ≪≫
        unboundedEtaleLowerShriekCompIso A v' f ≪≫
        unboundedEtaleLowerShriekCongr A sq.toCommSq.w ≪≫
        (unboundedEtaleLowerShriekCompIso A f' v).symm ≪≫
        Functor.isoWhiskerLeft
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f') dv
    delta.inv.app M =
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriekIso A cs).inv.app M) ≫
        gam.app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} A) cs.i).mapDerivedCategory.obj M) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
          (a.hom.app M) ≫
        (rightDerivedLowerShriekIso A c).hom.app
          ((etaleLowerShriek (ModuleCat.{u + 1} A) v' inferInstance).mapDerivedCategory.obj M) := by
  sorry

end AlgebraicGeometry.Etale
