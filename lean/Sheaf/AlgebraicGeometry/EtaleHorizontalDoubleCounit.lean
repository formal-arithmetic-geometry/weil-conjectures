/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-!
# Double counits in an etale-horizontal square

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md, Step 1;
Stacks Project, Tags 0037, 0DV0, 0F7J, 0F7K, 0F7L and 03S6
(blueprint: lem-pur-etale-horizontal-double-counit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The right-adjoint restriction comparison determined by inverse compact-support exchange.
Source: Stacks Project, Tags 0037 and 0F7L
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalCounitRightExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [HasCompactification h] [HasCompactification h'] [QuasiCompact h']
    (sq : IsPullback e' h' h e)
    {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
    (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G') :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  (mateEquiv adj adj'
    (TwoSquare.mk _ _ _ _ (etaleHorizontalSupportBaseChangeIso A sq).inv)).natTrans

section Square

variable (A : Type (u + 1)) [CommRing A] [Finite A]
  {X X' Y Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
  {h : X ⟶ Y} {h' : X' ⟶ Y'} {e : Y' ⟶ Y} {e' : X' ⟶ X}
  [IsSeparated h] [IsSeparated h'] [IsSeparated e] [IsSeparated e']
  [Etale e] [Etale e']
  [LocallyOfFiniteType h] [LocallyOfFiniteType h']
  [QuasiCompact h] [QuasiCompact h'] [QuasiCompact e] [QuasiCompact e']
  [HasCompactification h] [HasCompactification h']
  [HasCompactification e] [HasCompactification e']
  [HasCompactification (e' ≫ h)] [HasCompactification (h' ≫ e)]
  (sq : ChosenCartesianSquare e' h' h e) (N : EtaleCompactSupportNormalization A)
  {G : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
  {G' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
  (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h ⊣ G)
  (adj' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) h' ⊣ G')

/-- Conjugate the specified inverse delta under the two normalized composite adjunctions.
This is the map b of the node; the compositor formula is recorded below.
Source: Stacks Project, Tags 0037 and 0DV0
(blueprint: lem-pur-etale-horizontal-double-counit). -/
noncomputable def etaleHorizontalDoubleCounitIso :
    G ⋙ (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙ G' :=
  conjugateIsoEquiv
    ((derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e' inferInstance).comp adj)
    (adj'.comp (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance))
    (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).symm

/-- Double-counit equality, single-counit equality, and the unique adjunct description.
Source: blueprint co-smooth etale locality, Step 1; Stacks 0037, 0DV0 and 0F7K
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: (1) conjugacy of d inverse preserves the evaluation/counit normalization.
(2) Conjugate the difference of the two compositors, using contravariant composition.
(3) Change from the compact-support adjunctions to the sum/evaluation adjunctions;
mate pasting identifies the resulting conjugate with b and the left map with delta inverse.
(4) Expand both composite counits by Adjunction.comp to obtain the first equality.
(5) Apply lem-pur-etale-horizontal-support-mate at G K and use counit naturality.
(6) Cancel the inverse hom bijection for the sum adjunction, obtaining the second
identity. The hom bijection for adj' gives the unique adjunct assertion.
(7) Refinement comparisons preserve d and the compositors; conjugacy preserves their
counits, so the identities transport under refinement.
(8) Exchange pasting and lem-pur-etale-support-map-compatibility identify the two
restricted mates; the sum/evaluation adjunction is the same after open restriction.
No evaluation counit is cancelled as an isomorphism. -/
theorem etaleHorizontalDoubleCounit :
    ∀ K : DerivedCategoryModule A Y,
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
              ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
            adj'.counit.app
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ≫
        (derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K =
      (etaleHorizontalSupportMateDelta A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) N).inv.app
          ((upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory.obj (G.obj K)) ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) h).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance).counit.app (G.obj K)) ≫
        adj.counit.app K) ∧
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) h').map
          ((etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) ≫
        adj'.counit.app
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) =
      (etaleHorizontalSupportBaseChangeIso A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
        (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map (adj.counit.app K)) ∧
      (adj'.homEquiv _ _
        ((etaleHorizontalSupportBaseChangeIso A
          (IsPullback.of_iso_pullback sq.toCommSq
            sq.isoPullback sq.hom_fst sq.hom_snd)).inv.app (G.obj K) ≫
          (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
            (adj.counit.app K)) =
        (etaleHorizontalDoubleCounitIso A sq N adj adj').hom.app K) := by
  sorry

/-- The explicit formula rho inverse, inverse first conjugate compositor, second
conjugate compositor, and rho. A common right adjoint for the equal composites is
arbitrary, and both occurrences use the same adjunction.
Source: Stacks 0037 and 0DV0, blueprint co-smooth etale locality Step 1
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: conjugate alpha for each composite adjunction. Contravariance identifies the
middle two factors with the conjugate of alpha_h inverse after alpha_e. Mate pasting
moves d_e inverse and d_e' across the composite adjunctions. These are exactly rho_e
and rho_e' inverse, respectively, giving the defining conjugate of delta inverse. -/
theorem etaleHorizontalDoubleCounit_compositors
    {Ge : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A Y'}
    {Ge' : DerivedCategoryModule A X ⥤ DerivedCategoryModule A X'}
    {Gd : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X'}
    (ae : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ Ge)
    (ae' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e' ⊣ Ge')
    (ad : rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e' ≫ h) ⊣ Gd) :
    etaleHorizontalDoubleCounitIso A sq N adj adj' =
      Functor.isoWhiskerLeft G
        (conjugateIsoEquiv ae'
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e' inferInstance)
          (etaleCanonicalCompactSupportComparison A e' N).symm).symm ≪≫
      (conjugateIsoEquiv ad (ae'.comp adj)
        (unboundedEtaleLowerShriekCompIso A e' h)).symm ≪≫
      conjugateIsoEquiv ad (adj'.comp ae)
        (unboundedEtaleLowerShriekCompIso A h' e ≪≫
          (unboundedEtaleLowerShriekCongr A sq.toCommSq.w).symm) ≪≫
      Functor.isoWhiskerRight
        (conjugateIsoEquiv ae
          (derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance)
          (etaleCanonicalCompactSupportComparison A e N).symm) G' := by
  sorry

/-- Equality of natural transformations, making naturality in K explicit.
Source: blueprint co-smooth etale locality Step 1 and Stacks 0037
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: the single-counit identity identifies the two transformations under the
adjunction hom bijection, component by component; injectivity gives equality. -/
theorem etaleHorizontalDoubleCounit_exchange :
    (etaleHorizontalDoubleCounitIso A sq N adj adj').hom =
      etaleHorizontalCounitRightExchange A (IsPullback.of_iso_pullback sq.toCommSq
        sq.isoPullback sq.hom_fst sq.hom_snd) adj adj' := by
  sorry

/-- Compatibility with proper-refinement comparisons for both vertical arrows.
The fixed-compactification adjunctions are transported to the shared compact-support
functor, and the right comparisons are conjugates of the inverse refinement maps.
Source: Stacks 0F7I, 0F7J, 0F7K and 0GKM
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: the comparison cocycle identifies the common-refinement isomorphism with the
specified refinement map. Its conjugate preserves the counit. Substitute the refinement
identities for d and alpha into delta; adjacent comparison inverses cancel. Conjugacy
then gives the displayed square, independently of either normalization family. -/
theorem etaleHorizontalDoubleCounit_refinement
    (M : EtaleCompactSupportNormalization A)
    (c d : Compactification h) (_r : c.Refinement d)
    (c' d' : Compactification h') (_r' : c'.Refinement d')
    {H : DerivedCategoryModule A Y ⥤ DerivedCategoryModule A X}
    {H' : DerivedCategoryModule A Y' ⥤ DerivedCategoryModule A X'}
    (ac : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ G)
    (ad : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d ⊣ H)
    (ac' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c' ⊣ G')
    (ad' : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d' ⊣ H') :
    Functor.whiskerRight
        (conjugateIsoEquiv ac ad
          (rightDerivedLowerShriekOfCompactificationIso A d c)).hom
        (upperStar (ModuleCat.{u + 1} A) e').mapDerivedCategory ≫
      (etaleHorizontalDoubleCounitIso A sq M
        (ad.ofNatIsoLeft (rightDerivedLowerShriekIso A d))
        (ad'.ofNatIsoLeft (rightDerivedLowerShriekIso A d'))).hom =
    (etaleHorizontalDoubleCounitIso A sq N
        (ac.ofNatIsoLeft (rightDerivedLowerShriekIso A c))
        (ac'.ofNatIsoLeft (rightDerivedLowerShriekIso A c'))).hom ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
        (conjugateIsoEquiv ac' ad'
          (rightDerivedLowerShriekOfCompactificationIso A d' c')).hom := by
  sorry

/-- The comparison square for a further compatible Cartesian open restriction.
The vertical restriction maps on right adjoints are exactly the mates of inverse
compact-support exchange, with the same evaluation normalization as the original b.
Source: Stacks 0F7L and 03S6, blueprint co-smooth etale locality Step 1
(blueprint: lem-pur-etale-horizontal-double-counit).

Proof: write the two pasted inverse-exchange squares for the Cartesian cube. They agree
by compatibility of compact-support exchange with successive changes of base. Apply mate
pasting to their equality. The single-counit identity identifies the horizontal mates
with b and its restriction, while the vertical mates are the specified restriction maps.
The canonical inverse-image square isomorphisms give the two remaining factors. The
sum/evaluation normalization is preserved by degreewise open restriction, since both
operations evaluate the same restricted lift; support-map compatibility identifies d.
Thus the double and single counit identities transport along this comparison square. -/
theorem etaleHorizontalDoubleCounit_openRestriction
    {V V' W W' : Scheme.{u}}
    [IsNoetherian V] [IsNoetherian V'] [IsNoetherian W] [IsNoetherian W']
    {k : V ⟶ W} {k' : V' ⟶ W'} {v : W' ⟶ W} {v' : V' ⟶ V}
    [IsSeparated k] [IsSeparated k'] [IsSeparated v] [IsSeparated v']
    [Etale v] [Etale v'] [LocallyOfFiniteType k] [LocallyOfFiniteType k']
    [QuasiCompact k] [QuasiCompact k'] [QuasiCompact v] [QuasiCompact v']
    [HasCompactification k] [HasCompactification k']
    [HasCompactification v] [HasCompactification v']
    [HasCompactification (v' ≫ k)] [HasCompactification (k' ≫ v)]
    (barsq : ChosenCartesianSquare v' k' k v)
    (jX : V ⟶ X) (jX' : V' ⟶ X') (jY : W ⟶ Y) (jY' : W' ⟶ Y')
    [IsOpenImmersion jX] [IsOpenImmersion jX']
    [IsOpenImmersion jY] [IsOpenImmersion jY']
    (leftsq : IsPullback jX k h jY) (rightsq : IsPullback jX' k' h' jY')
    (topsq : CommSq v' jX' jX e') (bottomsq : CommSq v jY' jY e)
    {H : DerivedCategoryModule A W ⥤ DerivedCategoryModule A V}
    {H' : DerivedCategoryModule A W' ⥤ DerivedCategoryModule A V'}
    (a : rightDerivedLowerShriek (ModuleCat.{u + 1} A) k ⊣ H)
    (a' : rightDerivedLowerShriek (ModuleCat.{u + 1} A) k' ⊣ H') :
    Functor.whiskerRight (etaleHorizontalDoubleCounitIso A sq N adj adj').hom
        (upperStar (ModuleCat.{u + 1} A) jX').mapDerivedCategory ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
        (etaleHorizontalCounitRightExchange A rightsq adj' a') =
    Functor.whiskerLeft G
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) topsq).hom ≫
      Functor.whiskerRight (etaleHorizontalCounitRightExchange A leftsq adj a)
        (upperStar (ModuleCat.{u + 1} A) v').mapDerivedCategory ≫
      Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) jY).mapDerivedCategory
        (etaleHorizontalDoubleCounitIso A barsq N a a').hom ≫
      Functor.whiskerRight
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) bottomsq).inv H' := by
  sorry

end Square

end AlgebraicGeometry.Etale
