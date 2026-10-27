/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.SixFunctors.CompositionProjectionData
public import Sheaf.Paper.FiniteSiteTowerPaste

/-! # Inclusion of a Cartesian proper/open tower into the ambient derived category

Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sf-cartesian-tower-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
namespace CartesianTower

variable (A : Type (u + 1)) [CommRing A]

/-- The specified inclusion comparison for the four-factor source word.
Source: the canonical D+ inclusion compatibilities (Stacks 0F7J)
(blueprint: lem-sf-cartesian-tower-restriction). -/
@[irreducible] def sourceInclusion {X V Y B Z : Scheme.{u}}
    (j : X ⟶ V) (q : V ⟶ Y) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion j] [IsOpenImmersion i]
    (M : FiniteSiteTower.DP A X) :=
  (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctorPlusCompatibility.app
      ((FiniteSiteTower.JP A i).obj ((FiniteSiteTower.PP A q).obj
        ((FiniteSiteTower.JP A j).obj M))) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) s).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategoryPlusCompatibility.app
          ((FiniteSiteTower.PP A q).obj ((FiniteSiteTower.JP A j).obj M)) ≪≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) i).mapDerivedCategory.mapIso
          ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctorPlusCompatibility.app
              ((FiniteSiteTower.JP A j).obj M) ≪≫
            (lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor.mapIso
              ((openImmersionLowerShriek
                (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.app M)))

/-- The specified inclusion comparison for the two-factor output word.
Source: the canonical D+ inclusion compatibilities (Stacks 0F7J)
(blueprint: lem-sf-cartesian-tower-restriction). -/
@[irreducible] def targetInclusion {X W Z : Scheme.{u}}
    (j : X ⟶ W) (p : W ⟶ Z) [IsOpenImmersion j]
    (M : FiniteSiteTower.DP A X) :=
  (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.app
      ((FiniteSiteTower.JP A j).obj M) ≪≫
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlusCompatibility.app M)

end CartesianTower

/-- The raw Cartesian mate tower restricts to the specified site-interchange tower.
This contains no compactification comparison or canonical compact-support compositor.
Source: Stacks 0F7B, proper/open interchange, and 0F7J, compatible triangle
(blueprint: lem-sf-cartesian-tower-restriction).

Proof: The map from V into the fibre product W x_B Y is an isomorphism because the
square is Cartesian. Therefore the clopen projector in properOpenAlpha is the identity.
Take its two proper adjunction mates and then its open adjunction mate. The open unit
normalization of beta and the proper triangle identity show that this adjunct is the
inverse of restriction exchange followed by the inverse open unit. The specified
properOpenSiteInterchange has precisely this adjunct by properOpen_site_mate and the
canonical site/open comparison, so injectivity of the open Hom equivalence
identifies the maps. At J_j nu^*E use the canonical open site comparison to change the
witness, which gives GP. Transport the proper compositor through the D+ inclusion by
adjunction conjugacy, and the open compositor by the exact-derived comparison. Expand
alpha and AP, paste the three squares, and cancel the intermediate inclusion
isomorphisms. The two surviving boundary isomorphisms are sourceInclusion and
targetInclusion, by their displayed definitions. This argument also covers empty opens:
the same units and triangle identities hold for the zero extension functor. -/
theorem cartesianTowerRestriction
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (E : FiniteSiteTower.DE A X.obj.left) :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    letI : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    letI : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
    letI : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
    letI : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
    letI : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
    letI : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    letI : IsOpenImmersion (j ≫ b).hom.left :=
      mappedCompositeOpen (geo := geometry F) j b
    letI : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
    DerivedCategory.Plus.ι.map
        (FiniteSiteTower.AP A j.hom.left b.hom.left p.hom.left s.hom.left i.hom.left
          q.hom.left sq E) ≫
      (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom =
    (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (alpha (ordinary F A) j b q p i s hb).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X.obj.left).mapDerivedCategory.obj
          E.obj) := by sorry

end AlgebraicGeometry.ProEtale
