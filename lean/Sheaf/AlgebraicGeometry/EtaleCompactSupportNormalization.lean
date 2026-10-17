/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FiniteEtale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

import Sheaf.EtaleCohomology.SepClosedFieldVanishing
import Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.OpenSectionClopen
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint

/-!
# Normalization of compact supports for an etale morphism

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Inclusion of compactly supported sheaf sections into direct image.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def compactificationSheafToDirectImage
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} {f : U ⟶ X}
    (c : Compactification f) :
    openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g ⟶ lowerStar (ModuleCat.{u + 1} A) f :=
  Functor.whiskerRight (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i)
      (lowerStar (ModuleCat.{u + 1} A) c.g) ≫
    (lowerStarComp (ModuleCat.{u + 1} A) c.i c.g f c.comm).hom

/-- The specified sum-extension exchange, descended termwise and inverted.
Source: Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def exactEtaleSumExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        (etaleLowerShriek (ModuleCat.{u + 1} A) (pullback.fst g f)
          inferInstance).mapDerivedCategory :=
  haveI := isIso_etaleLowerShriekBaseChangeMap A g f
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (etaleLowerShriekBaseChangeMap A g f)).symm ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The proper exchange followed by inverse open-extension exchange, using exact derived
inverse image. The transport from `L(g^*)` is the canonical exact-functor comparison.
Source: SGA 4 XVII 5.2.2
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def exactCompactSupportExchange
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⟶
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) :=
  Functor.whiskerLeft (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).inv ≫
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} A)
      (IsPullback.of_hasPullback g f).flip c ≫
    Functor.whiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd g f)).hom _

/-- The compact-support exchange as a 2-square, for canonical pasting.
Source: SGA 4 XVII 5.2.2
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def exactCompactSupportExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    {f : U ⟶ X} (c : Compactification f) (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactCompactSupportExchange A c g)

/-- The specified sum exchange as a 2-square, for the same canonical pasting.
Source: Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def exactEtaleSumExchangeSquare
    (A : Type (u + 1)) [CommRing A] {U X X' : Scheme.{u}}
    (f : U ⟶ X) [Etale f] (g : X' ⟶ X) :=
  TwoSquare.mk _ _ _ _ (exactEtaleSumExchange A f g).hom

/-- A termwise sheaf comparison followed by the total-right-derived comparison.
This is a map on homotopy representatives, with no boundedness condition.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def compactSupportComparisonOnHomotopy
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (c : Compactification f)
    (a : etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj K) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
        (DerivedCategory.Qh.obj K) :=
  (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategoryFactorsh.hom.app K ≫
    DerivedCategory.Qh.map ((a.mapHomotopyCategory (ComplexShape.up ℤ)).app K) ≫
    DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app K) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctorUnit.app
      (((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K) ≫
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategoryFactorsh.inv.app K)

/-- Regard a proper refinement as a compactification of the coarser open immersion.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-etale-compact-support-normalization). -/
def refinementOpenCompactification
    {U X : Scheme.{u}} {f : U ⟶ X} {c d : Compactification f}
    (r : c.Refinement d) : Compactification d.i where
  Z := c.Z
  g := r.hom
  i := c.i
  comm := r.i_hom.symm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- Identity normalization: remove the exact derived direct image of the identity.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-etale-compact-support-normalization). -/
noncomputable def identityEtaleCompactSupportComparison
    (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper (𝟙 X)) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory :=
  Functor.isoWhiskerLeft
      (etaleLowerShriek (ModuleCat.{u + 1} A) (𝟙 X) inferInstance).mapDerivedCategory
      ((lowerStar (ModuleCat.{u + 1} A) (𝟙 X)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
        Functor.mapDerivedCategoryNatIso (lowerStarId (ModuleCat.{u + 1} A) X) ≪≫
        Functor.mapDerivedCategoryIdIso _) ≪≫
    Functor.rightUnitor _

/-- A simultaneous normalization, on all unbounded complexes. The graph-extension equation
specifies the sheaf comparison, and the homotopy equation specifies its derived descent;
neither comparison is an arbitrary isomorphism. Proper refinements are compared using the
same normalized comparison for the coarser open immersion.
Source: SGA 4 XVII 5.2.2, 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization). -/
structure EtaleCompactSupportNormalization (A : Type (u + 1)) [CommRing A] where
  /-- The compact-support-to-sum comparison. -/
  comparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory
  /-- Inverse comparison on sheaves: extend each sheet section by zero off its graph. -/
  sheafComparison : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f),
    etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
        lowerStar (ModuleCat.{u + 1} A) c.g
  /-- The sheaf map is the specified graph-extension map inside direct image. -/
  sheaf_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f) (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
    (sheafComparison f c).app M ≫ (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M
  /-- On every homotopy representative, descend the preceding sheaf map degreewise and
  then apply the total-right-derived unit. -/
  derived_normalization : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (K : HomotopyCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
      (ComplexShape.up ℤ)),
    (comparison f c).inv.app (DerivedCategory.Qh.obj K) =
      compactSupportComparisonOnHomotopy A f c (sheafComparison f c) K
  /-- The actual proper/open exchange agrees with the specified inverse sum exchange. -/
  base_change : ∀ {U X X' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X'] (c : Compactification f) (g : X' ⟶ X),
    exactCompactSupportExchange A c g ≫
        Functor.whiskerLeft
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory
          (comparison (pullback.fst g f)
            (c.ofIsPullback (IsPullback.of_hasPullback g f).flip)).hom =
      Functor.whiskerRight (comparison f c).hom
          (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≫
        (exactEtaleSumExchange A f g).hom
  /-- Compatibility for two changes of base, with the canonical pasting associators.
  The exchanges are the specified maps, so this is compatibility with their composite. -/
  composition : ∀ {U X X' X'' : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [QuasiCompact f] [IsLocallyNoetherian U] [CompactSpace U]
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian X'] [CompactSpace X']
    [IsLocallyNoetherian X''] [CompactSpace X'']
    (c : Compactification f) (g : X' ⟶ X) (k : X'' ⟶ X'),
    ((exactCompactSupportExchangeSquare A c g).vComp
        (exactCompactSupportExchangeSquare A
          (c.ofIsPullback (IsPullback.of_hasPullback g f).flip) k)).natTrans ≫
      Functor.whiskerLeft
        ((upperStar (ModuleCat.{u + 1} A) (pullback.snd g f)).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} A)
            (pullback.snd k (pullback.fst g f))).mapDerivedCategory)
        (comparison (pullback.fst k (pullback.fst g f))
          ((c.ofIsPullback (IsPullback.of_hasPullback g f).flip).ofIsPullback
            (IsPullback.of_hasPullback k (pullback.fst g f)).flip)).hom =
      Functor.whiskerRight (comparison f c).hom
        ((upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
          (upperStar (ModuleCat.{u + 1} A) k).mapDerivedCategory) ≫
        ((exactEtaleSumExchangeSquare A f g).vComp
          (exactEtaleSumExchangeSquare A (pullback.fst g f) k)).natTrans
  /-- Under a proper refinement, use the comparison for the coarser open immersion,
  normalized by graph extension (hence identity over U), and then compose direct images. -/
  refinement : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c d : Compactification f) (r : c.Refinement d)
    [IsLocallyNoetherian d.Z] [CompactSpace d.Z],
    Functor.whiskerRight (comparison d.i (refinementOpenCompactification r)).inv
        (lowerStar (ModuleCat.{u + 1} A) d.g).rightDerivedFunctor ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar (ModuleCat.{u + 1} A) r.hom)
          (lowerStar (ModuleCat.{u + 1} A) d.g)
          (lowerStarComp (ModuleCat.{u + 1} A) r.hom d.g c.g r.hom_g.symm)).hom ≫
      (comparison f c).hom = (comparison f d).hom
  /-- For an identity morphism the normalized comparison is the identity after removing
  the identity functor. Refinement compatibility supplies every other compactification. -/
  identity : ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X],
    comparison (𝟙 X) (Compactification.ofIsProper (𝟙 X)) =
      identityEtaleCompactSupportComparison A X
  /-- Every chosen compact-support adjunction is identified with the degreewise
  sum/evaluation adjunction, with the unique counit-preserving right-adjoint comparison. -/
  adjunction : ∀ {U X : Scheme.{u}} (f : U ⟶ X) [Etale f] [IsSeparated f]
    [IsLocallyNoetherian U] [CompactSpace U] [IsLocallyNoetherian X] [CompactSpace X]
    (c : Compactification f)
    (R : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣ R),
    ∃! e : R ≅ (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory,
      Functor.whiskerLeft R (comparison f c).hom ≫
        Functor.whiskerRight e.hom
          (etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).mapDerivedCategory ≫
        (Adjunction.mapDerivedCategoryAdjunction
          (etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) f inferInstance)).counit =
        adj.counit

/-- The canonical compact-support-to-sum normalization, including its degree-zero,
refinement, sum/evaluation adjunction, base-change and identity/composition normalizations.
Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tag 03S6
(blueprint: lem-asd-etale-compact-support-normalization).

Proof:
1. Apply sum extension and inverse image degreewise, using exactness from
   lem-weil-pbc-etale-restriction-injectives. Descend their unit, evaluation counit and
   triangles by lem-weil-pbc-termwise-adjunction-homotopy and
   lem-weil-pbc-localization-universal-property. Descend the specified etale beta and its
   inverse using lem-weil-pbc-etale-shriek-base-change-modules.
2. In V = Z times_X U the graph of j is open (etale diagonal) and closed (a section of the
   proper projection). Use lem-weil-pbc-open-section-clopen. Restriction to the two clopen
   components gives the canonical projection q^*M to extension from the graph.
3. Pull back sum extension to Z by the specified inverse beta, project to the graph and
   compose left adjoints. Transpose under r^* adjoint to Rr_* to construct a from derived
   sum extension to compact support before asserting invertibility.
4. Pull this construction back along g. On graph components both maps are identity and
   on their complements both are zero. Mate pasting and localization descend this equality
   of sheaf transformations to all complexes. Transposition yields C g^*a = a' C_sum.
5. At a geometric point use unbounded torsion proper base change
   (lem-kun-proper-base-change-torsion-ring). By lem-kun-0ezp the fibre is a finite disjoint
   union of field points. It is clopen in the compactification. Pushforward on it is the
   exact finite product, equal to the finite sum; the graph construction is its identity.
   Resolve the two clopen factors independently by K-injectives. The complement is zero.
   Exact conservative stalks and lem-weil-pbc-unbounded-derived-iso-cohomology show a is
   invertible on every complex, including the empty fibre. Put c = a inverse.
6. On sheaves a extends each summand by zero off its graph. Its support is closed in the
   graph, hence proper over the test scheme. The inverse recovers the sheet components.
   The sheaf_normalization equation records precisely this map into direct image.
7. For a refinement, restrict to the coarser open, apply proper exchange and project to
   the clopen graph component. Transpose to obtain the identity-normalized comparison.
   It is invertible by the same fibre calculation. Composing derived direct images gives
   rho; transposition of the graph projections gives rho a₂ = a₁ and hence c₁ rho = c₂.
   Identity and composition laws follow by cancellation.
8. Transport the degreewise sum/evaluation adjunction through c. The conjugacy bijection
   gives the unique right-adjoint isomorphism preserving the specified counit, for every
   chosen compact-support right adjoint (thm-amb-etale-exceptional-adjoint).
9. Invert a in step 4 to obtain the displayed base-change square. Identity comparisons
   and pasted comparisons are identities and composites by mate pasting, conjugacy of beta
   and localization. For the identity morphism the graph map is identity after removing
   the identity functors; step 7 handles its other compactifications. -/
theorem nonempty_etaleCompactSupportNormalization
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    Nonempty (EtaleCompactSupportNormalization A) := by
  sorry

end AlgebraicGeometry.Etale
