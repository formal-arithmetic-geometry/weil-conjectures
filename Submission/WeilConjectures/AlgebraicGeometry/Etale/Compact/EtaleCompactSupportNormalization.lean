/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement

public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
public import Submission.WeilConjectures.SixFunctors.BaseChange.Etale
public import Submission.WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Submission.WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import Submission.WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Submission.WeilConjectures.SixFunctors.OpenClosed.Conservative
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
import Submission.WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

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

end AlgebraicGeometry.Etale
