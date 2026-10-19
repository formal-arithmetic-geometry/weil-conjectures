/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.SfFiniteOpenExtensionBaseChange
public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint
import Sheaf.AlgebraicGeometry.ExceptionalBaseChangeReducesToProper
import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange
import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
import Sheaf.Paper.EtaleCoefficientSystemAdjoint
import Sheaf.Paper.FullCDClassRestriction
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# Exceptional base change along an arbitrary open immersion

Source: Weil blueprint, order 1815, sk-prop-sf-existence
(blueprint: cor-exc-base-change-open-immersion-general).
The ambient assertion and the independent coefficient-class assertion are separate.
The former uses the given ordinary unbounded adjunctions. The latter uses only the
specified transported etale exceptional functor. No quasi-compactness of the open
immersion is imposed in the ambient assertion.

## Main statements

- `sfAmbientExceptionalOpenBaseChange`: the ordinary ambient comparison and restricted
  FullCD bound, using the supplied adjunction and the base-changed compactification.
- `sfFiniteExceptionalOpenBaseChange`: the independent comparison for degree-zero
  etale-origin sheaves and bounded constructible complexes.

The support and realization comparisons below specify the canonical maps in these statements.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The exact open extension-by-zero comparison in the two recorded presentations.
It cancels the unit of the specified realization equivalence.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicOpenExtensionComparison (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence U A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- Canonical realization of the compact-support candidate, fixed on constant sections
and on K-injective representatives by sfIntrinsicDerivedDirectImageComparison.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicCompactSupportComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      sfFixedCompactSupport A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A c.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The given ambient right adjoint in the canonically equivalent fixed-scalar category.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedAmbientRightAdjoint (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (D : SfAmbientExceptionalRightAdjointDatum A f c) (d : Compactification f) :=
  (sfIntrinsicDerivedEquivalence Y A).functor ⋙ D.rightAdjoint d ⋙
    (sfIntrinsicDerivedEquivalence X A).inverse

/-- Transport of the actual supplied adjunction, with its units and counits.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedAmbientAdjunction (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    (D : SfAmbientExceptionalRightAdjointDatum A f c) (d : Compactification f) :
    sfFixedCompactSupport A d ⊣ sfFixedAmbientRightAdjoint A D d :=
  (((sfIntrinsicDerivedEquivalence X A).toAdjunction.comp (D.adjunction d)).comp
    (sfIntrinsicDerivedEquivalence Y A).symm.toAdjunction).ofNatIsoLeft
      (Functor.isoWhiskerRight (sfIntrinsicCompactSupportComparison A d) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (sfIntrinsicDerivedEquivalence Y A).unitIso.symm ≪≫
        Functor.rightUnitor _)

/-- The specified compactification support exchange. The first arrow is the proper
ordinary derived direct-image mate, and the second is the inverse extension-by-zero
mate, applied degreewise. This defines a map even before its invertibility is proved.
Source: blueprint order 1815, proof Steps 1-4; Stacks Tags 0F7B and 0F7C
(blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    sfFixedCompactSupport A c ⋙ sfFixedDerivedPullback A g ⟶
      sfFixedDerivedPullback A g' ⋙ sfFixedCompactSupport A (c.ofIsPullback sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (sfFixedDerivedBaseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (sfFixedDerivedOpenExtensionBaseChangeIso A (c.isPullback_i_ofIsPullback sq)).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The actual exceptional comparison: the mate of the inverse specified support
exchange under the transported supplied ambient adjunctions. Its proof parameter only
certifies invertibility of the already defined support exchange; it supplies no map.
Source: blueprint order 1815, proof Step 4
(blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfAmbientExceptionalOpenComparison (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum A f c)
    (D' : SfAmbientExceptionalRightAdjointDatum A f' (c.ofIsPullback sq))
    [hEx : IsIso (sfFixedCompactSupportExchange A sq c)] :
    sfFixedAmbientRightAdjoint A D c ⋙ sfFixedDerivedPullback A g' ⟶
      sfFixedDerivedPullback A g ⋙ sfFixedAmbientRightAdjoint A D' (c.ofIsPullback sq) :=
  mateEquiv (sfFixedAmbientAdjunction A D c)
    (sfFixedAmbientAdjunction A D' (c.ofIsPullback sq))
    (inv (sfFixedCompactSupportExchange A sq c))

/-- Exceptional base change on the whole ordinary derived categories, conditional on
exactly the supplied ambient datum. The existential bound is the same before and after
base change, and the new datum uses the base-changed compactification.
Source: blueprint order 1815, first clause and proof Steps 1-4
(blueprint: cor-exc-base-change-open-immersion-general).
Proof: use the compactification already in D, not Nagata over the arbitrary base S.
The proper part is finite type over S, so lem-sp-fullcd-ambient-adjoint applies to its
identity-open compactification. Pull back the compactification; properness, separatedness
and finite type are stable under base change, with no quasi-compactness requirement on g.
Extend every sheaf on the new proper source by zero. The two clauses of the original
FullCD bound, evaluated on the open base and on each of its weakly-etale objects, give
the identical bound for the new proper part. Apply lem-sp-fullcd-ambient-adjoint there.
Give the closed complement its reduced induced structure and apply the conditional
proper comparison prop-exc-base-change-proper. Finally
cor-exc-base-change-reduces-to-proper identifies its open paste with the displayed mate
and proves that mate invertible. An affine open is an instance of the same open g. -/
theorem sfAmbientExceptionalOpenBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum (Padic.coefficientExtensionRing l E (n + 1)) f c)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] :
    ∃ c_cd : ℕ,
      sfFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E (n + 1)) c_cd ∧
      sfFullCohomologicalDimension
        (c.ofIsPullback (IsPullback.of_hasPullback f g)).g
        (Padic.coefficientExtensionRing l E (n + 1)) c_cd ∧
      ∃ D' : SfAmbientExceptionalRightAdjointDatum
          (Padic.coefficientExtensionRing l E (n + 1)) (pullback.snd f g)
          (c.ofIsPullback (IsPullback.of_hasPullback f g)),
        ∃ hEx : IsIso (sfFixedCompactSupportExchange
            (Padic.coefficientExtensionRing l E (n + 1)) (IsPullback.of_hasPullback f g) c),
          IsIso (sfAmbientExceptionalOpenComparison
            (Padic.coefficientExtensionRing l E (n + 1)) (IsPullback.of_hasPullback f g)
            c D D' (hEx := hEx)) := by
  sorry

/-- The independent finite-coefficient comparison on the two stated input classes.
In particular a degree-zero sheaf need not be finite or constructible. There is no
ambient datum in this assertion. The compactification is arbitrary; its base change
is used on the right, as in the defining finite-level construction.
Source: blueprint order 1815, second clause and proof Steps 5-7
(blueprint: cor-exc-base-change-open-immersion-general).
Proof: finite-type schemes over the algebraic closure of a finite field are Noetherian.
Their open subschemes and the compactification are again finite type, and a finite
bound on the dimension exists. Thus thm-sf-ambient-adjoint-class supplies the relative
Hom bijections on bounded-below etale-origin complexes, independently of any ambient
adjunction. Transport the etale proper/open interchange through the specified proper
comparison and extension-by-zero comparison; its five arrows are all invertible.
Full faithfulness of comparison on D⁺ makes this independent of the etale witness.
Paste the open extensions using the unique comparison of their adjunctions. This gives
the canonical support interchange Θ. For every test M in the full etale-origin class,
transpose successively through g'_! ⊣ g'^*, the relative f adjunction, Θ, g_! ⊣ g^*,
and the relative f' adjunction. This gives a natural bijection
Hom(M,g'^*Rf!K) ≃ Hom(M,Rf'!g^*K). Its action is postcomposition with the displayed
comparison: expand the units and counits to identify it with the mate of the reverse
support exchange. Both endpoints are in this full class. Surjectivity on Hom from the
right endpoint and injectivity on Hom from the left give a two-sided inverse. This
argument applies to every degree-zero etale-origin sheaf and to every bounded
constructible K, which has an etale-origin witness. It uses the entire bounded-below
complex, so no sheaf-only extension or truncation argument is assumed. -/
theorem sfFiniteExceptionalOpenBaseChange
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (_hK :
      (∃ F : Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))),
        (comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
          Y).essImage F ∧
        Nonempty ((DerivedCategory.singleFunctor _ 0).obj F ≅ K)) ∨
      intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) Y
        ((sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
          K)) :
    IsIso (sfFiniteExceptionalOpenComparison (Padic.coefficientExtensionRing l E (n + 1))
      (IsPullback.of_hasPullback f g) c K) := by
  sorry

end AlgebraicGeometry.ProEtale
