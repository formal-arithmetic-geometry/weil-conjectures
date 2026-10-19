/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.AlgebraicGeometry.AmbientExceptionalRightAdjoint
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison
public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge
public import Sheaf.Paper.EtaleOriginDerivedCategory
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ExceptionalBaseChangeCartesianOpenInjectiveAcyclic
import Sheaf.CategoryTheory.FiniteCohomologicalDimensionAcyclicComplex
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.UnboundedProperOpenInterchange
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.AlgebraicGeometry.ProEtaleComparisonPullbackSections
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin
import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom

/-!
# Proper exceptional inverse image and arbitrary open restriction

Source: blueprint main-20261015, sk-prop-sf-existence,
prop-exc-base-change-proper, with the reviewed stage-1 repair of Steps 1–8
(blueprint: prop-exc-base-change-proper).

The ambient adjunction and the relative etale-origin assertion have separate hypotheses.
The proper/open map is fixed by sectionwise restriction and the open adjunctions.

## Main definitions

* `sfProperOpenDerivedComparison`: the canonical proper/open support arrow Γ.
* `sfProperExceptionalOpenComparison`: its double-transpose exceptional comparison β.
* `sfProperEtaleOriginFixedForgetful`: canonical coefficient realization of the recorded
  bounded-below etale-origin category.

## Main statements

* `sfProperExceptionalOpenBaseChange`: the conditional unbounded ambient assertion.
* `sfProperFiniteExceptionalOpenBaseChange`: the independent etale-origin assertion.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Proper normalization at the identity-open compactification. The identity extension
is the unique unit-compatible left adjoint to identity restriction, so this fixes the
normalization of the left adjoint and its counit.
Source: blueprint prop-exc-base-change-proper, Step 1
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperSupportNormalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : sfAmbientCompactSupportCandidate A (Compactification.ofIsProper f) ≅
      proEtaleConstantDerivedDirectImage f A :=
  isoWhiskerRight (sfIntrinsicDerivedOpenId A X) _ ≪≫ Functor.leftUnitor _

/-- The given ambient right adjoint, with the actual adjunction transported along the
identity-open normalization. Its right functor is the datum's value at (id,f).
Source: blueprint prop-exc-base-change-proper, Step 1
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperAmbientAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {c : Compactification f} (D : SfAmbientExceptionalRightAdjointDatum A f c) :
    proEtaleConstantDerivedDirectImage f A ⊣ D.rightAdjoint (Compactification.ofIsProper f) :=
  (D.adjunction (Compactification.ofIsProper f)).ofNatIsoLeft
    (sfProperSupportNormalization A f)

/-- Open restriction of direct image, using exactly the sectionwise fibre-product map
of the recorded sheaf comparison, now expressed with the exact inverse-image functors.
Source: blueprint prop-exc-base-change-proper, Steps 2–3; Stacks Tags 09AE and 09BN
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperOpenPullbackRestriction {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantModuleDirectImage p A ⋙ sfIntrinsicPullback A i ≅
      sfIntrinsicPullback A k ⋙ proEtaleConstantModuleDirectImage r A :=
  isoWhiskerRight (sfProperOpenDirectImageCoordinates A p) _ ≪≫
    (sfIntrinsicTransportComp A _ _).symm ≪≫
    sfIntrinsicTransportIso A
      (isoWhiskerLeft _
          (ProEtale.upperStarIsoOpenImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i) ≪≫
        sfProperOpenFixedRestrictionIso A r k i p sq ≪≫
        isoWhiskerRight
          (ProEtale.upperStarIsoOpenImmersionRestriction
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).symm _) ≪≫
    sfIntrinsicTransportComp A _ _ ≪≫
    isoWhiskerLeft _ (sfProperOpenDirectImageCoordinates A r).symm

/-- Derived open restriction. Direct image preserves K-injectives as right adjoint to
exact inverse image; open pullback preserves them as right adjoint to exact extension.
Thus this is induced by the specified sectionwise map on K-injective representatives.
No finite-CD or ambient-adjoint hypothesis is needed for this restriction isomorphism.
Source: blueprint prop-exc-base-change-proper, Step 3
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperOpenDerivedRestriction {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantDerivedDirectImage p A ⋙ sfIntrinsicDerivedPullback A i ≅
      sfIntrinsicDerivedPullback A k ⋙ proEtaleConstantDerivedDirectImage r A :=
  letI := (sfIntrinsicConstantModuleAdjunction p A).preservesKInjectiveComplexes
  letI := (sfIntrinsicOpenAdjunction A k).preservesKInjectiveComplexes
  isoWhiskerLeft (proEtaleConstantDerivedDirectImage p A)
      (sfIntrinsicPullback A i).rightDerivedFunctorIsoMapDerivedCategory.symm ≪≫
    (Functor.rightDerivedFunctorCompIso _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (sfProperOpenPullbackRestriction A r k i p sq) ≪≫
    Functor.rightDerivedFunctorCompIso _ _ ≪≫
    isoWhiskerRight (sfIntrinsicPullback A k).rightDerivedFunctorIsoMapDerivedCategory _

/-- The canonical derived proper/open arrow Γ. First use the open unit, then inverse
sectionwise restriction, and finally transpose under i_! ⊣ i^*. On K-injective
representatives this is the sheaf arrow sfProperOpenSheafComparison, followed by the
acyclic-complex derived comparison; the finite-CD input proves its invertibility.
Source: blueprint prop-exc-base-change-proper, Steps 2–3
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperOpenDerivedComparison {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    proEtaleConstantDerivedDirectImage r A ⋙ sfIntrinsicDerivedOpen A i ⟶
      sfIntrinsicDerivedOpen A k ⋙ proEtaleConstantDerivedDirectImage p A :=
  whiskerRight
      (whiskerRight (exceptionalOpenAdjunction k A).unit
          (proEtaleConstantDerivedDirectImage r A) ≫
        whiskerLeft (sfIntrinsicDerivedOpen A k)
          (sfProperOpenDerivedRestriction A r k i p sq).inv)
      (sfIntrinsicDerivedOpen A i) ≫
    whiskerLeft (sfIntrinsicDerivedOpen A k ⋙ proEtaleConstantDerivedDirectImage p A)
      (exceptionalOpenAdjunction i A).counit

/-- The comparison β is exactly the two transposes in the node, using Γ followed by
Rf_* of the open counit and then the normalized proper counit. The supplied adjunction
for r only determines its right adjoint; it supplies no freely chosen comparison map.
Source: blueprint prop-exc-base-change-proper, Steps 4–6
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperExceptionalOpenComparison {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsProper p] [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p)
    {c : Compactification p} (D : SfAmbientExceptionalRightAdjointDatum A p c)
    (H : proEtaleDerivedCategory W A ⥤ proEtaleDerivedCategory U A)
    (adj : proEtaleConstantDerivedDirectImage r A ⊣ H) (K : proEtaleDerivedCategory T A) :
    (sfIntrinsicDerivedPullback A k).obj
        ((D.rightAdjoint (Compactification.ofIsProper p)).obj K) ⟶
      H.obj ((sfIntrinsicDerivedPullback A i).obj K) :=
  adj.homEquiv _ _ ((exceptionalOpenAdjunction i A).homEquiv _ _
    ((sfProperOpenDerivedComparison A r k i p sq).app _ ≫
      (proEtaleConstantDerivedDirectImage p A).map
        ((exceptionalOpenAdjunction k A).counit.app _) ≫
      (sfProperAmbientAdjunction A p D).counit.app K))

/-- Under the optional ambient datum the proper/open map is invertible on the ordinary
unbounded derived categories, the restricted direct image has a right adjoint, and the
specified double-transpose comparison is invertible on every object.
Source: blueprint prop-exc-base-change-proper, reviewed statement and Steps 1–6
(blueprint: prop-exc-base-change-proper).
Proof: normalize the datum at (id,f) using its refinement comparisons and counit equations.
Exact extension by zero and FullCD of the distinguished proper part give a uniform bound
for Rf_* on all module sheaves. Proper/open sheaf comparison gives γ. Resolve M by a
K-injective complex J with injective terms. Its extension has f_*-acyclic terms; the uniform
bound identifies Rf_*g'_!M with f_*g'_!J and gives the displayed Γ. Restricting this
resolution identifies the open transpose of Γ with inverse derived restriction, precisely
the map used above. Successive open, proper and open adjunctions give natural bijections
Hom(M,g'^*Rf×K) ≃ Hom(Rf'_*M,g^*K). Put H=g'^*Rf×Rg_*; the open localization counit
identifies g^*Rg_* with identity and supplies Rf'_* ⊣ H. Yoneda then gives β as an
isomorphism. Evaluating the Hom bijection at identity gives exactly the two displayed
transposes, including the open and proper counits. This also proves naturality and covers
every unbounded K and every open immersion, including non-quasi-compact opens.
The inputs are def-weil-ambient-exceptional-adjoint and
lem-exc-proetale-proper-open-sheaf-comparison, followed by
prop-pur-kinjective-resolutions-exist, lem-exc-proetale-cartesian-open-injective-acyclic,
lem-kun-finite-cd-acyclic-complex, prop-exc-open-adjoint,
lem-weil-proetale-weakly-etale-localization and lem-galois-yoneda-fully-faithful. -/
theorem sfProperExceptionalOpenBaseChange
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    (_hS : ∀ x : S, IsUnit (l : S.presheaf.stalk x))
    [LocallyOfFiniteType (X ↘ S)] [QuasiCompact (X ↘ S)]
    [LocallyOfFiniteType (Y ↘ S)] [QuasiCompact (Y ↘ S)]
    (f : X ⟶ Y) [f.IsOver S] [IsProper f] (c : Compactification f)
    (D : SfAmbientExceptionalRightAdjointDatum
      (Padic.coefficientExtensionRing l E (n + 1)) f c)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g] :
    IsIso (sfProperOpenDerivedComparison (Padic.coefficientExtensionRing l E (n + 1))
      (pullback.snd f g) (pullback.fst f g) g f (IsPullback.of_hasPullback f g).flip) ∧
    ∃ H : proEtaleDerivedCategory Y' (Padic.coefficientExtensionRing l E (n + 1)) ⥤
        proEtaleDerivedCategory (pullback f g) (Padic.coefficientExtensionRing l E (n + 1)),
      ∃ adj : proEtaleConstantDerivedDirectImage (pullback.snd f g)
          (Padic.coefficientExtensionRing l E (n + 1)) ⊣ H,
        ∀ K : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)),
          IsIso (sfProperExceptionalOpenComparison (Padic.coefficientExtensionRing l E (n + 1))
            (pullback.snd f g) (pullback.fst f g) g f (IsPullback.of_hasPullback f g).flip
            D H adj K) := by
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale
open Scheme

/-- Forget the recorded bounded-below etale-origin witness, then use the inverse of the
canonical scalar realization to express that same complex as fixed-scalar module sheaves.
The inverse is the inverse of the published equivalence, not a chosen origin or map.
Source: blueprint prop-exc-base-change-proper, independent clause and Step 8;
coefficient realization of def-sf-etale-origin-subcategory
(blueprint: prop-exc-base-change-proper). -/
noncomputable def sfProperEtaleOriginFixedForgetful (T : Scheme.{u})
    (A : Type u) [CommRing A] [Finite A] :
    @EtaleOriginDerivedCategory T (ULift.{u + 1, u} A) _ _ ⊥
      (discreteTopology_bot _) ⥤
      DerivedCategory (Sheaf (ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :=
  let e := (@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
    (discreteTopology_bot _)).asEquivalence
  letI : e.functor.Additive :=
    inferInstanceAs (@finiteCoefficientRealization T (ULift.{u + 1, u} A) _ _ ⊥
      (discreteTopology_bot _)).Additive
  (@etaleOriginForgetful T (ULift.{u + 1, u} A) _ _ ⊥ (discreteTopology_bot _)) ⋙
    e.mapDerivedCategory.inverse

/-- Independently of ambient adjoint data, the canonical relative exceptional comparison
is invertible on every bounded-below complex of etale origin. The input retains its
entire witness, and the conclusion uses the already recorded canonical comparison map.
Source: blueprint prop-exc-base-change-proper, independent clause and Steps 7–8
(blueprint: prop-exc-base-change-proper).
Proof: finite-type schemes over k are Noetherian; their open subschemes are finite type
and have finite dimension (empty schemes use bound zero). Apply the relative adjunction
theorem to the proper identity-open compactifications of f and f'. Exact open extension
commutes with comparison and preserves bounded-below origins. Transport the etale
proper/open interchange by the five canonical comparison arrows of Step 7: the two proper
direct-image comparisons, the two open-extension comparisons, and comparison pullback of
the etale interchange. Full faithfulness of comparison on D+ makes this independent of
the retained witness. The direct-image counit-mate and pullback-pasting identities show
its open transpose is inverse sectionwise restriction, so it is the canonical map Γ.
Write K=ν* K₀. The formula for Rf! and the comparison unit identify the two endpoints
with ν* of the etale adjoint values restricted to the open. These values are bounded
below: the relative theorem bounds their comparison images, and exact fully faithful
comparison reflects vanishing of their cohomology. Hence both endpoints belong to the
same full etale-origin category. For each test object M in that category, successive
open adjunction, relative proper adjunction, precomposition with Γ, open adjunction and
relative proper adjunction give a natural bijection between Hom(M,B) and Hom(M,C).
Yoneda in this full category gives an isomorphism B→C. Evaluating at identity identifies
it with sfFiniteExceptionalOpenComparison, whose definition is the same canonical
comparison-site paste of the etale mate. Degree-zero coefficient sheaves are included;
no constructibility, extra boundedness, or unrestricted ambient datum is assumed.
The relative input is thm-sf-ambient-adjoint-class, with its independent discharge
cor-sf-ambient-adjoint-discharge. The five-arrow comparison uses
lem-cbc-proetale-extension-zero-comparison, lem-sf-class-compact-support-comparison,
lem-amb-unbounded-proper-open-interchange and thm-weil-pbc-site-comparison.
Its normalization uses lem-weil-pbc-comparison-direct-image-canonical-mate,
lem-weil-pbc-comparison-pullback and lem-weil-pbc-mate-pasting; exactness and the section
calculation are lem-sf-comparison-pullback-exact and lem-cbc-comparison-pullback-sections. -/
theorem sfProperFiniteExceptionalOpenBaseChange
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))] [IsProper f]
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K : @EtaleOriginDerivedCategory Y
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) _ _ ⊥
      (discreteTopology_bot _)) :
    IsIso (sfFiniteExceptionalOpenComparison (Padic.coefficientExtensionRing l E (n + 1))
      (IsPullback.of_hasPullback f g) (Compactification.ofIsProper f)
      ((sfProperEtaleOriginFixedForgetful Y
        (Padic.coefficientExtensionRing l E (n + 1))).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale
