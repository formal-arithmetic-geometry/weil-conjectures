module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.EtaleOriginDerivedCategory
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportCandidate
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.EtaleChartAdjointComparison
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.Compactification.NagataCompactification
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.Paper.CompactificationCoherence
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange

/-! # Witnessed adjunctions and exceptional comparison on an affine chart

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-et-proet,
`thm-pur-general-admissibility.proof.md`, Steps 1 and 3
(blueprint: lem-pur-affine-chart-exceptional-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.PurityChart

/-- The recorded witnessed category with its prescribed discrete lifted coefficients.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
abbrev C (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (S : Scheme.{u}) :=
  EtaleOriginDerivedCategory S A

/-- The canonical fixed-scalar forgetful realization, retaining all ambient arrows.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
abbrev forget (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (S : Scheme.{u}) :=
  originWitnessFixedAmbient A S

/-- The specified witness isomorphism in fixed-scalar coordinates, obtained from alpha
and the unit of the published coefficient equivalence. No origin is chosen.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def witnessIso (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] (S : Scheme.{u}) (K : C A S) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj
        K.2.L.obj ≅ (forget A S).obj K :=
  let R := finiteCoefficientRealization S A
  let E := R.asEquivalence
  letI : E.functor.Additive := finiteCoefficientRealization_additive S A
  letI : E.inverse.Additive := @Equivalence.inverse_additive _ _ _ _ _ _ E
    (finiteCoefficientRealization_additive S A)
  let ν := comparisonUpperStar (ModuleCat.{u + 1} A) S
  E.mapDerivedCategory.unitIso.app (ν.mapDerivedCategory.obj K.2.L.obj) ≪≫
    E.inverse.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν R).symm.app K.2.L.obj ≪≫
        DerivedCategory.Plus.ι.mapIso K.2.alpha)

/-- The compact-support functor at the chosen compactification in fixed-ring coordinates.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
abbrev support (A : Type (u + 1)) [CommRing A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The ordinary etale right adjoint at the specified compactification.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def etaleRight (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).rightAdjoint

/-- Its actual adjunction, used to normalize the witnessed Hom bijections.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def etaleAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) :
    Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) c ⊣ etaleRight A c :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  Adjunction.ofIsLeftAdjoint _

/-- The defined transported exceptional functor, with the adjoint-existence theorem
supplied rather than imposed as a hypothesis.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def right (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) :=
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  sfFiniteExceptionalAt A c

/-- The comparison-unit witness arrow for the exceptional image. Its invertibility
on the stated domain is a conclusion below, not an extra assumption.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def rightOrigin (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) (N : C A R) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.obj
        ((etaleRight A c).obj N.2.L.obj) ⟶ (right A c).obj ((forget A R).obj N) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
    ((etaleRight A c).map
      ((derivedComparisonAdjunction (ModuleCat.{u + 1} A) R).unit.app
        N.2.L.obj ≫
        (comparisonLowerStar (ModuleCat.{u + 1} A) R).rightDerivedFunctor.map
          (witnessIso A R N).hom))

/-- A pair of lifts with their actual etale witnesses and the normalized adjunction.
All fields are data or properties of those data; no lift is selected by a definition.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
structure LiftedAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} (c : Compactification v) where
  lower : C A S ⥤ C A R
  upper : C A R ⥤ C A S
  lowerUnderlying : lower ⋙ forget A R ≅ forget A S ⋙ support A c
  upperUnderlying : upper ⋙ forget A S ≅ forget A R ⋙ right A c
  lowerWitness (M : C A S) :
    (lower.obj M).2.L.obj =
      (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj M.2.L.obj
  upperWitness (N : C A R) : (upper.obj N).2.L.obj = (etaleRight A c).obj N.2.L.obj
  origin_iso (N : C A R) : IsIso (rightOrigin A c N)
  adj : lower ⊣ upper
  normalized (M : C A S) (N : C A R)
      (t : (Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj M.2.L.obj ⟶ N.2.L.obj)
      (m : lower.obj M ⟶ N)
      (hm : (forget A R).map m = lowerUnderlying.hom.app M ≫
        (support A c).map (witnessIso A S M).inv ≫
        (compactSupportSiteComparison A c).hom.app M.2.L ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) R).mapDerivedCategory.map t ≫
        (witnessIso A R N).hom) :
    (forget A S).map (adj.homEquiv M N m) ≫ upperUnderlying.hom.app N =
      (witnessIso A S M).inv ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map
          ((etaleAdjunction A c).homEquiv _ _ t) ≫ rightOrigin A c N

/-- Open restriction lifts with the ordinary etale restriction as its retained witness.
Source: blueprint, Steps 1 and 3
(blueprint: lem-pur-affine-chart-exceptional-identification). -/
structure OpenLift (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j] where
  restriction : C A T ⥤ C A W
  underlying : restriction ⋙ forget A W ≅
    forget A T ⋙ (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
  witness (K : C A T) : (restriction.obj K).2.L.obj =
    (Etale.upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj K.2.L.obj

/-- Finite purity coefficients are finite at every prescribed positive level.
Source: blueprint finite conventions
(blueprint: lem-pur-affine-chart-exceptional-identification). -/
instance finiteRing (P : WeilConjectures.PurityFiniteSetting.{u}) : Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

/-- Finiteness after the prescribed size lift of the finite coefficient ring.
Source: blueprint finite conventions
(blueprint: lem-pur-affine-chart-exceptional-identification). -/
instance finiteCoefficient (P : WeilConjectures.PurityFiniteSetting.{u}) :
    Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- The finite coefficient ring has its specified discrete topology.
Source: blueprint, finite coefficients
(blueprint: lem-pur-affine-chart-exceptional-identification). -/
instance coefficientTopology (P : WeilConjectures.PurityFiniteSetting.{u}) :
    TopologicalSpace P.Coefficient := ⊥

/-- Discreteness of the specified topology.
Source: blueprint, finite coefficients
(blueprint: lem-pur-affine-chart-exceptional-identification). -/
instance coefficientDiscrete (P : WeilConjectures.PurityFiniteSetting.{u}) :
    DiscreteTopology P.Coefficient := discreteTopology_bot _

/-- Compact support and transported exceptional inverse image lift to the witnessed
categories, retaining precisely the two ordinary etale bounded-below witnesses.
Source: blueprint, Step 1
(blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: finite-type schemes over k are Noetherian and quasi-compact. Etale compact support
preserves D+, and its right adjoint preserves D+ over a quasi-compact target. The canonical
compact-support site comparison supplies the left witness. The comparison unit at the
specified etale witness, followed by Rnu_* of alpha, supplies the right witness. Exact
comparison preserves the lower bounds. Lift arrows using the ambient functors; no witness
map is required. Full faithfulness of comparison and the ordinary etale adjunction give
the displayed normalized natural Hom bijections for all underlying arrows. -/
theorem exists_liftedAdjunction (P : WeilConjectures.PurityFiniteSetting.{u})
    {S R : Scheme.{u}} [S.Over (Spec (.of P.field.k))] [R.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (R ↘ Spec (.of P.field.k))]
    [QuasiCompact (R ↘ Spec (.of P.field.k))]
    (v : S ⟶ R) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (c : Compactification v) :
    Nonempty (LiftedAdjunction P.Coefficient c) := by
  sorry

/-- Exact open restriction preserves witnessed etale origin.
Source: blueprint, Steps 1 and 3
(blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: constant-coefficient inverse image is exact on both sites, hence preserves a
cohomological lower bound. Apply the canonical pullback-comparison square to alpha and
retain the ordinary etale restriction of the specified witness. Use ambient inverse
image on arrows. The identity and composition equations are inherited from it. -/
theorem exists_openLift (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {W T : Scheme.{u}} (j : W ⟶ T) [IsOpenImmersion j] : Nonempty (OpenLift A j) := by
  sorry


/-- Canonical compact-support comparison on the retained-witness domain, in the ambient
fixed-scalar coordinates. This is the published etale-origin comparison, pulled back
along the recorded forgetful realization.
Source: blueprint, Step 1 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def supportComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} [QuasiCompact v] (c d : Compactification v) :=
  Functor.isoWhiskerLeft (originWitnessFixed A S)
    (rightDerivedLowerShriekOfCompactificationEtaleOriginIso A c d)

/-- Independence of the underlying functors and Hom bijections under the canonical
compact-support comparison and the counit-compatible uniqueness comparison of right
adjoints. This is asserted for any two lifts satisfying their normalized Hom chain.
Source: blueprint, Step 1
(blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: compare the left functors by the canonical compact-support comparison, whose
identity and cocycle equations hold on etale origin. Full faithfulness of the forgetful
functor lifts this comparison uniquely. Transport the first adjunction along it and use
uniqueness of right adjoints. Its counit equation is precisely compatibility of the Hom
bijections. The right comparisons satisfy identity and composition because both routes
are counit-compatible and uniqueness forces their equality. -/
theorem compactification_independence (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {S R : Scheme.{u}} {v : S ⟶ R} [QuasiCompact v] (c d : Compactification v)
    (D : LiftedAdjunction A c) (E : LiftedAdjunction A d) :
    ∃ e : D.lower ≅ E.lower,
      (∀ M, (forget A R).map (e.hom.app M) = D.lowerUnderlying.hom.app M ≫
        (supportComparison A c d).hom.app M ≫ E.lowerUnderlying.inv.app M) ∧
      ∃ r : D.upper ≅ E.upper,
        r = (D.adj.ofNatIsoLeft e).rightAdjointUniq E.adj ∧
        ∀ (M : C A S) (N : C A R) (m : E.lower.obj M ⟶ N),
          D.adj.homEquiv M N (e.hom.app M ≫ m) ≫ r.hom.app N = E.adj.homEquiv M N m := by
  sorry

/-- The natural chart isomorphism in the witnessed categories. The input ranges over
all bounded-below etale-origin objects, not just the bounded constructible ones.
Source: blueprint, Step 1
(blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: finite type over k implies Noetherianity and quasi-compactness of every chart.
All etale right adjoints involved preserve D+; exact open inverse image also does so.
Apply lem-sf-etale-chart-adjoint-comparison with the identity open on V, to the specified
etale witness N_e. Its natural Hom chain compares Q=(u')^*f_e^times N_e with
B=i_e^times pi_e^times N_e. Evaluate at Q and B: the images of their identities give
arrows a and b. Naturality and the inverse-bijection identities give ab=1 and ba=1.
Naturality in N_e makes a a natural isomorphism. Apply nu_U^*, use the witness-unit
identifications for f, pi and i, and use the inverse-image comparison for u'. Full
faithfulness of comparison identifies every underlying arrow with its unique etale
arrow, hence gives naturality for all morphisms in the witnessed category. -/
theorem affine_chart (P : WeilConjectures.PurityFiniteSetting.{u})
    {X V : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))] [IsAffine V]
    (f : X ⟶ V) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {U : Scheme.{u}} [IsAffine U] (j : U ⟶ X) [IsOpenImmersion j]
    (d : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [IsClosedImmersion i]
    (_w : j ≫ f = i ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    (cf : Compactification f) (ci : Compactification i)
    (cp : Compactification (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    (F : LiftedAdjunction P.Coefficient cf) (I : LiftedAdjunction P.Coefficient ci)
    (B : LiftedAdjunction P.Coefficient cp) (J : OpenLift P.Coefficient j) :
    Nonempty (F.upper ⋙ J.restriction ≅ B.upper ⋙ I.upper) := by
  sorry

/-- The canonical ordinary etale exceptional mate at the actual two compactifications.
Source: blueprint, Step 3 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def etaleOpenMate (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {v : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h v f g) [QuasiCompact v] (c : Compactification f) :=
  letI := Etale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_of_finite A sq c
  mateEquiv (etaleAdjunction A c) (etaleAdjunction A (c.ofIsPullback sq))
    (inv (Etale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} A) sq c))

/-- The canonical base-open arrow: comparison pullback, the etale exceptional mate,
and comparison direct-image restriction. The etale adjoints use the specified c itself.
Source: blueprint, Step 3 (blueprint: lem-pur-affine-chart-exceptional-identification). -/
def baseOpenMap (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {h : X' ⟶ X} {v : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback h v f g) [IsOpenImmersion g] [QuasiCompact v]
    (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :
    (sfFixedDerivedPullback A h).obj
        ((@right (ULift.{u + 1} A) _ _ ⊥ (discreteTopology_bot _) X Y f c).obj K) ⟶
      (@right (ULift.{u + 1} A) _ _ ⊥ (discreteTopology_bot _) X' Y' v
        (c.ofIsPullback sq)).obj ((sfFixedDerivedPullback A g).obj K) :=
  letI : TopologicalSpace (ULift.{u + 1} A) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} A) := discreteTopology_bot _
  (sfDerivedComparisonPullbackIso A h).hom.app
      ((etaleRight (ULift.{u + 1} A) c).obj
        ((comparisonLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).rightDerivedFunctor.obj K)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X').mapDerivedCategory.map
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ h).inv.app _ ≫
        (etaleOpenMate (ULift.{u + 1} A) sq c).app
          ((comparisonLowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).rightDerivedFunctor.obj K) ≫
        (etaleRight (ULift.{u + 1} A) (c.ofIsPullback sq)).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory _ g).hom.app _)) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X').mapDerivedCategory.map
      ((etaleRight (ULift.{u + 1} A) (c.ofIsPullback sq)).map
        ((sfDerivedComparisonOpenRestrictionIso A g).hom.app K))

/-- Every bounded constructible intrinsic complex has a realization in the witnessed
category. This supplies the inputs of the final comparison without assuming a witness.
Source: blueprint, Step 3 (blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: the intrinsic constructibility predicate is the bounded cohomological predicate
on the constant-ring presentation. The canonical coefficient equivalence transports it
to bounded constructibility in fixed coefficients. The constructible-origin comparison
supplies a bounded-below etale representative and its comparison isomorphism. Realize
that isomorphism in the recorded continuous-function presentation and retain both the
representative and alpha as an object of the induced witnessed category. The canonical
realization equivalence identifies its intrinsic image with the original K. -/
theorem constructible_origin (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory Y P.Ring)
    (_hK : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos Y K) :
    ∃ L : C P.Coefficient Y,
      Nonempty ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj
        ((forget P.Coefficient Y).obj L) ≅ K) := by
  sorry

/-- The canonical base-open comparison and its chart composite, lifted to witnessed
objects. The base-open arrow is the actual published comparison-site paste; an arbitrary
isomorphism of the two values would not meet its displayed normalization.
Source: blueprint, Step 3
(blueprint: lem-pur-affine-chart-exceptional-identification).

Proof: bounded constructible inputs admit bounded-below etale origins. Apply the
independent canonical open-base comparison to the underlying input. Its two values
retain the witnesses already supplied by the lifted functors and open restriction.
The forgetful functor is fully faithful, so the canonical comparison and its inverse
lift uniquely. Compose with the natural chart isomorphism of affine_chart. Exact
inverse image identifies restriction along u=hu' with successive restriction along
h and u'; the resulting arrow is the chart composite in the assertion. No preservation
of bounded constructibility by any exceptional functor enters this argument. -/
theorem base_open_chart (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {V : Scheme.{u}} [IsAffine V] (g : V ⟶ Y) [IsOpenImmersion g]
    {U : Scheme.{u}} [IsAffine U] (j : U ⟶ pullback f g) [IsOpenImmersion j]
    (d : ℕ) (i : U ⟶ AffineSpace (ULift.{u} (Fin d)) V) [IsClosedImmersion i]
    (_w : j ≫ pullback.snd f g = i ≫ (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    (c : Compactification f) (ci : Compactification i)
    (cp : Compactification (AffineSpace (ULift.{u} (Fin d)) V ↘ V))
    (F : LiftedAdjunction P.Coefficient c)
    (FV : LiftedAdjunction P.Coefficient (c.ofIsPullback (IsPullback.of_hasPullback f g)))
    (I : LiftedAdjunction P.Coefficient ci) (B : LiftedAdjunction P.Coefficient cp)
    (G : OpenLift P.Coefficient g) (H : OpenLift P.Coefficient (pullback.fst f g))
    (J : OpenLift P.Coefficient j)
    (Ju : OpenLift P.Coefficient (j ≫ pullback.fst f g))
    (e : FV.upper ⋙ J.restriction ≅ B.upper ⋙ I.upper)
    (L : C P.Coefficient Y)
    (_hL : Scheme.intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos Y
        ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).functor.obj
          ((forget P.Coefficient Y).obj L))) :
    ∃ b : H.restriction.obj (F.upper.obj L) ≅ FV.upper.obj (G.restriction.obj L),
      (forget P.Coefficient (pullback f g)).map b.hom =
        H.underlying.hom.app (F.upper.obj L) ≫
        (sfFixedDerivedPullback P.Ring (pullback.fst f g)).map
          (F.upperUnderlying.hom.app L) ≫
        baseOpenMap P.Ring (IsPullback.of_hasPullback f g) c
          ((forget P.Coefficient Y).obj L) ≫
        (right P.Coefficient
          (c.ofIsPullback (IsPullback.of_hasPullback f g))).map
            (G.underlying.inv.app L) ≫
        FV.upperUnderlying.inv.app (G.restriction.obj L) ∧
      ∃ t : Ju.restriction.obj (F.upper.obj L) ≅
          J.restriction.obj (H.restriction.obj (F.upper.obj L)),
        (forget P.Coefficient U).map t.hom =
          Ju.underlying.hom.app (F.upper.obj L) ≫
          (Functor.mapDerivedCategoryNatIso
            (upperStarComp (ModuleCat.{u + 1} P.Coefficient) j (pullback.fst f g))).hom.app
              ((forget P.Coefficient X).obj (F.upper.obj L)) ≫
          (Functor.mapDerivedCategoryCompIso
            (upperStar (ModuleCat.{u + 1} P.Coefficient) (pullback.fst f g))
            (upperStar (ModuleCat.{u + 1} P.Coefficient) j)).hom.app
              ((forget P.Coefficient X).obj (F.upper.obj L)) ≫
          (sfFixedDerivedPullback P.Ring j).map
            (H.underlying.inv.app (F.upper.obj L)) ≫
          J.underlying.inv.app (H.restriction.obj (F.upper.obj L)) ∧
        ∃ z : Ju.restriction.obj (F.upper.obj L) ≅
            I.upper.obj (B.upper.obj (G.restriction.obj L)),
          z = t ≪≫ J.restriction.mapIso b ≪≫ e.app (G.restriction.obj L) := by
  sorry

end AlgebraicGeometry.ProEtale.PurityChart
