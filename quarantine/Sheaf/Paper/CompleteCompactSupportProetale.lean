/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.AdicCoefficientDatum
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.Paper.ProjectionCompactification
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedOpenExchangeTransport
public import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.CompleteProetale
public import Sheaf.Paper.CompletedExchangeCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.OpenImmersionTensorPiece
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import Sheaf.Paper.KoszulReconstruction
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.Algebra.Homology.RoosComplex
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.CategoryTheory.DiagramSiteRealization
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedPullbackReduction
import Sheaf.Paper.StrictTowerExchangeMateNormalization
import Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.AlgebraicGeometry.ComparisonDirectImage
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.RefinementExchangeCoherence

/-!
# Complete pro-etale compact-support base change

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-sf-cbc,
node thm-cbc-complete-proetale (blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The projection of an open pullback, as an arrow in the original pro-etale site.
Source: Stacks 09AE, localization (blueprint: thm-cbc-complete-proetale). -/
def cbcOpenProjection {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (V : T.ProEt) :
    (cbcOpenSiteFunctor j inferInstance).obj ((proEtaleBaseChange j).obj V) ⟶ V :=
  MorphismProperty.Over.homMk (pullback.fst V.hom j) pullback.condition

/-- Restriction of sections is the unit from a module to direct image of open restriction.
Its section formula fixes the comparison, including its completed scalar action.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: apply each presheaf restriction to the displayed pullback projection. Functoriality
makes these maps natural. The finite coefficient projections show scalar compatibility;
limit uniqueness gives the same compatibility for completed coefficients. The formula on
all sections uniquely determines a sheaf map and then the natural transformation. -/
theorem cbcRestrictionUnit_existsUnique {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    ∃! η : 𝟭 (proEtaleRingModules T (d.completedRing T)) ⟶
        cbcOpenRestriction d j inferInstance ⋙
          proEtaleRingModuleDirectImage j (d.completedRing T) (d.completedRing U)
            (d.integralRingIso j),
      ∀ (M : proEtaleRingModules T (d.completedRing T)) (V : T.ProEt)
        (x : M.val.obj (op V)),
        (η.app M).val.app (op V) x = M.val.map (cbcOpenProjection j V).op x := by
  sorry

/-- The section-normalized restriction unit.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
def cbcRestrictionUnit {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (cbcRestrictionUnit_existsUnique d j).choose

set_option maxHeartbeats 800000 in
-- Transposing the section unit compares the concrete and small-model module categories.
/-- Ordinary inverse image identifies with open restriction by transposing its section unit.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcPullToRestriction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
        (d.integralRingIso j) ⟶ cbcOpenRestriction d j inferInstance :=
  (((proEtaleRingModuleAdjunction j (d.completedRing T) (d.completedRing U)
    (d.integralRingIso j)).whiskerRight
      (proEtaleRingModules T (d.completedRing T))).homEquiv
        (𝟭 (proEtaleRingModules T (d.completedRing T)))
          (cbcOpenRestriction d j inferInstance)).symm (cbcRestrictionUnit d j)

/-- The specified restriction comparison is invertible.
Source: Stacks 03DI and 09AE (blueprint: thm-cbc-complete-proetale).
Proof: localization identifies pro-etale objects over U with objects over the open object
of T. Inverse image on this slice is evaluation on those same objects. The tensor-unit
adjunction sends its comparison to precisely the section restriction unit above. Thus
that transpose is the localization equivalence's restriction identification, hence invertible. -/
theorem cbcPullToRestriction_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcPullToRestriction d j) := by
  sorry

/-- The exact, section-normalized open adjunction on completed coefficients.
Source: Stacks 03DI and 03DJ (blueprint: thm-cbc-complete-proetale). -/
def cbcDerivedOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⊣ d.pull j :=
  Adjunction.ofNatIsoRight
    ((Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
      (@asIso _ _ _ _ (cbcPullToRestriction d j)
        (cbcPullToRestriction_isIso d j)).symm).mapDerivedCategoryRightDerivedAdjunction)
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory

/-- Abbreviation for the recorded exact open extension, without a new construction.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  cbcDerivedOpenShriek d j inferInstance

/-- Open composition is the unique comparison of the composition adjunctions.
Source: Stacks 03DI, 0F7D (blueprint: thm-cbc-complete-proetale). -/
def cbcJComp {U V T : Scheme.{t}} (j : U ⟶ V) (k : V ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion k] : cbcJ d j ⋙ cbcJ d k ≅ cbcJ d (j ≫ k) :=
  Adjunction.leftAdjointCompIso (cbcDerivedOpenAdjunction d j)
    (cbcDerivedOpenAdjunction d k) (cbcDerivedOpenAdjunction d (j ≫ k))
    (d.pullComp j k).symm

/-- Equality transport for the recorded open extension.
Source: blueprint canonical comparisons (blueprint: thm-cbc-complete-proetale). -/
def cbcJCongr {U T : Scheme.{t}} {j k : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) : cbcJ d j ≅ cbcJ d k :=
  by
    subst k
    exact Iso.refl _

/-- Proper inverse image/direct image with their published tensor-normalized adjunction.
Source: Stacks 07A6 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcPullPushAdjunction {U T : Scheme.{t}} (f : U ⟶ T) : d.pull f ⊣ d.push f :=
  proEtaleRingDerivedAdjunction f (d.completedRing T) (d.completedRing U)
    (d.integralRingIso f)

/-- Pullback composition around a commutative square, with its canonical compositors.
Source: Stacks 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcSquarePull {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    d.pull i ⋙ d.pull r ≅ d.pull p ⋙ d.pull k :=
  (d.pullComp r i).symm ≪≫ eqToIso (congrArg (fun f ↦ d.pull f) h.symm) ≪≫
    d.pullComp k p

/-- The inverse open comparison is the transpose of the open-extension unit.
Source: Stacks 09AE and 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcBetaInv {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    d.pull a ⋙ cbcJ d j' ⟶ cbcJ d j ⋙ d.pull g :=
  (((cbcDerivedOpenAdjunction d j').whiskerRight _).homEquiv _ _).symm
    ((Functor.leftUnitor (d.pull a)).inv ≫
      Functor.whiskerRight (cbcDerivedOpenAdjunction d j).unit (d.pull a) ≫
      (Functor.associator (cbcJ d j) (d.pull j) (d.pull a)).hom ≫
      Functor.whiskerLeft (cbcJ d j) (cbcSquarePull d a j' j g h).inv ≫
      (Functor.associator (cbcJ d j) (d.pull g) (d.pull j')).inv)

/-- The unit-normalized open comparison is invertible for a Cartesian open square.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale).
Proof: localization identifies the right adjoints around this Cartesian square by
restriction on the same pulled-back objects. Their adjunction conjugate is invertible.
Its inverse has exactly the open-unit transpose defining cbcBetaInv, proving the claim. -/
theorem cbcBetaInv_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (_sq : IsPullback a j' j g) : IsIso (cbcBetaInv d a j' j g h) := by
  sorry

/-- Cartesian open comparison, in the forward direction fixed by the inverse unit-mate.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcBeta {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : cbcJ d j ⋙ d.pull g ≅ d.pull a ⋙ cbcJ d j' :=
  (@asIso _ _ _ _ (cbcBetaInv d a j' j g h)
    (cbcBetaInv_isIso d a j' j g h sq)).symm

/-- The open unit is invertible, including on the empty open subscheme.
Source: Stacks 03DI (blueprint: thm-cbc-complete-proetale).
Proof: restriction of the extension presheaf has just the summand indexed by the
structure map of an object over the open. Sheafification and localization preserve
this unit identification, so every component of the derived unit is invertible. -/
theorem cbcOpenUnit_isIso {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    IsIso (cbcDerivedOpenAdjunction d j).unit := by
  sorry

/-- Open extension to direct image, fixed by the ordinary units of both adjunctions.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcOpenToPush {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcJ d j ⟶ d.push j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (cbcJ d j) (cbcPullPushAdjunction d j).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (@inv _ _ _ _ (cbcDerivedOpenAdjunction d j).unit
      (cbcOpenUnit_isIso d j)) (d.push j) ≫ (Functor.leftUnitor _).hom

/-- The specified open-to-direct-image map is invertible on a clopen immersion.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale).
Proof: split every test object into its two clopen parts. Both extension and direct
image give the sections on the image part and zero on the complement. The units in
the definition identify the comparison with identity on that first factor. The same
formula holds on complexes and descends through the exact localizations. -/
theorem cbcOpenToPush_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : IsIso (cbcOpenToPush d j) := by
  sorry

/-- Canonical clopen projection; identity on the image and zero on the complement.
Source: Stacks 09AE (blueprint: thm-cbc-complete-proetale). -/
def cbcClopenProjection {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : 𝟭 (d.derived T) ⟶ d.pull j ⋙ cbcJ d j :=
  (cbcPullPushAdjunction d j).unit ≫ Functor.whiskerLeft (d.pull j)
    (@inv _ _ _ _ (cbcOpenToPush d j) (cbcOpenToPush_isIso d j))

/-- The non-Cartesian proper/open comparison before taking its proper-adjunction mate.
It projects onto the clopen image of (k,r) in the fibre product, with no extra
Cartesian-square hypothesis on a refinement.
Source: Stacks 0F7B, 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcProperOpenAlpha {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : cbcJ d i ⋙ d.pull p ⟶ d.pull r ⋙ cbcJ d k :=
  (cbcBeta d (pullback.snd p i) (pullback.fst p i) i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (d.pull (pullback.snd p i))
    (cbcClopenProjection d (ProEtale.StrictTower.squareLift k r p i h)))
      (cbcJ d (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator (d.pull (pullback.snd p i))
    (d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))).inv
        (cbcJ d (pullback.fst p i)) ≫
  (Functor.associator (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))
        (cbcJ d (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      ((cbcJComp d (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
        (cbcJCongr d (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight ((d.pullComp (ProEtale.StrictTower.squareLift k r p i h)
    (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h))).hom) (cbcJ d k)

/-- The canonical proper/open map is the proper-adjunction mate of the clopen projection.
Source: Stacks 0F7B, 07A7 (blueprint: thm-cbc-complete-proetale). -/
def cbcProperOpenGamma {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : d.push r ⋙ cbcJ d i ⟶ cbcJ d k ⋙ d.push p :=
  mateEquiv (cbcPullPushAdjunction d r) (cbcPullPushAdjunction d p)
    (cbcProperOpenAlpha d k r p i h)

/-- The base-changed finite-type morphism is quasi-compact. This is a consequence
of the supplied square, not an additional typeclass hypothesis in the coherence laws.
Source: Stacks 01K5 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcBaseChangeQuasiCompact {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sq : OpenImmersionSquare g' c'.i c.i gbar) : QuasiCompact f' :=
  c'.quasiCompact (MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
      (c.quasiCompact_openImmersion inferInstance))

/-- The recorded exchange, with its quasi-compactness instance named for explicit
transport to a base-changed compactification. Its map is definitionally unchanged.
Source: blueprint ordered two-factor composite (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcExchange {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [qf : QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  completedCompactSupportExchange d c c' gbar sp sj r a ha K

/-- The exact chosen-compactification functor Rp_* j_! on completed-ring modules.
Source: blueprint displayed definition of Rf_!^c (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcSupport {X Y : Scheme.{t}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcJ d c.i ⋙ d.push c.g

/-- The canonical refinement map, directed from the coarser to the finer compactification.
It is proper pushforward of gamma, with the proper identity and composition comparisons.
Source: blueprint proof step 8, C_u (blueprint: thm-cbc-complete-proetale). -/
def cbcRefinementMap {X Y : Scheme.{t}} {f : X ⟶ Y} [qf : QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂) (K : d.derived X) :
    (cbcSupport d c₂).obj K ⟶ (cbcSupport d c₁).obj K :=
  letI : QuasiCompact c₁.i := c₁.quasiCompact_openImmersion qf
  letI : QuasiCompact c₂.i := c₂.quasiCompact_openImmersion qf
  (d.push c₂.g).map
    ((cbcJ d c₂.i).map ((d.pushId X).inv.app K) ≫
      (cbcProperOpenGamma d c₁.i (𝟙 X) u.hom c₂.i
        (u.i_hom.trans (Category.id_comp _).symm)).app K) ≫
    (d.pushComp u.hom c₂.g).hom.app ((cbcJ d c₁.i).obj K) ≫
      (eqToIso (congrArg (fun f ↦ d.push f) u.hom_g)).hom.app ((cbcJ d c₁.i).obj K)

/-- The compatible-tower compact-support composition map. Its middle factor is the
specified proper/open gamma, so this is not an arbitrary isomorphism of the endpoints.
Source: blueprint proof step 8, D_j (blueprint: thm-cbc-complete-proetale). -/
def cbcCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    [IsOpenImmersion b] [QuasiCompact b] [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : QuasiCompact ch.i := ch.quasiCompact_openImmersion inferInstance
  (d.push ch.g).map ((cbcProperOpenGamma d b cf.g p ch.i hp).app
      ((cbcJ d cf.i).obj K)) ≫
    (d.pushComp p ch.g).hom.app ((cbcJ d b).obj ((cbcJ d cf.i).obj K)) ≫
    (d.push (p ≫ ch.g)).map
      ((cbcJComp d cf.i b).hom.app K ≫ (cbcJCongr d hb).hom.app K) ≫
    (eqToIso (congrArg (fun f ↦ d.push f) hq)).hom.app ((cbcJ d chf.i).obj K)

/-- Composition for a supplied Cartesian compatible tower. The open immersion and
quasi-compactness of b are derived from that square and the outer compactification.
Source: blueprint proof step 8, compatible towers (blueprint: thm-cbc-complete-proetale). -/
def cbcTowerCompositionMap {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [qh : QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h) (chf : Compactification (f ≫ h))
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z) [IsProper p]
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g) (sq : IsPullback b cf.g p ch.i) (K : d.derived X) :
    (cbcSupport d ch).obj ((cbcSupport d cf).obj K) ⟶ (cbcSupport d chf).obj K :=
  letI : IsOpenImmersion b := MorphismProperty.of_isPullback sq.flip ch.isOpenImmersion
  letI : QuasiCompact b := MorphismProperty.of_isPullback sq.flip
    (ch.quasiCompact_openImmersion qh)
  cbcCompositionMap d cf ch chf b p hb hp hq K

/-- The completed compact-support exchange is invertible on an intrinsically complete
object carrying compatible bounded-below etale origins. Its component is the ordered
proper exchange followed by the normalized completed open comparison from
`completedCompactSupportExchange`. No common lower bound on the origins is required.
The remaining clauses of this node are stated in the identity, horizontal,
compactifications, refinement, vertical, and composition_refinement theorems below.

Source: blueprint thm-cbc-complete-proetale, proof steps 1--8; Stacks 09AE, 09AF,
09BP, 099M, 099N, 09C9 and 07A7 (blueprint: thm-cbc-complete-proetale).
Proof:
1. Localize the ringed site at the open. Restriction is evaluation on the localized
objects, so commutes with limits and identifies the restricted completed coefficient
ring with A_X. The localized module adjunction supplies the actual exact j_! used here.
2. Resolve each positive quotient by a bounded finite-projective A-complex. The open
projection formula identifies reductions of j_!K with j_!K_n, naturally in the quotient
maps. Finite-coefficient site comparison extends each retained etale origin; exact etale
extension preserves its own lower bound. These origins remain transition-compatible.
3. The ringed open/closed sequence and immersion limit preservation imply that j_!
preserves small limits. Countable products are exact. On K-injective tower complexes,
the canonical comparison j_! lim I -> lim J is induced by the resolution j_!I -> J.
The signed Roos map lim C -> Cone(1-shift)[-1], x |-> (0,x), commutes with this map
and the diagonal product map. The latter is a quasi-isomorphism, hence the comparison
is invertible. The same formulas preserve homotopies, so resolution comparison makes
it natural and independent of choices. The quotient-unit family maps to the extended
quotient-unit family; Koszul reconstruction therefore proves j_!K complete.
4. Apply completed proper base change to p and j_!K, using steps 2 and 3. Proper
direct image commutes with the relevant derived limits, identifies its reduction tower,
and preserves completeness. This proves invertibility of the first exchange factor.
5. The second factor is the finite-reduction comparison, Rlim of the normalized open
unit-mate, and the inverse of the extension/Rlim comparison of step 3, in that order.
Every factor is invertible. Completed pullback preserves completeness, so the target
comparison applies as well. Their ordered composite is precisely the map displayed here.
6. Normalize the full strict-tower exchange as the proper mate followed by the open
unit-mate, then restrict to constant A coefficients. These are equalities of tower
morphisms before evaluation, and the completed comparison is their Rlim transport.
7. Naturality follows from the mates and comparisons. Identity and horizontal pasting
hold before evaluation by mate-pasting and the open unit characterization. Applying
Rlim cancels adjacent reconstruction comparisons and leaves the canonical completed
identity and composition identifications displayed in the following statements.
8. Use the normalized proper/open comparison for every commutative proper/open square,
including noncartesian refinement squares. Its finite-origin components are invertible;
the reduction cone criterion and completeness give invertibility after completion.
Mate-pasting gives the refinement cocycle, base-change/refinement interchange, vertical
composition, and compatibility with refining compatible towers. Cofiltered common
refinements of compactifications and compatible towers remove both choices. Proper
composition and the same Rlim comparisons give exactly the equations below. -/
theorem completeCompactSupportProetale_isIso
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{t}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f')
    (gbar : c'.Z ⟶ c.Z)
    (properSquare : ChosenCartesianSquare gbar c'.g c.g g)
    (openSquare : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K) ∧
      ∀ (H : (cbcCompleteProperty d X r a ha).FullSubcategory)
        (k : K.obj ⟶ H.obj),
        (d.completedPull g).map
            ((d.push c.g).map
              ((cbcDerivedOpenShriek d c.i c.isOpenImmersion).map k)) ≫
            completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha H =
          completedCompactSupportExchange d c c' gbar properSquare openSquare r a ha K ≫
            (d.push c'.g).map
              ((cbcDerivedOpenShriek d c'.i c'.isOpenImmersion).map
                ((d.completedPull g').map k)) := by
  sorry


/-- Identity base change is the identity after the canonical completed identity maps.
The existential proofs only supply the complete-object inputs of those fixed maps.
Source: blueprint statement and proof step 7; Stacks 07A7, 099N
(blueprint: thm-cbc-complete-proetale).
Proof: write the exchange as Rlim of the proper mate followed by the open unit-mate.
Both identity mates are identities before evaluation. The quotient reconstruction and
open/limit comparisons preserve their units. Their conjugation is therefore precisely
the completed identity isomorphism displayed here, on K and on Rp_*j_!K. -/
theorem completeCompactSupportProetale_identity
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (sp : ChosenCartesianSquare (𝟙 c.Z) c.g c.g (𝟙 Y))
    (sj : OpenImmersionSquare (𝟙 X) c.i c.i (𝟙 c.Z))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    ∃ (hK : d.TowerComplete X K.obj)
      (hF : d.TowerComplete Y ((cbcSupport d c).obj K.obj)),
      cbcExchange d c c (𝟙 c.Z) sp sj r a ha K ≫
          (cbcSupport d c).map (d.completedPullId X K.obj hK).hom =
        (d.completedPullId Y ((cbcSupport d c).obj K.obj) hF).hom := by
  sorry

/-- Successive arbitrary base changes agree with the composite base change.
The intermediate completed pullback is complete; its proof is supplied in the conclusion
rather than assumed. The two completed pullback compositors have their unit normalization.
Source: blueprint statement and proof step 7; Stacks 07A7, 099N
(blueprint: thm-cbc-complete-proetale).
Proof: the strict-tower proper mate satisfies horizontal mate-pasting. Transpose the two
open comparisons; their transposes are the same iterated open unit, so beta satisfies the
same pasting equation. Substitute in the ordered two-factor exchange and move the middle
beta by naturality. Apply Rlim and cancel adjacent reconstruction comparisons. The
remaining outside comparisons are exactly d.completedPullComp, giving this equation.
Completed pullback preserves completeness by quotient/Koszul reconstruction. -/
theorem completeCompactSupportProetale_horizontal
    {X X' X'' Y Y' Y'' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (c'' : Compactification f'')
    (gb : c'.Z ⟶ c.Z) (hb : c''.Z ⟶ c'.Z)
    (sp₁ : ChosenCartesianSquare gb c'.g c.g g)
    (sj₁ : OpenImmersionSquare g' c'.i c.i gb)
    (sp₂ : ChosenCartesianSquare hb c''.g c'.g h)
    (sj₂ : OpenImmersionSquare h' c''.i c'.i hb)
    (sp : ChosenCartesianSquare (hb ≫ gb) c''.g c.g (h ≫ g))
    (sj : OpenImmersionSquare (h' ≫ g') c''.i c.i (hb ≫ gb))
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    ∃ hK' : cbcCompleteProperty d X' r a ha ((d.completedPull g').obj K.obj),
      cbcExchange d c c'' (hb ≫ gb) sp sj r a ha K =
        (d.completedPullComp h g).hom.app ((cbcSupport d c).obj K.obj) ≫
          (d.completedPull h).map (cbcExchange d c c' gb sp₁ sj₁ r a ha K) ≫
          cbcExchange d (qf := cbcBaseChangeQuasiCompact c c' gb sj₁)
            c' c'' hb sp₂ sj₂ r a ha ⟨(d.completedPull g').obj K.obj, hK'⟩ ≫
          (cbcSupport d c'').map ((d.completedPullComp h' g').inv.app K.obj) := by
  sorry

/-- Every normalized proper/open refinement map is invertible on the stated inputs.
No Cartesian hypothesis is imposed on the refinement square.
Source: blueprint statement and proof step 8; Stacks 0F7B, 09C9
(blueprint: thm-cbc-complete-proetale).
Proof: pass to the strict quotient tower after constant-coefficient restriction. The
section and unit normalizations identify gamma with the strict proper/open gamma.
Finite evaluation is the normalized finite-coefficient proper/open map on the retained
bounded-below origins, hence invertible by finite compact-support base change. The
cone is acyclic levelwise, so gamma is invertible as an actual derived strict-tower
map. Apply Rlim and the specified open/limit and proper composition comparisons. -/
theorem cbcRefinementMap_isIso
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ : Compactification f} (u : c₁.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (cbcRefinementMap d u K.obj) := by
  sorry

/-- The canonical compactification comparison through any supplied common refinement.
Its factors are the specified proper/open refinement maps, not chosen endpoint isos.
Source: blueprint proof step 8, I_12 (blueprint: thm-cbc-complete-proetale). -/
def cbcCompactificationComparison
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₀ c₁ c₂ : Compactification f} (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (cbcSupport d c₁).obj K.obj ≅ (cbcSupport d c₂).obj K.obj :=
  @asIso _ _ _ _ (cbcRefinementMap d u₁ K.obj)
      (cbcRefinementMap_isIso d u₁ r a ha K origins) ≪≫
    (@asIso _ _ _ _ (cbcRefinementMap d u₂ K.obj)
      (cbcRefinementMap_isIso d u₂ r a ha K origins)).symm

/-- Refinement maps are natural, unital and transitive. Compactification comparisons
are independent of the common refinement and its arrows, and satisfy the cocycle law.
Source: blueprint statement and proof step 8; Stacks 0F7C, 0F7D
(blueprint: thm-cbc-complete-proetale).
Proof: naturality follows from the proper/open mate and pushforward compositors.
Strict proper/open vertical composition with identity left proper arrows gives
C_vu = C_v followed by C_u, and the unit law gives C_id = 1. Apply Rlim to these actual
tower equations. For two common refinements take a common dominating refinement and
then equalize both pairs of arrows. Transitivity cancels the new invertible factors.
A common refinement of three compactifications likewise cancels the middle factors
and gives the cocycle. Nonemptiness covers the empty finite family. -/
theorem completeCompactSupportProetale_compactifications
    {X Y : Scheme.{t}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (∀ (c₁ c₂ : Compactification f) (u : c₁.Refinement c₂)
      (H : (cbcCompleteProperty d X r a ha).FullSubcategory) (k : K.obj ⟶ H.obj),
      (cbcSupport d c₂).map k ≫ cbcRefinementMap d u H.obj =
        cbcRefinementMap d u K.obj ≫ (cbcSupport d c₁).map k) ∧
    (∀ c : Compactification f,
      cbcRefinementMap d (Compactification.Refinement.id c) K.obj = 𝟙 _) ∧
    (∀ (c₁ c₂ c₃ : Compactification f) (u : c₁.Refinement c₂) (v : c₂.Refinement c₃),
      cbcRefinementMap d (u.comp v) K.obj =
        cbcRefinementMap d v K.obj ≫ cbcRefinementMap d u K.obj) ∧
    (∀ (c₀ c₀' c₁ c₂ : Compactification f)
      (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂)
      (v₁ : c₀'.Refinement c₁) (v₂ : c₀'.Refinement c₂),
      cbcCompactificationComparison d u₁ u₂ r a ha K origins =
        cbcCompactificationComparison d v₁ v₂ r a ha K origins) ∧
    (∀ (c₀ c₁ c₂ c₃ : Compactification f)
      (u₁ : c₀.Refinement c₁) (u₂ : c₀.Refinement c₂) (u₃ : c₀.Refinement c₃),
      cbcCompactificationComparison d u₁ u₂ r a ha K origins ≪≫
          cbcCompactificationComparison d u₂ u₃ r a ha K origins =
        cbcCompactificationComparison d u₁ u₃ r a ha K origins) := by
  sorry

/-- The completed exchange commutes with the specified refinement maps.
Thus its compactification comparisons are comparisons of the actual exchange, not
merely isomorphisms between its endpoints.
Source: blueprint statement and proof step 8, C'_u e^c2 = e^c1 G_g C_u
(blueprint: thm-cbc-complete-proetale).
Proof: restrict to constant coefficients and identify the ordered exchange with the
strict-tower proper mate followed by beta. The strict proper/open base-change interchange
moves gamma past these two factors. Proper mate-pasting then combines the proper factors.
This is an equality of strict derived tower maps before evaluation. Apply Rlim and the
unit-normalized coefficient, open and direct-image comparisons; their conjugates give
exactly the two paths displayed below. -/
theorem completeCompactSupportProetale_refinement
    {X X' Y Y' : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
    (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
    (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
    (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
    (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
    (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
    (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (d.completedPull g).map (cbcRefinementMap d u K.obj) ≫
        cbcExchange d c₁ c₁' gb₁ sp₁ sj₁ r a ha K =
      cbcExchange d c₂ c₂' gb₂ sp₂ sj₂ r a ha K ≫
        cbcRefinementMap d (qf := cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
          u' ((d.completedPull g').obj K.obj) := by
  sorry

/-- Vertical pasting for supplied compatible compactification towers, with their
proper/open composition maps. Both composition maps are invertible on these inputs.
The intermediate compact-support image is complete, rather than an extra hypothesis.
Source: blueprint statement and proof step 8; Stacks 0F7F, 07A7
(blueprint: thm-cbc-complete-proetale).
Proof: in the strict quotient-tower category combine the two open comparisons into
the comparison for their composite. The proper/open interchange moves the proper mate
past gamma, and proper mate-pasting combines the remaining proper exchanges. This is
exactly the exchange for the composite compactification. Gamma is invertible on the
retained finite-origin reductions; levelwise acyclicity and Rlim give invertibility of
the specified composition maps. Open extension preserves completeness and origins,
and proper direct image preserves completeness and the individual lower bounds.
Thus the second completed exchange is defined on Rf_!K. Apply Rlim to the strict
equality and cancel the specified comparisons to obtain the two paths below. -/
theorem completeCompactSupportProetale_vertical
    {X X' Y Y' Z Z' : Scheme.{t}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {h : Y ⟶ Z} {h' : Y' ⟶ Z'}
    {gx : X' ⟶ X} {gy : Y' ⟶ Y} {gz : Z' ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf : Compactification f) (ch : Compactification h)
    (chf : Compactification (f ≫ h))
    (cf' : Compactification f') (ch' : Compactification h')
    (chf' : Compactification (f' ≫ h'))
    (gbf : cf'.Z ⟶ cf.Z) (gbh : ch'.Z ⟶ ch.Z) (gbhf : chf'.Z ⟶ chf.Z)
    (spf : ChosenCartesianSquare gbf cf'.g cf.g gy)
    (sjf : OpenImmersionSquare gx cf'.i cf.i gbf)
    (sph : ChosenCartesianSquare gbh ch'.g ch.g gz)
    (sjh : OpenImmersionSquare gy ch'.i ch.i gbh)
    (sphf : ChosenCartesianSquare gbhf chf'.g chf.g gz)
    (sjhf : OpenImmersionSquare gx chf'.i chf.i gbhf)
    (b : cf.Z ⟶ chf.Z) (p : chf.Z ⟶ ch.Z)
    (b' : cf'.Z ⟶ chf'.Z) (p' : chf'.Z ⟶ ch'.Z)
    [IsProper p]
    [IsProper p']
    (hb : cf.i ≫ b = chf.i) (hp : b ≫ p = cf.g ≫ ch.i)
    (hq : p ≫ ch.g = chf.g)
    (hb' : cf'.i ≫ b' = chf'.i) (hp' : b' ≫ p' = cf'.g ≫ ch'.i)
    (hq' : p' ≫ ch'.g = chf'.g)
    (sq : IsPullback b cf.g p ch.i) (sq' : IsPullback b' cf'.g p' ch'.i)
    (_wb : b' ≫ gbhf = gbf ≫ b) (_wp : p' ≫ gbh = gbhf ≫ p)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    IsIso (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ∧
    IsIso (cbcTowerCompositionMap d
      (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
      cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj)) ∧
    ∃ hF : cbcCompleteProperty d Y r a ha ((cbcSupport d cf).obj K.obj),
      (d.completedPull gz).map (cbcTowerCompositionMap d cf ch chf b p hb hp hq sq K.obj) ≫
          cbcExchange d chf chf' gbhf sphf sjhf r a ha K =
        cbcExchange d ch ch' gbh sph sjh r a ha ⟨(cbcSupport d cf).obj K.obj, hF⟩ ≫
          (cbcSupport d ch').map (cbcExchange d cf cf' gbf spf sjf r a ha K) ≫
          cbcTowerCompositionMap d
            (qh := cbcBaseChangeQuasiCompact ch ch' gbh sjh)
            cf' ch' chf' b' p' hb' hp' hq' sq' ((d.completedPull gx).obj K.obj) := by
  sorry

/-- Composition comparisons are unchanged by refinements of compatible towers.
Together with refinement cofilteredness and the preceding cocycle law this removes
all choices of tower from the vertical pasting identification.
Source: blueprint statement and proof step 8, C_hf D_2 = D_1 (C_h F_f1) (F_h2 C_f)
(blueprint: thm-cbc-complete-proetale).
Proof: let B be the proper/open square between the two intermediate open parts,
H and J the source and base refinement squares, and F the total refinement square.
Strict proper/open vertical composition on B above Q_2 and on Q_1 above J identifies
their common outer gamma. Horizontal composition on H followed by B identifies gamma_F.
Whisker by the final proper direct image and the source open extension; naturality
moves gamma_Q2 past gamma_H. Proper composition gives precisely this displayed equality
in the strict derived tower category. Applying Rlim preserves the equality. A common
refining compatible tower and the refinement cocycle then remove the chosen tower. -/
theorem completeCompactSupportProetale_composition_refinement
    {X Y Z : Scheme.{t}} {f : X ⟶ Y} {h : Y ⟶ Z}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf₁ cf₂ : Compactification f) (ch₁ ch₂ : Compactification h)
    (chf₁ chf₂ : Compactification (f ≫ h))
    (b₁ : cf₁.Z ⟶ chf₁.Z) (p₁ : chf₁.Z ⟶ ch₁.Z)
    (b₂ : cf₂.Z ⟶ chf₂.Z) (p₂ : chf₂.Z ⟶ ch₂.Z)
    [IsProper p₁]
    [IsProper p₂]
    (hb₁ : cf₁.i ≫ b₁ = chf₁.i) (hp₁ : b₁ ≫ p₁ = cf₁.g ≫ ch₁.i)
    (hq₁ : p₁ ≫ ch₁.g = chf₁.g)
    (hb₂ : cf₂.i ≫ b₂ = chf₂.i) (hp₂ : b₂ ≫ p₂ = cf₂.g ≫ ch₂.i)
    (hq₂ : p₂ ≫ ch₂.g = chf₂.g)
    (sq₁ : IsPullback b₁ cf₁.g p₁ ch₁.i) (sq₂ : IsPullback b₂ cf₂.g p₂ ch₂.i)
    (uf : cf₁.Refinement cf₂) (uh : ch₁.Refinement ch₂) (uhf : chf₁.Refinement chf₂)
    (_wb : uf.hom ≫ b₂ = b₁ ≫ uhf.hom) (_wp : uhf.hom ≫ p₂ = p₁ ≫ uh.hom)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    cbcTowerCompositionMap d cf₂ ch₂ chf₂ b₂ p₂ hb₂ hp₂ hq₂ sq₂ K.obj ≫
        cbcRefinementMap d uhf K.obj =
      (cbcSupport d ch₂).map (cbcRefinementMap d uf K.obj) ≫
        cbcRefinementMap d uh ((cbcSupport d cf₁).obj K.obj) ≫
          cbcTowerCompositionMap d cf₁ ch₁ chf₁ b₁ p₁ hb₁ hp₁ hq₁ sq₁ K.obj := by
  sorry

end AlgebraicGeometry.Scheme
