/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.CompactificationCoherence
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.ProEtaleProperOpenComparison
public import Sheaf.Paper.FiniteDirectImageComposition
public import WeilConjectures.Compactification.CategoryBaseChange
public import Sheaf.SixFunctors.FrobeniusSquareCartesian
public import Sheaf.Paper.PbcActualRingedExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.AlgebraicGeometry.FrobeniusOpenSquare
public import Sheaf.Paper.SfIntegralDirectImageConstructible
public import Sheaf.Paper.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.Paper.WeilCompactSupportCohomology
public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Coefficient passage for the specified operation exchanges

Source: slopmaster2 blueprint, `def:weil-direct-image-object` and
`def:weil-compact-support-object`; Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: def-weil-operation-exchange-coefficient-descent).

## Main definitions

- `SupportModel`, `modelExchange`: retain the direct or chosen compactification recipe.
- `modelRationalExchange`: literal localization of the integral exchange.
- `stageBeta`, `commonStageExchange`: canonical scalar maps and common-stage descent.
- `intrinsicCompactificationComparison`: normalized transport of the landed comparison.
- `intrinsicCompactificationComparison_refinement`: its recorded-refinement normalization.
- `transportCompact`: the specified witnessed compactification transport.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange

variable (A : Type u) [CommRing A] [Finite A]

/-- The published comparison inverse image followed by its canonical realization.
Source: Stacks 099R; blueprint compact-support etale-origin paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def originUnderlying (X : Scheme.{u}) :=
  ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
    (sfIntrinsicModuleEquivalence X A).functor

/-- Additivity of the specified comparison and realization composite.
Source: Stacks 099R (blueprint: def-weil-operation-exchange-coefficient-descent). -/
instance originUnderlyingAdditive (X : Scheme.{u}) : (originUnderlying A X).Additive :=
  inferInstanceAs ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor).Additive)

/-- Exact comparison preserves finite limits.
Source: Stacks 099R (blueprint: def-weil-operation-exchange-coefficient-descent). -/
instance originUnderlyingLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (originUnderlying A X) :=
  inferInstanceAs (PreservesFiniteLimits (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor))

/-- Exact comparison preserves finite colimits.
Source: Stacks 099R (blueprint: def-weil-operation-exchange-coefficient-descent). -/
instance originUnderlyingColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (originUnderlying A X) :=
  inferInstanceAs (PreservesFiniteColimits (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X ⋙
      (sfIntrinsicModuleEquivalence X A).functor))

/-- The inverse image from the etale site, in the actual intrinsic derived category.
Source: Stacks 099R (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def origin (X : Scheme.{u}) := (originUnderlying A X).mapDerivedCategory

/-- An actual retained etale-origin triple, in the intrinsic constant-ring category.
Its morphisms below will be all ambient morphisms between its underlying objects.
Source: blueprint order 1472 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
structure CompactOrigin (X : Scheme.{u}) where
  /-- The original pro-etale object. -/
  K : proEtaleDerivedCategory X A
  /-- Its bounded below etale antecedent. -/
  L : DerivedCategory.Plus
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
  /-- The retained comparison, with no new antecedent chosen. -/
  alpha : (origin A X).obj L.obj ≅ K

/-- The induced category retains every ambient map, without requiring a map of witnesses.
Source: blueprint order 1472 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
abbrev CompactOriginCategory (X : Scheme.{u}) :=
  InducedCategory (proEtaleDerivedCategory X A) (fun O : CompactOrigin A X ↦ O.K)

/-- Forget only the retained witness, and preserve its actual underlying object and map.
Source: blueprint order 1472 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def compactOriginForget (X : Scheme.{u}) :
    CompactOriginCategory A X ⥤ proEtaleDerivedCategory X A :=
  inducedFunctor (fun O : CompactOrigin A X ↦ O.K)

/-- Cancel the realization unit in ordinary open extension, before exact descent.
Source: Stacks 00YV, 03DI (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedOpenModel {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence X A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence B A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence X A).unitIso.symm _ ≪≫
      Functor.leftUnitor _

/-- The exact-derived open model is fixed by the same ordinary realization unit.
Source: Stacks 00YV, 03DI (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedDerivedOpenModel {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence B A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (fixedOpenModel A j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- The fixed-scalar candidate, using precisely exact open extension then proper image.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedCompact {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  (ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory ⋙
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.g).rightDerivedFunctor

/-- The explicit coordinate change is open-unit cancellation followed by the recorded
section-normalized direct-image comparison. It contains no freely chosen isomorphism.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedCompactModel {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      fixedCompact A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (fixedDerivedOpenModel A c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The fixed antecedent comparison retains the given alpha and the exact-derived
composition map, with the canonical realization unit.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedOriginWitness (X : Scheme.{u}) (O : CompactOrigin A X) :
    (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj O.L.obj ≅
      (sfIntrinsicDerivedEquivalence X A).inverse.obj O.K :=
  (sfIntrinsicDerivedEquivalence X A).unitIso.app _ ≪≫
    (sfIntrinsicDerivedEquivalence X A).inverse.mapIso
      (((Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X)
        (sfIntrinsicModuleEquivalence X A).functor).app O.L.obj).symm ≪≫ O.alpha)

/-- The proper-open comparison conjugated by this very retained witness.
Source: blueprint order 1485 part (a); lem-weil-pbc-proper-open-comparison-proetale
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def fixedRefinementOpen {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOrigin A X) :
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.i).mapDerivedCategory.obj
        ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K) ≅
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r.hom).rightDerivedFunctor.obj
      ((ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.obj
          ((sfIntrinsicDerivedEquivalence X A).inverse.obj O.K)) :=
  (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.i).mapDerivedCategory.mapIso
        (fixedOriginWitness A X O).symm ≪≫
    ProEtale.properOpenProEtaleIso _ r.hom c.i d.i r.i_hom O.L ≪≫
    (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r.hom).rightDerivedFunctor.mapIso
        ((ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i).mapDerivedCategory.mapIso
            (fixedOriginWitness A X O))

/-- The actual refinement isomorphism: proper compositor followed by proper
pushforward of the inverse proper-open map, transported to intrinsic coordinates.
Source: blueprint order 1485 part (b)
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def intrinsicRefinement {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c ⟶ d) (O : CompactOrigin A X) :
    (sfIntrinsicCompactSupport c A).obj O.K ≅ (sfIntrinsicCompactSupport d A).obj O.K :=
  let e := sfIntrinsicDerivedEquivalence X A
  let q := sfIntrinsicDerivedEquivalence Y A
  let K := e.inverse.obj O.K
  let fixed : (fixedCompact A c).obj K ≅ (fixedCompact A d).obj K :=
    (eqToIso (congrArg
      (fun h ↦ (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) h).rightDerivedFunctor)
      r.hom_g.symm)).app _ ≪≫
      (ProEtale.finiteDirectImageComposition _ r.hom d.g).app _ ≪≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) d.g).rightDerivedFunctor.mapIso
          (fixedRefinementOpen A r O).symm
  (sfIntrinsicCompactSupport c A).mapIso (e.counitIso.app O.K).symm ≪≫
    (fixedCompactModel A c).app K ≪≫ q.functor.mapIso fixed ≪≫
    ((fixedCompactModel A d).app K).symm ≪≫
    (sfIntrinsicCompactSupport d A).mapIso (e.counitIso.app O.K)

/-- The candidate restricted to witnessed objects, with all ambient morphisms.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def intrinsicOriginCandidate {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  compactOriginForget A X ⋙ sfIntrinsicCompactSupport c A

/-- Transport the landed retained witness into intrinsic constant-ring coordinates.
The antecedent is unchanged; its comparison is the canonical exact-composition
isomorphism followed by the realized recorded fixed witness.
Source: blueprint prop-compactification-coherence, witnessed-domain paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def refinementIntrinsicOrigin (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (O : ProEtale.RefinementFiniteLevelOrigin l E n hn X) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    CompactOrigin (Padic.coefficientExtensionRing l E n) X := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : TopologicalSpace (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) := ⊥
  letI : DiscreteTopology (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) :=
    discreteTopology_bot _
  exact
    { K := (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor.obj
        (ProEtale.refinementFiniteLevelFixedObject l E n hn X O)
      L := O.2.L
      alpha := ((Functor.mapDerivedCategoryCompIso
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X)
        (sfIntrinsicModuleEquivalence X (Padic.coefficientExtensionRing l E n)).functor).app
          O.2.L.obj) ≪≫
        (sfIntrinsicDerivedEquivalence X (Padic.coefficientExtensionRing l E n)).functor.mapIso
          (ProEtale.refinementFixedWitnessIso X
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) O) }

section Coherence
variable (K₀ : Type u) [Field K₀]
  (l : ℕ) [Fact l.Prime] (hl : IsUnit (l : K₀))
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]

include hl xo yo xft xqc yft yqc fo fs fft fqc
/-- The canonical refinement maps are natural, unital and transitive; finite
families have common refinements and comparisons are independent of all choices.
Source: blueprint prop-compactification-coherence, proof paragraphs 1--4
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: proper-open comparison is natural for maps of etale antecedents. Full
faithfulness of etale comparison transports this naturality to every ambient
map between witnessed objects and proves witness independence. Its identity
and composition laws, together with the proper compositor, give the refinement
laws. Over a field the compactification category is cofiltered. Take a common
refinement and form theta(d,c1) inverse followed by theta(d,c2). To compare
two choices, refine both and equalize their arrows; transitivity cancels the
extra factors. A common refinement for three compactifications proves the
cocycle. Nonemptiness handles the empty finite family. Transport through the
explicit fixedCompactModel preserves every equality. -/
theorem intrinsicCompactificationCoherence :
    let A := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    ∃ theta : ∀ (c d : Compactification f) (_r : c ⟶ d),
        intrinsicOriginCandidate A c ≅ intrinsicOriginCandidate A d,
      (∀ (c d : Compactification f) (r : c ⟶ d) (O : CompactOriginCategory A X),
        (theta c d r).app O = intrinsicRefinement A r O) ∧
      (∀ c, theta c c (𝟙 c) = Iso.refl _) ∧
      (∀ (c d e : Compactification f) (r : c ⟶ d) (s : d ⟶ e),
        theta c e (r ≫ s) = theta c d r ≪≫ theta d e s) ∧
      (∀ (m : ℕ) (c : Fin m → Compactification f),
        ∃ d : Compactification f, ∀ i : Fin m, Nonempty (d ⟶ c i)) ∧
      ∃! comparison : ∀ c d : Compactification f,
          intrinsicOriginCandidate A c ≅ intrinsicOriginCandidate A d,
        ∀ (c d b : Compactification f) (r : b ⟶ c) (s : b ⟶ d),
          comparison c d = (theta b c r).symm ≪≫ theta b d s := by
  sorry

/-- The normalized pairwise comparison extracted from the universal coherence
statement. Its common-refinement formula determines it uniquely.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def intrinsicCompactificationComparison :
    let A := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    ∀ c d : Compactification f, intrinsicOriginCandidate A c ≅ intrinsicOriginCandidate A d :=
  let h := intrinsicCompactificationCoherence K₀ l hl E n hn f
  (h.choose_spec.2.2.2.2.exists.choose)

/-- The specified pairwise comparisons satisfy the cocycle on the witnessed
category, including equal compactifications.
Source: blueprint order 1485 (blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: choose a common refinement of c, d, e. Substitute the normalized formula
for each comparison. The adjacent theta and inverse cancel, giving the formula
for c to e. The same calculation with repeated entries gives the identity case. -/
theorem intrinsicCompactificationComparison_cocycle (c d e : Compactification f) :
    intrinsicCompactificationComparison K₀ l hl E n hn f c d ≪≫
      intrinsicCompactificationComparison K₀ l hl E n hn f d e =
        intrinsicCompactificationComparison K₀ l hl E n hn f c e := by
  let A := Padic.coefficientExtensionRing l E n
  let := Padic.finite_coefficientExtensionRing l E n hn
  let h := intrinsicCompactificationCoherence K₀ l hl E n hn f
  have hc := h.choose_spec.2.2.2.2.exists.choose_spec
  obtain ⟨b, hb⟩ := h.choose_spec.2.2.2.1 3 ![c, d, e]
  obtain ⟨r⟩ := hb 0
  obtain ⟨s⟩ := hb 1
  obtain ⟨t⟩ := hb 2
  change h.choose_spec.2.2.2.2.exists.choose c d ≪≫
      h.choose_spec.2.2.2.2.exists.choose d e =
    h.choose_spec.2.2.2.2.exists.choose c e
  rw [hc c d b r s, hc d e b s t, hc c e b r t]
  ext O
  simp

/-- The intrinsic pairwise comparison along a refinement is the landed specified
refinement comparison, transported by the canonical fixed-compact models. Thus the
comparison used in transportCompact is normalized by the recorded map, rather than
an independently chosen isomorphism of the same endpoints.
Source: blueprint prop-compactification-coherence, proper-composition formula and
common-refinement formula (blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: apply the normalization of compactification_coherence to the retained
witness O. Expand refinementComparisonIsomorphism and refinementIntrinsicOrigin.
Cancel the realization unit and counit in fixedCompactModel; the proper-open
factor is fixedRefinementOpen with exactly the same antecedent and alpha.
The direct-image factor is the same section-normalized finite compositor.
This identifies intrinsicRefinement with the conjugated recorded refinement.
Use the intrinsic common-refinement formula with the identity refinement at c
and its identity law to identify the pairwise comparison with this refinement.
All equalities are on the witnessed domain, including noncartesian refinements. -/
theorem intrinsicCompactificationComparison_refinement :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    ∀ (c d : Compactification f) (r : c ⟶ d)
      (O : ProEtale.RefinementFiniteLevelOrigin l E n hn X),
      (intrinsicCompactificationComparison K₀ l hl E n hn f c d).app
          (refinementIntrinsicOrigin l E n hn X O) =
        (fixedCompactModel (Padic.coefficientExtensionRing l E n) c).app
            (ProEtale.refinementFiniteLevelFixedObject l E n hn X O) ≪≫
          (sfIntrinsicDerivedEquivalence Y (Padic.coefficientExtensionRing l E n)).functor.mapIso
            (ProEtale.refinementComparisonIsomorphism K₀ l hl E n hn f r O) ≪≫
          ((fixedCompactModel (Padic.coefficientExtensionRing l E n) d).app
            (ProEtale.refinementFiniteLevelFixedObject l E n hn X O)).symm := by
  sorry

end Coherence


variable (A : Type u) [CommRing A] [Finite A]

section Geometry
variable (D : FiniteFieldDatum.{u})

/-- The base change of the given model morphism, with the dependency's chosen fibers.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
abbrev fiberMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  zlFiberMap D f₀

/-- The coefficient action of geometric field Frobenius, including non-finite-type models.
Source: Deligne, Weil II (1.1.14)
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
abbrev galois (X₀ : Over (Spec (.of D.k₀))) :=
  D.galoisMap X₀.hom (@FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k _
    (Fintype.ofFinite D.k₀) _ _ _)

/-- The finite direct-image Frobenius exchange on the full ambient derived category.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def finiteDirect {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  finiteTensorExchange A (fiberMap D f₀) (fiberMap D f₀) (galois D X₀) (galois D Y₀)
    (D.frobenius_square_cartesian X₀ Y₀ f₀).2.2.2.2.1

/-- Positive finite-quotient specialization of the ambient direct Frobenius mate.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def frobeniusDirectFinite (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (n : ℕ) (hn : 1 ≤ n) {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  finiteDirect (Padic.coefficientExtensionRing l E n) D f₀

end Geometry


section EtaleOrigin
variable (A : Type u) [CommRing A] [Finite A]

/-- Exact termwise etale inverse image in the coefficient universe of the small site.
Source: Stacks 03P2 (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def etalePull {X Y : Scheme.{u}} (g : X ⟶ Y) :=
  (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategory

/-- Cancel the canonical realization unit in transported inverse image.
Source: Stacks 00YV; lem-weil-pbc-comparison-pullback
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def realizationPullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y A).functor ⋙ sfIntrinsicPullback A g ≅
      ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (sfIntrinsicModuleEquivalence Y A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- The actual comparison mate commutes with inverse image before deriving.
Source: lem-weil-pbc-comparison-pullback; Stacks 098T, 099R
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def originUnderlyingPullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    originUnderlying A Y ⋙ sfIntrinsicPullback A g ≅
      Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g ⋙ originUnderlying A X :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y) (realizationPullback A g) ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight
      (ProEtale.comparisonUpperStarCompUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g) _ ≪≫
    Functor.associator _ _ _

/-- Exact descent of the specified comparison mate, in tensor-pullback coordinates.
Source: lem-weil-pbc-comparison-pullback; blueprint compact-support paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def originPullback {X Y : Scheme.{u}} (g : X ⟶ Y) :
    origin A Y ⋙ proEtaleConstantRingDerivedPullback A g ≅ etalePull A g ⋙ origin A X :=
  isoWhiskerLeft (origin A Y) (openSquareDerivedPullbackModel A g) ≪≫
    (Functor.mapDerivedCategoryCompIso (originUnderlying A Y)
      (sfIntrinsicPullback A g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (originUnderlyingPullback A g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The retained witness for Frobenius pullback uses exactly the pulled-back
etale antecedent, with the specified comparison, not a new existential antecedent.
Source: blueprint compact-support etale-origin paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def pulledOriginWitness {X : Scheme.{u}} (g : X ⟶ X)
    (L : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (K : proEtaleDerivedCategory X A) (a : (origin A X).obj L ≅ K) :
    (proEtaleConstantRingDerivedPullback A g).obj K ≅
      (origin A X).obj ((etalePull A g).obj L) :=
  (proEtaleConstantRingDerivedPullback A g).mapIso a.symm ≪≫ (originPullback A g).app L

set_option linter.unusedSectionVars false in
/-- Exact etale inverse image preserves the very same lower cohomological bound.
Source: Stacks 03P2; blueprint compact-support etale-origin paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: exact inverse image commutes with all cohomology objects. If cohomology
vanishes below b, the pulled-back cohomology also vanishes in those degrees.
This applies to the retained antecedent in pulledOriginWitness, including zero. -/
theorem etalePull_lowerBound {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) (b : ℤ) [L.IsGE b] :
    ((etalePull A g).obj L).IsGE b := by
  exact Functor.isGE_mapDerivedCategory_obj
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g) L b

/-- The actual pulled origin triple: keep the pulled pro-etale object and the
exact inverse image of its retained bounded below etale antecedent.
Source: blueprint compact-support etale-origin paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def pulledCompactOrigin {X : Scheme.{u}} (g : X ⟶ X)
    (O : CompactOriginCategory A X) : CompactOriginCategory A X where
  K := (proEtaleConstantRingDerivedPullback A g).obj O.K
  L := (Etale.upperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlus.obj O.L
  alpha := (origin A X).mapIso
      ((Etale.upperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).mapDerivedCategoryPlusCompatibility.app O.L) ≪≫
    ((originPullback A g).app O.L.obj).symm ≪≫
    (proEtaleConstantRingDerivedPullback A g).mapIso O.alpha

/-- Inverse image of the witnessed domain retains all ambient morphisms.
Source: blueprint compact-support etale-origin paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def pulledCompactOriginFunctor {X : Scheme.{u}} (g : X ⟶ X) :
    CompactOriginCategory A X ⥤ CompactOriginCategory A X where
  obj O := pulledCompactOrigin A g O
  map a := InducedCategory.homMk ((proEtaleConstantRingDerivedPullback A g).map a.hom)
  map_id O := InducedCategory.hom_ext ((proEtaleConstantRingDerivedPullback A g).map_id O.K)
  map_comp a b :=
    InducedCategory.hom_ext ((proEtaleConstantRingDerivedPullback A g).map_comp a.hom b.hom)

end EtaleOrigin

section CompactificationTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (hn : 1 ≤ n)
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c d : Compactification f)
  (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
  (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)

variable (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- Transport with the actual comparison of compactification coherence, evaluated
at the original witness and its specified pulled-back witness. The comparison
is not an arbitrary argument. The chosen c remains the middle construction.
Source: blueprint compact-support transport formula
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def transportCompact :
    let A := Padic.coefficientExtensionRing l E n
    letI := Padic.finite_coefficientExtensionRing l E n hn
    intrinsicOriginCandidate A d ⋙ proEtaleConstantRingDerivedPullback A gY ⟶
      pulledCompactOriginFunctor A gX ⋙ intrinsicOriginCandidate A d := by
  let A := Padic.coefficientExtensionRing l E n
  letI := Padic.finite_coefficientExtensionRing l E n hn
  let C := intrinsicCompactificationComparison K₀ l hl E n hn f d c
  exact whiskerRight C.hom (proEtaleConstantRingDerivedPullback A gY) ≫
    whiskerLeft (compactOriginForget A X) (finiteCompact l E n hn c gX gB gY wp sj) ≫
    whiskerLeft (pulledCompactOriginFunctor A gX) C.inv

end CompactificationTransport

section RawLocalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {X Y : Scheme.{u}}
  (F : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
  [F.Additive] [F.Linear (Padic.coefficientExtensionIntegers l E)]

/-- Extend the actual integral Hom map by the tensor universal property.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedHom (K L : sfRationalConstructibleCategory l E X) :
    (K ⟶ L) →ₗ[Localization.Away (Padic.coefficientExtensionUniformizer l E)]
      ((⟨F.obj K.obj⟩ : sfRationalConstructibleCategory l E Y) ⟶ ⟨F.obj L.obj⟩) :=
  (F.mapLinearMap (Padic.coefficientExtensionIntegers l E)).baseChange
    (Localization.Away (Padic.coefficientExtensionUniformizer l E))

/-- The explicit tensor action satisfies the functor laws.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: on pure tensors use the integral functor laws and the tensor-composition
formula of def-weil-rationalization-karoubi. Extend by additivity in both variables.
The identity is one tensored with the integral identity. -/
theorem localizedHom_laws :
    (∀ K : sfRationalConstructibleCategory l E X,
      localizedHom l E F K K (𝟙 K) =
        𝟙 (⟨F.obj K.obj⟩ : sfRationalConstructibleCategory l E Y)) ∧
    (∀ (K L M : sfRationalConstructibleCategory l E X) (a : K ⟶ L) (b : L ⟶ M),
      localizedHom l E F K M (a ≫ b) =
        localizedHom l E F K L a ≫ localizedHom l E F L M b) := by
  constructor
  · intro K
    change (1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ
      F.map (𝟙 K.obj) = (1 : Localization.Away _) ⊗ₜ 𝟙 (F.obj K.obj)
    rw [F.map_id]
  · intro K L M a b
    change localizedHom l E F K M
      (ScalarLocalization.composition _ _ _ K.obj L.obj M.obj b a) =
        ScalarLocalization.composition _ _ _ _ _ _
          (localizedHom l E F L M b) (localizedHom l E F K L a)
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul d b =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul c a =>
        rw [ScalarLocalization.composition_tmul]
        change ((d * c) ⊗ₜ F.map (a ≫ b)) =
          ScalarLocalization.composition _ _ _ _ _ _ (d ⊗ₜ F.map b) (c ⊗ₜ F.map a)
        rw [ScalarLocalization.composition_tmul, F.map_comp]
      | add a a' ha ha' => simp [_root_.map_add, ha, ha']
    | add b b' hb hb' => simp [_root_.map_add, hb, hb']

/-- Raw scalar localization of an actual operation, with unchanged objects and
explicit tensor Hom maps. No idempotent completion or rational reduction occurs.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedFunctor :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y where
  obj K := ⟨F.obj K.obj⟩
  map {K L} a := localizedHom l E F K L a
  map_id K := (localizedHom_laws l E F).1 K
  map_comp a b := (localizedHom_laws l E F).2 _ _ _ a b

variable (G : sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y)
  [G.Additive] [G.Linear (Padic.coefficientExtensionIntegers l E)] (τ : F ⟶ G)

/-- Naturality of the explicitly localized components holds for every tensor Hom.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: for one pure tensor the equation is integral naturality multiplied by its
scalar. Tensor balancing and addition prove the equation for an arbitrary Hom. -/
theorem localizedTransformation_naturality (K L : sfRationalConstructibleCategory l E X)
    (a : K ⟶ L) :
    (localizedFunctor l E F).map a ≫
        (sfRationalConstructibleLocalization l E Y).map (τ.app L.obj) =
      (sfRationalConstructibleLocalization l E Y).map (τ.app K.obj) ≫
        (localizedFunctor l E G).map a := by
  change ScalarLocalization.composition _ _ _ _ _ _
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ τ.app L.obj)
      (localizedHom l E F K L a) =
    ScalarLocalization.composition _ _ _ _ _ _ (localizedHom l E G K L a)
      ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l E)) ⊗ₜ τ.app K.obj)
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c a =>
    change ScalarLocalization.composition _ _ _ _ _ _ (1 ⊗ₜ τ.app L.obj)
        (c ⊗ₜ F.map a) =
      ScalarLocalization.composition _ _ _ _ _ _ (c ⊗ₜ G.map a) (1 ⊗ₜ τ.app K.obj)
    simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, τ.naturality a]
  | add a b ha hb => simp [_root_.map_add, ha, hb]

/-- Localize precisely the integral exchange components, tensoring them with one.
Source: blueprint rational-coefficient paragraphs
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def localizedTransformation : localizedFunctor l E F ⟶ localizedFunctor l E G where
  app K := (sfRationalConstructibleLocalization l E Y).map (τ.app K.obj)
  naturality K L a := localizedTransformation_naturality l E F G τ K L a

private theorem localizedFunctor_comp {Z : Scheme.{u}}
    (H : sfIntegralConstructibleCategory l E Y ⥤ sfIntegralConstructibleCategory l E Z)
    [H.Additive] [H.Linear (Padic.coefficientExtensionIntegers l E)] :
    localizedFunctor l E (F ⋙ H) = localizedFunctor l E F ⋙ localizedFunctor l E H := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro K L a
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change localizedHom l E (F ⋙ H) K L a =
    localizedHom l E H _ _ (localizedHom l E F K L a)
  dsimp only [localizedHom]
  induction a using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c a =>
    change c ⊗ₜ H.map (F.map a) = c ⊗ₜ H.map (F.map a)
    rfl
  | add a b ha hb => simp only [_root_.map_add, ha, hb]

end RawLocalization

section CoefficientPassage
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [ix : ∀ x : X, Invertible (l : X.residueField x)]
  [iy : ∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]

/-- Integral pullback is additive and linear for constant completed scalars.
Source: blueprint scalar-localization paragraph; Stacks 099N(5)
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: use its single K-flat quotient presentation. Termwise inverse image and
its scalar tensor maps are additive and O_E-linear; the quotient transitions,
restriction and normalized total-limit maps respect these identities. -/
theorem pullback_linear (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    (constructibleIntegralPullback l E g).Additive ∧
      (constructibleIntegralPullback l E g).Linear (Padic.coefficientExtensionIntegers l E) := by
  sorry

/-- The localized pullback is the recorded rational pullback, on objects and
all tensor Hom maps, without adding an idempotent completion.
Source: def-weil-derived-pullback-tensor-hom, rational normalization
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: both functors keep the integral representative and send each pure tensor
a tensor v to a tensor g*(v). Tensor induction gives equality on all Homs;
functor extensionality and proof irrelevance identify the functors. -/
theorem localizedPullback_eq (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    letI := (pullback_linear l E T g).1
    letI := (pullback_linear l E T g).2
    localizedFunctor l E (constructibleIntegralPullback l E g) =
      rationalDerivedPullback l E g := by
  let := (pullback_linear l E T g).1
  let := (pullback_linear l E T g).2
  apply (rationalDerivedPullback_existsUnique l E g).unique
  · refine ⟨?_, fun K ↦ rfl, ?_⟩
    · exact ⟨fun {K L} {a b} ↦ (localizedHom l E _ K L).map_add a b⟩
    · intro K L a c
      apply heq_of_eq
      exact LinearMap.baseChange_tmul _ _ _
  · exact (rationalDerivedPullback_existsUnique l E g).exists.choose_spec

end CoefficientPassage

/-- Select one of the two specified recipes, retaining the compactification
and its actual Frobenius squares in the compact-support case.
Source: blueprint `def:weil-direct-image-object`, `def:weil-compact-support-object`
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
inductive SupportModel {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
  | direct (w : gX ≫ f = f ≫ gY)
  | compact (c : Compactification f) (gB : c.Z ⟶ c.Z)
      (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)

section CoefficientDescent
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [ix : ∀ x : X, Invertible (l : X.residueField x)]
  [iy : ∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY] (M : SupportModel f gX gY)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The already constructed actual integral operation selected by the retained recipe.
Source: blueprint coefficient passages
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelFunctor :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  match M with
  | .direct _ => directImageFunctor l E K₀ hl f
  | .compact c _ _ _ => sfCompactSupportFiniteIntegralFunctor l K₀ hl c E

/-- The specified integral exchange, selected without selecting any morphism data.
Source: blueprint coefficient passages
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelExchange : modelFunctor l K₀ hl f gX gY M E ⋙
      constructibleIntegralPullback l E gY ⟶
    constructibleIntegralPullback l E gX ⋙ modelFunctor l K₀ hl f gX gY M E :=
  match M with
  | .direct w => directIntegral l E K₀ hl f gX gY w
  | .compact c gB wp sj => compactIntegral l E K₀ hl f c gX gB gY wp sj

set_option linter.unusedSectionVars false in
/-- The inherited linearity proofs for the selected actual operation.
Source: blueprint scalar localization
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
theorem modelLinear : (modelFunctor l K₀ hl f gX gY M E).Additive ∧
    (modelFunctor l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  cases M with
  | direct w => exact directImage_linear l E K₀ hl f
  | compact c gB wp sj => exact sfCompactSupportFiniteIntegralFunctor_linear l K₀ hl c E

/-- The specified source composite on integral representatives.
Source: blueprint FrEx source (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSource := modelFunctor l K₀ hl f gX gY M E ⋙ constructibleIntegralPullback l E gY

/-- The specified target composite on integral representatives.
Source: blueprint FrEx target (blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelTarget := constructibleIntegralPullback l E gX ⋙ modelFunctor l K₀ hl f gX gY M E

/-- Linearity of the complete source composite, with its actual constant action.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: modelLinear and pullback_linear supply additive O_E-linear factors;
composition preserves both structures and their specified constant actions. -/
theorem modelSource_linear :
    (modelSource l K₀ hl f gX gY M E).Additive ∧
      (modelSource l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E Y gY).1
  let := (pullback_linear l E Y gY).2
  exact ⟨inferInstanceAs (_ ⋙ _).Additive, inferInstanceAs ((_ ⋙ _).Linear _)⟩

/-- Linearity of the complete target composite, in the prescribed opposite order.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: pullback_linear followed by modelLinear gives the additive O_E-linear
composition on the target, with exactly the same constant coefficient action. -/
theorem modelTarget_linear :
    (modelTarget l K₀ hl f gX gY M E).Additive ∧
      (modelTarget l K₀ hl f gX gY M E).Linear (Padic.coefficientExtensionIntegers l E) := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E X gX).1
  let := (pullback_linear l E X gX).2
  exact ⟨inferInstanceAs (_ ⋙ _).Additive, inferInstanceAs ((_ ⋙ _).Linear _)⟩

/-- The rational operation uses the recorded compact-support functor at the retained c.
The direct-image case is literal localization of its constructed integral action.
Source: blueprint rational coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalFunctor :
    sfRationalConstructibleCategory l E X ⥤ sfRationalConstructibleCategory l E Y :=
  match M with
  | .direct _ =>
    letI := (directImage_linear l E K₀ hl f).1
    letI := (directImage_linear l E K₀ hl f).2
    localizedFunctor l E (directImageFunctor l E K₀ hl f)
  | .compact c _ _ _ => sfCompactSupportFiniteFunctor l K₀ hl c E

/-- The rational source, with the recorded rational operations.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalSource :=
  modelRationalFunctor l K₀ hl f gX gY M E ⋙ rationalDerivedPullback l E gY

/-- The rational target, in the specified opposite order.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalTarget :=
  rationalDerivedPullback l E gX ⋙ modelRationalFunctor l K₀ hl f gX gY M E

/-- Raw localization of the integral source is the recorded rational source.
Source: blueprint rational paragraph; def-weil-rationalization-karoubi
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: the compact branch uses precisely sfCompactSupportFiniteIntegralFunctor.
Its localization has the same objects and baseChange Hom map as
sfCompactSupportFiniteFunctor. For direct image this is the definition. Use the
pure-tensor normalization of rationalDerivedPullback and composition on pure
tensors; tensor induction and functor extensionality give equality on all maps. -/
theorem modelRationalSource_eq :
    letI := (modelSource_linear l K₀ hl f gX gY M E).1
    letI := (modelSource_linear l K₀ hl f gX gY M E).2
    localizedFunctor l E (modelSource l K₀ hl f gX gY M E) =
      modelRationalSource l K₀ hl f gX gY M E := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E Y gY).1
  let := (pullback_linear l E Y gY).2
  dsimp only [modelSource, modelRationalSource]
  rw [localizedFunctor_comp, localizedPullback_eq]
  cases M with
  | direct w => rfl
  | compact c gB wp sj => rfl

/-- The same literal localization identity for the target composite.
Source: blueprint rational paragraph; def-weil-rationalization-karoubi
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: use the preceding pure-tensor computation in the opposite functor order.
The retained c and the integral object representatives are the same; only the
order of the two actual tensor Hom maps changes. Tensor induction proves the
identity on every Hom, and functor extensionality concludes. -/
theorem modelRationalTarget_eq :
    letI := (modelTarget_linear l K₀ hl f gX gY M E).1
    letI := (modelTarget_linear l K₀ hl f gX gY M E).2
    localizedFunctor l E (modelTarget l K₀ hl f gX gY M E) =
      modelRationalTarget l K₀ hl f gX gY M E := by
  let := (modelLinear l K₀ hl f gX gY M E).1
  let := (modelLinear l K₀ hl f gX gY M E).2
  let := (pullback_linear l E X gX).1
  let := (pullback_linear l E X gX).2
  dsimp only [modelTarget, modelRationalTarget]
  rw [localizedFunctor_comp, localizedPullback_eq]
  cases M with
  | direct w => rfl
  | compact c gB wp sj => rfl

/-- Rational exchange is the literal image of the integral exchange, expressed
on the recorded rational compact-support functor in its compact branch.
Source: blueprint rational paragraph
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalExchange : modelRationalSource l K₀ hl f gX gY M E ⟶
    modelRationalTarget l K₀ hl f gX gY M E :=
  letI := (modelSource_linear l K₀ hl f gX gY M E).1
  letI := (modelSource_linear l K₀ hl f gX gY M E).2
  letI := (modelTarget_linear l K₀ hl f gX gY M E).1
  letI := (modelTarget_linear l K₀ hl f gX gY M E).2
  (eqToIso (modelRationalSource_eq l K₀ hl f gX gY M E)).inv ≫
    localizedTransformation l E (modelSource l K₀ hl f gX gY M E)
      (modelTarget l K₀ hl f gX gY M E) (modelExchange l K₀ hl f gX gY M E) ≫
    (eqToIso (modelRationalTarget_eq l K₀ hl f gX gY M E)).hom

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The actual completed integral coefficient extension used by the stage system.
Source: def-weil-algebraically-closed-coefficients
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
abbrev scalar (T : Scheme.{u}) := sfConstructibleIntegralScalarExtension 0 l
  (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι T

/-- The pullback scalar comparison is fixed at every object by the recorded
K-flat normalized comparison, rather than an arbitrary natural isomorphism.
Source: def-weil-derived-pullback-tensor-hom, scalar comparison
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: integralPullbackScalarComparison is induced by the balanced tensor chain
map on the single K-flat quotient system. It is natural on complexes and roofs.
Its components determine the natural isomorphism uniquely. -/
theorem pullScalar_existsUnique (T : Scheme.{u})
    [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :
    ∃! b : constructibleIntegralPullback l E g ⋙ scalar l E L ι T ≅
      scalar l E L ι T ⋙ constructibleIntegralPullback l L g,
      ∀ K, b.app K = integralPullbackScalarComparison l E L ι g K := by
  refine ⟨NatIso.ofComponents (fun K ↦ integralPullbackScalarComparison l E L ι g K)
    ?_, fun K ↦ rfl, ?_⟩
  · intro K N a
    apply ObjectProperty.hom_ext
    let b : (sfIntegralConstructible l E T).ι ⋙ integralOrdinaryDerivedScalar l E L ι T ≅
        (sfIntegralConstructible l E T).ι ⋙ integralScalarExtension l E L ι T :=
      NatIso.ofComponents (fun K ↦ scalarCompletionIso l E L ι T K.obj K.property.1)
        (fun {K N} a ↦ (scalarCompletion l E L ι T).naturality a.hom)
    let q := isoWhiskerLeft (constructibleIntegralPullback l E g) b.symm ≪≫
      isoWhiskerLeft (sfIntegralConstructible l E T).ι (scalarPullbackOrdinary l E L ι g) ≪≫
      isoWhiskerRight b (integralDerivedPullback l L g)
    exact q.hom.naturality a
  · intro b hb
    ext K
    exact congrArg (fun i ↦ i.hom.hom) (hb K)

/-- The specified integral pullback scalar comparison.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def pullScalar (T : Scheme.{u}) [∀ t : T, Invertible (l : T.residueField t)] (g : T ⟶ T) :=
  (pullScalar_existsUnique l E L ι T g).exists.choose

/-- The coefficient mate for the recorded integral compact-support functor,
conjugated by the projection-normalized system identifications at E and L.
Source: lem-fix-operation-reduction, compact-support coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def compactCoefficientExchange (c : Compactification f) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtensionOfUniverses l E L ι Y ⟶
      scalar l E L ι X ⋙ sfCompactSupportFiniteIntegralFunctor l K₀ hl c L ⋙
        (sfIntegralConstructible l L Y).ι :=
  whiskerRight (compactRealization l E K₀ hl f c).hom
      (integralScalarExtensionOfUniverses l E L ι Y) ≫
    coefficientExchange l E L ι
      (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)
      (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g)
      (systemCompactScalar l E L ι c) ≫
    whiskerLeft (scalar l E L ι X) (compactRealization l L K₀ hl f c).inv

/-- Coefficient change of the selected operation is the constructed whole-system mate.
Source: lem-fix-operation-reduction; blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelScalarMap : modelFunctor l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ⟶
    scalar l E L ι X ⋙ modelFunctor l K₀ hl f gX gY M L := by
  cases M with
  | direct _w =>
    exact
      { app := fun K ↦ ObjectProperty.homMk
          ((coefficientExchange l E L ι (systemDirect l E f) (systemDirect l L f)
            (systemDirectScalar l E L ι f)).app K)
        naturality := fun _K _N a ↦ ObjectProperty.hom_ext _
          ((coefficientExchange l E L ι (systemDirect l E f) (systemDirect l L f)
            (systemDirectScalar l E L ι f)).naturality a) }
  | compact c _gB _wp _sj =>
    exact
      { app := fun K ↦ ObjectProperty.homMk
          ((compactCoefficientExchange l K₀ hl f E L ι c).app K)
        naturality := fun _K _N a ↦ ObjectProperty.hom_ext _
          ((compactCoefficientExchange l K₀ hl f E L ι c).naturality a) }

include hl xo yo xft xqc yft yqc fo ix iy in
/-- Finite coefficient extension makes this actual integral mate invertible.
Source: lem-fix-operation-reduction; finite-free completed scalar comparison
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: the finite integral coefficient extension is finite free. Its ordinary
tensor is a finite direct sum locally on coefficients and commutes with direct
image, exact open extension and total derived inverse limit on these complete
constructible inputs. The balanced tensor identifications on simultaneous
K-flat and K-injective representatives identify the inverse with the displayed
mate. This proves invertibility of that constructed map, also for ramification;
no global flatness of the finite quotient-ring inclusion is asserted. -/
theorem modelScalarMap_isIso : IsIso (modelScalarMap l K₀ hl f gX gY M E L ι) := by
  sorry

/-- The actual integral operation scalar isomorphism.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelScalar :=
  letI := modelScalarMap_isIso l K₀ hl f gX gY M E L ι
  asIso (modelScalarMap l K₀ hl f gX gY M E L ι)

/-- Scalar comparison for the source composite, in its prescribed order.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSourceScalar : modelSource l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ modelSource l K₀ hl f gX gY M L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (modelFunctor l K₀ hl f gX gY M E) (pullScalar l E L ι Y gY) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (modelScalar l K₀ hl f gX gY M E L ι)
      (constructibleIntegralPullback l L gY) ≪≫
    Functor.associator _ _ _

/-- Scalar comparison for the target composite, in its prescribed order.
Source: blueprint coefficient passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelTargetScalar : modelTarget l K₀ hl f gX gY M E ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ modelTarget l K₀ hl f gX gY M L :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (constructibleIntegralPullback l E gX) (modelScalar l K₀ hl f gX gY M E L ι) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (pullScalar l E L ι X gX) (modelFunctor l K₀ hl f gX gY M L) ≪≫
    Functor.associator _ _ _

/-- Select source or target while retaining its prescribed integral comparison.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelSideScalar (target : Bool) :
    (if target then modelTarget l K₀ hl f gX gY M E
      else modelSource l K₀ hl f gX gY M E) ⋙ scalar l E L ι Y ≅
    scalar l E L ι X ⋙ (if target then modelTarget l K₀ hl f gX gY M L
      else modelSource l K₀ hl f gX gY M L) := by
  cases target with
  | false => exact modelSourceScalar l K₀ hl f gX gY M E L ι
  | true => exact modelTargetScalar l K₀ hl f gX gY M E L ι

/-- Rational scalar comparison fixed by localization of the already constructed
integral scalar maps, on both source and target composites.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: localize each specified integral component. The pure tensor scalar-action
formula proves naturality for every rational Hom. Its inverse localizes as well.
The component formula determines the comparison uniquely. -/
theorem modelRationalScalar_existsUnique (target : Bool) :
    let R := if target then modelRationalTarget l K₀ hl f gX gY M E
      else modelRationalSource l K₀ hl f gX gY M E
    let R' := if target then modelRationalTarget l K₀ hl f gX gY M L
      else modelRationalSource l K₀ hl f gX gY M L
    ∃! b : R ⋙ sfRationalScalarExtension l E Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
        sfRationalScalarExtension l E X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙ R',
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K) ((sfRationalConstructibleLocalization l L Y).map
          ((modelSideScalar l K₀ hl f gX gY M E L ι target).hom.app K.obj)) := by
  sorry

/-- The normalized rational comparison, retaining the whole-system integral mate.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def modelRationalScalar (target : Bool) :=
  (modelRationalScalar_existsUnique l K₀ hl f gX gY M E L ι target).exists.choose

end CoefficientDescent

attribute [irreducible] modelRationalSource modelRationalTarget modelRationalExchange
  modelFunctor modelSource modelTarget modelScalar modelSourceScalar modelTargetScalar
  modelRationalScalar

section CommonStage
open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
variable (l : ℕ) [Fact l.Prime]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY] (M : SupportModel f gX gY)
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The prescribed rational source or target at the actual finite coefficient stage.
Source: blueprint common-stage passage
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageSide (target : Bool) (E : Index l Ω) : Stage l Ω X E ⥤ Stage l Ω Y E :=
  if target then modelRationalTarget l K₀ hl f gX gY M (Coefficient.{u} l Ω E)
    else modelRationalSource l K₀ hl f gX gY M (Coefficient.{u} l Ω E)

/-- The actual beta: whole-system coefficient mate, localized, then expressed in
the recorded stage-system transitions. No comparison is supplied as an input.
Source: blueprint common-stage passage; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageBeta (target : Bool) {E L : Index l Ω} (h : E ≤ L) :
    stageSide l K₀ hl f gX gY M Ω target E ⋙ (stageSystem l Ω Y).T h ≅
      (stageSystem l Ω X).T h ⋙ stageSide l K₀ hl f gX gY M Ω target L :=
  isoWhiskerLeft (stageSide l K₀ hl f gX gY M Ω target E)
      (operationStageTransitionIso l Ω Y E L h) ≪≫
    modelRationalScalar l K₀ hl f gX gY M (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (coefficientInclusion l Ω E L h) target ≪≫
    isoWhiskerRight (operationStageTransitionIso l Ω X E L h).symm
      (stageSide l K₀ hl f gX gY M Ω target L)

/-- The specified scalar comparisons obey the full coefficient-tower cocycle,
including repeated fields and the identity coefficient embedding.
Source: lem-fix-operation-reduction; Stacks 06YY, 0941
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: at the system level both scalar chains are the same balanced tensor map
on each simultaneous K-flat representative. The normalized pullback and ordinary
section-direct-image compositors preserve this map. Mate pasting proves the
corresponding direct-image and open-adjunction identities. The actual system
counits and total-limit functor preserve the identities. Localize those exact
maps, and cancel the stage transition identifications. This is precisely the
displayed cocycle with the recorded scalar associators. -/
theorem stageBeta_coherence (target : Bool) (E L N : Index l Ω)
    (h : E ≤ L) (k : L ≤ N) (K : Stage l Ω X E) :
    ((stageSystem l Ω Y).T k).map
        ((stageBeta l K₀ hl f gX gY M Ω target h).hom.app K) ≫
      (stageBeta l K₀ hl f gX gY M Ω target k).hom.app
        (((stageSystem l Ω X).T h).obj K) ≫
      (stageSide l K₀ hl f gX gY M Ω target N).map
        (((stageSystem l Ω X).assoc h k).hom.app K) =
    ((stageSystem l Ω Y).assoc h k).hom.app
        ((stageSide l K₀ hl f gX gY M Ω target E).obj K) ≫
      (stageBeta l K₀ hl f gX gY M Ω target (h.trans k)).hom.app K := by
  sorry

/-- The coherent family uses the explicit beta just constructed, so the induced
common-stage operation has the canonical representative formula.
Source: prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageAction (target : Bool) :
    StageSystem.Morphism (stageSystem l Ω X) (stageSystem l Ω Y) where
  Φ := stageSide l K₀ hl f gX gY M Ω target
  β h := stageBeta l K₀ hl f gX gY M Ω target h
  coh h k K := stageBeta_coherence l K₀ hl f gX gY M Ω target _ _ _ h k K

/-- The constructed exchanges commute with the constructed canonical scalar betas.
Source: lem-fix-operation-reduction; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent).
Proof: expand the system exchange and coefficient comparison into their actual
pullback-composition maps, units and counits. The normalized scalar/pullback
associator commutes with the Frobenius square. Naturality and mate pasting give
the coefficient square in the derived category of whole systems. The same
calculation for the inverse open mate proves the compact-support square, keeping
the same c. Apply exact scalar restriction and total inverse limit to this
identity, compose with the specified alpha and beta, and localize. This yields
the equation below before passing to common-stage morphism classes. -/
theorem stageExchange_compatible (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E) :
    ((stageSystem l Ω Y).T h).map
        ((modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω E)).app K) ≫
      (stageBeta l K₀ hl f gX gY M Ω true h).hom.app K =
    (stageBeta l K₀ hl f gX gY M Ω false h).hom.app K ≫
      (modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω L)).app
        (((stageSystem l Ω X).T h).obj K) := by
  sorry

/-- The compatible exchange family is fixed at every finite stage by its
localized integral component.
Source: prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def stageExchange : StageSystem.Morphism.Hom
    (stageAction l K₀ hl f gX gY M Ω false) (stageAction l K₀ hl f gX gY M Ω true) where
  τ E := modelRationalExchange l K₀ hl f gX gY M (Coefficient.{u} l Ω E)
  comm h K := stageExchange_compatible l K₀ hl f gX gY M Ω _ _ h K

/-- The common-stage Frobenius exchange: at (E,K) its component is exactly the
morphism class of the rational exchange at E. Its naturality includes every
common-stage representative by the existing descent construction. No Karoubi
completion and no finite reduction of a rational object occur.
Source: blueprint common-stage paragraphs; prop-weil-pbc-descent-functors
(blueprint: def-weil-operation-exchange-coefficient-descent). -/
def commonStageExchange :
    (stageAction l K₀ hl f gX gY M Ω false).functor ⟶
      (stageAction l K₀ hl f gX gY M Ω true).functor :=
  StageSystem.Morphism.descNatTrans (stageExchange l K₀ hl f gX gY M Ω)

end CommonStage

end WeilConjectures.FrobeniusExchange
