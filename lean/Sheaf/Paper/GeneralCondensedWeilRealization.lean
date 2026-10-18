/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q122
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CommonStageCompactWeilCohomology
public import Sheaf.Paper.CondensedPointSupertrace
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.GlobalGeometricFrobenius
public import Sheaf.Paper.LocalFrobeniusTrace
public import Sheaf.Paper.PointRealizationCoefficientComparison
public import Sheaf.Paper.SfWeilSheafComplex
public import Sheaf.SixFunctors.FrobeniusFixedPoints
public import Sheaf.SixFunctors.SchemeFrobenius
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.TraceFormula.Statement
import Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite
import Sheaf.AlgebraicGeometry.SchemeFrobeniusFiniteRadicial
import Sheaf.Paper.CondensedERealization
import Sheaf.Paper.CondensedFlatCoefficientCalculus
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.FrobeniusCoefficientReductionCoherence
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.LocalFrobeniusTransportNormalization
import Sheaf.Paper.ModelCompactComparisonUnit
import Sheaf.Paper.ProfinitePointPullback
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.Compactification.Dense
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # Condensed realization of finite-stage Weil complexes

Source: main-20261015, sec-zeta-weil/sk-thm-tracetodeterminant,
prop-every-iterate-trace.proof.md, coefficient/operator comparison prerequisite
(blueprint: lem-zl-general-condensed-weil-realization).

All comparisons below concern objects and specified operators; no trace identity occurs.
The source coefficient field is the dependency's canonical universe lift of E.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace WeilConjectures

/-- The geometric Frobenius composite at the finite coefficient presentation.
Source: blueprint order 2061, the ordinary and compact Frobenius composites
(blueprint: lem-zl-general-condensed-weil-realization).
This helper uses the defining composites of globalGeometricFrobenius with a field
presentation, so it also applies to the canonical FieldModel = ULift E.val. -/
def globalGeometricFrobeniusForField
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (c₀ : Compactification Y₀.hom)
    (K : sfWeilComplex D l hl Y₀ E) :
    End ((frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).obj K.carrier) ×
      End ((frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ true).obj K.carrier) :=
  ((frobeniusCohomologyTransportRational D l hl E Y₀ c₀ K.carrier).1 ≫
      (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ false).map K.str.hom,
    (frobeniusCohomologyTransportRational D l hl E Y₀ c₀ K.carrier).2 ≫
      (frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ true).map K.str.hom)

end WeilConjectures

namespace WeilConjectures.GeneralCondensedWeil

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField l)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The model Frobenius as a morphism over k, using its recorded projection equation.
Source: scheme/model Frobenius in the realization comparison
(blueprint: lem-zl-general-condensed-weil-realization). -/
def modelFrobenius : D.geometricFiber Y₀ ⟶ D.geometricFiber Y₀ :=
  Over.homMk (D.schemeFrobenius Y₀) (D.relativeFrobenius_projections Y₀).2

/-- The inherited finite-type structure on the geometric fibre.
Source: the realization proof, step 1
(blueprint: lem-zl-general-condensed-weil-realization). -/
instance fiberLocallyFiniteType : LocallyOfFiniteType (D.geometricFiber Y₀).hom :=
  (FrobeniusExchange.fiber_finiteType D Y₀).1

/-- The inherited quasi-compactness of the geometric fibre.
Source: the realization proof, step 1
(blueprint: lem-zl-general-condensed-weil-realization). -/
instance fiberQuasiCompact : QuasiCompact (D.geometricFiber Y₀).hom :=
  (FrobeniusExchange.fiber_finiteType D Y₀).2

/-- Separatedness is preserved by the recorded base change.
Source: the realization statement, separated finite-type model
(blueprint: lem-zl-general-condensed-weil-realization). -/
instance fiberSeparated : IsSeparated (D.geometricFiber Y₀).hom :=
  inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))

/-- The source fixed-pair category at the canonical lift of the finite subextension.
Source: the realization statement, finite-stage Weil datum
(blueprint: lem-zl-general-condensed-weil-realization). -/
abbrev Source := sfWeilComplex D l hl Y₀ (PointRealizationComparison.FieldModel.{u} l E)

/-- Compact coefficient complexes, descended through the recorded up/down equivalence.
Source: the realization statement, RΓ_c
(blueprint: lem-zl-general-condensed-weil-realization). -/
def compactComplex (c₀ : Compactification Y₀.hom) :=
  sfWeilForget D l hl Y₀ (PointRealizationComparison.FieldModel.{u} l E) ⋙
    frobeniusCohomologyRationalFunctor D l hl
      (PointRealizationComparison.FieldModel.{u} l E) Y₀ c₀ true ⋙
        (PointRealizationComparison.fdEquivalence.{u} l E).inverse

/-- The recorded compact geometric Frobenius transported through that same equivalence.
Source: the realization statement, F
(blueprint: lem-zl-general-condensed-weil-realization). -/
def compactFrobenius (c₀ : Compactification Y₀.hom) (K : Source D l hl E Y₀) :
    End ((compactComplex D l hl E Y₀ c₀).obj K) :=
  (PointRealizationComparison.fdEquivalence.{u} l E).inverse.map
    (globalGeometricFrobeniusForField D l hl
      (PointRealizationComparison.FieldModel.{u} l E) Y₀ c₀ K).2

/-- Stalk coefficient complexes at the actual geometric point z.
Source: the realization statement, K_(E,z)
(blueprint: lem-zl-general-condensed-weil-realization). -/
def stalkComplex (z : RationalPoint (D.geometricFiber Y₀)) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  sfWeilForget D l hl Y₀ (PointRealizationComparison.FieldModel.{u} l E) ⋙
    rationalDerivedPullback l (PointRealizationComparison.FieldModel.{u} l E) z.left ⋙
      PointRealizationComparison.fibre D l hl E

/-- Specialize the recorded model-characteristic theorem to Spec(k) and transport
its global-section equality through the canonical spectrum/sections isomorphism.
Source: finite-field datum, realization proof step 1
(blueprint: lem-zl-general-condensed-weil-realization). -/
abbrev characteristic (D : FiniteFieldDatum.{u}) : ringChar D.k = D.p :=
  CharP.ringChar_of_prime_eq_zero D.prime
    ((map_natCast (Scheme.ΓSpecIso (.of D.k)).hom.hom D.p).symm.trans
      ((congrArg (Scheme.ΓSpecIso (.of D.k)).hom.hom
        (D.model_characteristic
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).trans (map_zero _)))

/-- The inherited prime characteristic, with no new hypothesis on the datum.
Source: realization proof step 1 (blueprint: lem-zl-general-condensed-weil-realization). -/
instance characteristicPrime : Fact (ringChar D.k).Prime :=
  ⟨(congrArg Nat.Prime (characteristic D)).mpr D.prime⟩

/-- The inherited prime-to-l characteristic, with no new hypothesis on the datum.
Source: realization proof step 1 (blueprint: lem-zl-general-condensed-weil-realization). -/
abbrev characteristicDifferent : Fact (ringChar D.k ≠ l) :=
  ⟨(congrArg (fun p : ℕ ↦ p ≠ l) (characteristic D)).mpr (Ne.symm hl)⟩

section Condensed

variable [Fact (ringChar D.k).Prime] [Fact (ringChar D.k ≠ l)]

/-- The target is the published internal-module Weil category for the model Frobenius.
Source: the realization statement, (K_Ω,phi_Ω)
(blueprint: lem-zl-general-condensed-weil-realization). -/
abbrev Target := WeilBoundedConstructibleOfEnd l (modelFrobenius D Y₀)

/-- The simultaneous functorial realization, specified object comparisons, operator
identities, fixed-point indexing, and right duals. The matrix functor is the single
finite-matrix realization supplied by the dependency, shared by all clauses.
Source: the entire realization statement
(blueprint: lem-zl-general-condensed-weil-realization). -/
structure Data (c₀ : Compactification Y₀.hom)
    (A : CondensedPointSupertraceData D.k l E) where
  realization : Source D l hl E Y₀ ⥤ Target D l Y₀
  [finite : ∀ n : ℕ, IsFinite (frobeniusIterate (modelFrobenius D Y₀) n).left]
  [universal : ∀ n : ℕ,
    IsUniversalHomeomorphism (frobeniusIterate (modelFrobenius D Y₀) n).left]
  compactComparison :
    realization ⋙ CategoryTheory.Endofunctor.IsoAlgebra.forget _ ⋙
      boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj l) l
        (toPoint (D.geometricFiber Y₀)) ≅
      compactComplex D l hl E Y₀ c₀ ⋙ A.realization.rho
  stalkComparison : ∀ z : RationalPoint (D.geometricFiber Y₀),
    realization ⋙ CategoryTheory.Endofunctor.IsoAlgebra.forget _ ⋙
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l z ≅
      stalkComplex D l hl E Y₀ z ⋙ A.realization.rho
  global_intertwines : ∀ (K : Source D l hl E Y₀) (n : ℕ), 1 ≤ n →
    (realization.obj K).globalOperator n ≫ compactComparison.hom.app K =
      compactComparison.hom.app K ≫
        A.realization.rho.map (compactFrobenius D l hl E Y₀ c₀ K ^ n)
  fixedIndex : ∀ (n : ℕ) (hn : 1 ≤ n),
    D.extensionPoints Y₀ n hn ≃ FixedPoint (modelFrobenius D Y₀) n
  fixedIndex_point : ∀ (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn),
    ((fixedIndex n hn x).val).left = localExtensionPoint D Y₀ n hn x
  fixed_finite : ∀ (n : ℕ), 1 ≤ n → Finite (FixedPoint (modelFrobenius D Y₀) n)
  local_intertwines : ∀ (K : Source D l hl E Y₀) (n : ℕ) (hn : 1 ≤ n)
    (x : D.extensionPoints Y₀ n hn) (e : D.extensionSubfield n hn →+* D.k),
    e.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k →
    ∀ z : RationalPoint (D.geometricFiber Y₀),
      z.left ≫ pullback.fst Y₀.hom
          (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom e) ≫ x.left →
      ∃ (hfix : z ≫ frobeniusIterate (modelFrobenius D Y₀) n = z)
        (hreturn : z.left ≫ localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
          localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z.left),
        (realization.obj K).stalkFrobenius n z hfix ≫ (stalkComparison z).hom.app K =
          (stalkComparison z).hom.app K ≫ A.realization.rho.map
            ((PointRealizationComparison.fdEquivalence.{u} l E).inverse.map
              (localFrobeniusOperator l (PointRealizationComparison.FieldModel.{u} l E)
                D hl Y₀ K z.left (n - 1) hreturn))
  compact_dual : ∀ K : Source D l hl E Y₀,
    HasRightDual ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj l) l
      (toPoint (D.geometricFiber Y₀))).obj (realization.obj K).carrier)
  stalk_dual : ∀ (K : Source D l hl E Y₀) (z : RationalPoint (D.geometricFiber Y₀)),
    HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l z).obj
      (realization.obj K).carrier)

end Condensed

/-- Every finite-stage Weil complex admits the simultaneous condensed realization.
Source: main-20261015, prop-every-iterate-trace.proof.md, coefficient/operator
comparison prerequisite (blueprint: lem-zl-general-condensed-weil-realization).

Proof:
1. The geometric fibre is noetherian and finite-dimensional, and l is invertible.
   Take the integral representative of the raw rationalization. The stratified-perfect
   characterization identifies its integral category with the domain of J. The chosen
   compactification and its base change give the compact-support presentations.
2. Its reductions have finite Tor amplitude: tensor each bounded finite-projective
   stratum model with the quotient and take the bounds over finitely many strata.
   Write the rational Weil isomorphism as t^(-N)u by the rational-model theorem;
   no invertible integral Weil structure is required.
3. The scheme/Galois comparisons come from the relative-Frobenius site isomorphism
   on the whole quotient diagram. Coefficient coherence and integral pullback
   realization identify the limit comparisons and their multiplicative compositors.
   Thus w_r=t^(-Nr)u^[r]kappa_r is the r-th iterate of w_1.
4. Compose J with the actual finite-extension-valued condensed scalar extension.
   Pullback compatibility is tensor reassociation b tensor (e tensor m) ↦ be tensor m;
   three-factor reassociation gives its unit and composition coherence.
5. Apply this functor to w_1 to give the model-Frobenius Weil structure. Naturality
   of kappa gives functoriality on Weil arrows; its construction is independent
   of the denominator used to represent the rational arrow.
6. The compact-support realization and the normalized point-coefficient comparison
   give compactComparison. Pullback at each actual k-point and the same normalized
   comparison give stalkComparison. Their source coefficient complexes are bounded
   finite-dimensional by the recorded compact and point-fibre interfaces.
7. The Frobenius fixed-point theorem gives fixedIndex using the fixed inclusion.
   Every other k0-embedding also has image killed by q^n-power minus identity,
   so its lift is fixed and satisfies the geometric/Galois return equation.
   Changing embeddings can permute fixedIndex; it does not identify distinct lifts.
8. Scheme Frobenius and its iterates are finite universal homeomorphisms. The
   model compact-unit comparison identifies the published globalOperator with
   the proper-unit composite; no trace formula is used.
9. Proper-unit condensed realization and its naturality on whole towers identify
   that composite with the finite graph operators, hence with t^(-Nr)U_r.
   Individual reduction functors are not used as faithful tests of arrows.
10. Integral compact-transport recurrence and naturality give U_(r+1)=U_1 U_r.
    Its one-step normalization is the specified geometric Frobenius F, hence the
    rational composite is F^r. This proves global_intertwines.
11. Local transport normalization identifies the specified iterated point transport
    and composition comparison with kappa_r followed by the fixed-point comparison.
    It uses the actual chosen lift, so it applies to every allowed embedding.
12. Pullback composition coherence and naturality of the point comparison send
    the published stalkFrobenius to precisely localFrobeniusOperator, proving
    local_intertwines. Finite matrix realization extends each operator entry by
    the specified inclusion E→Omega, including on cohomology.
13. The condensed point supertrace dependency supplies right duals of finite matrix
    realizations and every isomorphic object. Transport them across the two
    comparison isomorphisms. This uses its realization/duality conclusions only.
-/
theorem general_condensed_weil_realization (c₀ : Compactification Y₀.hom) :
    ∃ A : CondensedPointSupertraceData D.k l E, Nonempty
      (@Data D l _ hl E Y₀ _ _ _ (characteristicPrime D)
        (characteristicDifferent D l hl) c₀ A) := by
  sorry

end WeilConjectures.GeneralCondensedWeil
