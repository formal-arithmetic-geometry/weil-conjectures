/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.SixFunctors.SelectedSchemeGaloisComparison
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntegralPullbackComposition
public import Sheaf.Paper.FrobeniusCoefficientReductionMap
public import Sheaf.Paper.FourCorners
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.PurInverseImageTensorHom
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.SixFunctors.SchemeFrobenius
import Sheaf.SixFunctors.SchemeGaloisCoefficientChange
/-!
# Frobenius pullback and coefficient reduction coherence

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).

Index n denotes exponent n+1. The quotient comparison is fixed by ordinary balancing;
the finite pullback comparison is the unit-normalized four-corners mate.
All integral reductions are over the completed coefficient sheaf.

## Main statements

* `frobeniusIntegralReduction_coherent`: quotient coherence of the integral comparison.
* `frobeniusIntegralReduction_natural`: naturality in the integral object.
* `frobeniusIntegralReduction_composition`: compatibility with integral composition.
* `frobeniusFiniteComposition_reduction`: composition and reduction at finite levels.
* `frobeniusSchemeGalois_reduction`: the canonical scheme--Galois quotient square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The published universal derived tensor along the actual quotient of finite rings.
Source: blueprint clause (2); Stacks 06YY
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
abbrev frobeniusReduction (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b) :
    proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (b + 1)) ⥤
      proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (a + 1)) :=
  reductionDerivedChange X (frobeniusReductionRingMap l E X b a h)

/-- Completion projections commute with every quotient arrow.
Source: blueprint clause (2); Stacks 03CO
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: the completed ring is the limit of the specified constant quotient sheaves.
Its cone naturality gives the equation for adjacent indices. Compose these equations
from a to b; quotient induction identifies their composite with the displayed quotient.
For equal indices both maps are identities. -/
theorem frobeniusReductionProjection (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b) :
    completedIntegralCommRingProjectionUnrestricted.{u, u} l E X b ≫
        frobeniusReductionRingMap l E X b a h =
      completedIntegralCommRingProjectionUnrestricted.{u, u} l E X a := by
  sorry

/-- The tower normalization is uniquely fixed by balancing on all K-flat computations.
Source: blueprint clause (2); Stacks 06YY and 03EK
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: use one K-flat resolution P. Its scalar extension to B_b is K-flat by
lem-pur-kflat-change-of-rings. Both successive tensors therefore compute derived
extension. The published reductionBalance multiplies the two coefficient factors,
with inverse inserting 1. Its naturality and cocycle descend through quasi-isomorphisms.
The universal derived counits give the equation below. Every object has a K-flat
resolution, so that equation uniquely determines the natural isomorphism. -/
theorem frobeniusReductionNormalization_existsUnique
    (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b) :
    ∃! η : scalarReductionDerivedExtension.{u, u} l E X b ⋙ frobeniusReduction l E X b a h ≅
        scalarReductionDerivedExtension.{u, u} l E X a,
      ∀ P : CochainComplex (scalarReductionSource.{u, u} l E X) ℤ,
        @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
            X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} X.ProEt)
            (ProEt.topology X) (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P →
        η.hom.app (DerivedCategory.Q.obj P) ≫
            reductionScalarComplexCounit X
              (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X a) P =
          (frobeniusReduction l E X b a h).map
              (reductionScalarComplexCounit X
                (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X b) P) ≫
            reductionScalarComplexCounit X (frobeniusReductionRingMap l E X b a h)
              ((reductionChangeComplex X
                (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X b)).obj P) ≫
            DerivedCategory.Q.map (reductionBalance X
              (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X b)
              (frobeniusReductionRingMap l E X b a h)
              (completedIntegralCommRingProjectionUnrestricted.{u, u} l E X a)
              (frobeniusReductionProjection l E X b a h) P) := by
  sorry

/-- The uniquely tensor-normalized tower identification, natural in every integral object.
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
def frobeniusReductionNormalization (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b) :
    scalarReductionDerivedExtension.{u, u} l E X b ⋙ frobeniusReduction l E X b a h ≅
      scalarReductionDerivedExtension.{u, u} l E X a :=
  (frobeniusReductionNormalization_existsUnique l E X b a h).exists.choose

/-- The canonical finite pullback/reduction comparison, specialized from the
unit-normalized four-corners mate.
Source: blueprint clause (2); def-weil-pbc-four-corners
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
noncomputable abbrev frobeniusFiniteReductionPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (b a : ℕ) (h : a ≤ b) :
    proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (b + 1)) f ⋙ frobeniusReduction l E X b a h ≅
      frobeniusReduction l E Y b a h ⋙ proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (a + 1)) f := by
  exact (AlgebraicGeometry.Scheme.proEtaleReductionPullbackIso f
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (b + 1)))
    (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (a + 1)))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (b + 1)))
    (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (a + 1)))
    (frobeniusReductionRingMap l E Y b a h)
    (frobeniusReductionRingMap l E X b a h)
    (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (b + 1)))
    (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (a + 1)))
    (by
      simpa [frobeniusReductionRingMap, flatModelReductionRingMap,
        proEtaleConstantRingComparison] using
        (proEtaleConstantInverseImageMap_naturality f
          (a := CommRingCat.ofHom
            (flatModelReductionCoefficientMap l E (a + 1) (b + 1)
              (Nat.add_le_add_right h 1)))).symm)).symm

/-- The finite comparison at an object, obtained from the four-corners isomorphism.
Source: blueprint clause (2); def-weil-pbc-four-corners
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
def frobeniusFiniteReductionComponent
    {X Y : Scheme.{u}} (f : X ⟶ Y) (b a : ℕ) (h : a ≤ b)
    (M : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (b + 1))) :
    (frobeniusReduction l E X b a h).obj
        ((proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (b + 1)) f).obj M) ≅
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (a + 1)) f).obj
          ((frobeniusReduction l E Y b a h).obj M) :=
  (frobeniusFiniteReductionPullback l E f b a h).app M

/-- The normalized tower identification at an object, with explicit scalar endpoints.
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
def frobeniusReductionNormalizationComponent
    (X : Scheme.{u}) (b a : ℕ) (h : a ≤ b)
    (M : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (frobeniusReduction l E X b a h).obj
        ((scalarReductionDerivedExtension.{u, u} l E X b).obj M) ≅
      (scalarReductionDerivedExtension.{u, u} l E X a).obj M :=
  (frobeniusReductionNormalization l E X b a h).app M

namespace FiniteFieldDatum

/-- The existing geometric-fibre invertibility construction, exposed as an instance.
The Fact binder is exactly ell not equal to p, rather than an extra geometric assumption.
Source: blueprint clause (2); finite-field coefficient convention
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
instance frobeniusCoherenceInvertible
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [Fact (l ≠ D.p)] :
    ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
  D.schemeFrobeniusCoefficientInvertible X₀ l Fact.out

/-- Every positive coefficient quotient is finite, by the recorded arithmetic theorem.
Source: blueprint coefficient convention; Serre, Local Fields II.2
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
instance frobeniusCoherenceCoefficientFinite (n : ℕ) :
    Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
  Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)

/-- The coefficient quotients satisfy the annihilator hypothesis of schemeGaloisComparison.
Source: blueprint clause (2), finite coefficient convention
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: in the valuation ring ell is a unit times a positive uniformizer power, because
its spectral absolute value is less than one. A sufficiently high power ell^N lies
in (varpi^(n+1)), so it annihilates the quotient. Since ell differs from p, ell^N
is nonzero in the characteristic-p field k and is a unit there. This also covers
ramified extensions, without claiming that n+1 is the ramification-adjusted exponent. -/
theorem frobeniusCoherenceAnnihilator
    (D : WeilConjectures.FiniteFieldDatum.{u}) [Fact (l ≠ D.p)] (n : ℕ) :
    ∃ N : ℕ, IsUnit (N : D.k) ∧
      ∀ x : Padic.coefficientExtensionRing l E (n + 1), N • x = 0 := by
  sorry

variable (D : WeilConjectures.FiniteFieldDatum.{u})
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]
  [Fact (l ≠ D.p)]

include hsep

/-- The integral comparison reduces coherently along every positive quotient.
All good representatives and all identifications are quantified, so no resolution
is additional data or a hypothesis. Index a denotes exponent a+1, and likewise for b.
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof:
1. Resolve K over the completed ring by one K-flat complex with flat terms
(lem-pc-kflat-resolution). Its simultaneous finite reductions are K-flat
(lem-pur-kflat-change-of-rings), and their normalization is the published balancing
map (def-weil-pbc-adic-coefficient-datum), represented by multiplying scalar factors.
2. A power of geometric Frobenius is an isomorphism. The sectionwise inverse-image
formula (lem-weil-proetale-isomorphism-inverse-image) and its tensor comparison
(lem-pur-isomorphism-inverse-image-tensor-hom) commute with quotient maps. Pullback
preserves flat-term K-flatness (lem-weil-pbc-ringed-pullback-preserves-kflat).
3. These maps give a strict normalized DVR tower. Its functorial derived limit is
integral pullback (def-pur-integral-derived-operations). Apply
lem-coef-normalized-dvr-effectivity: the canonical counits are isomorphisms and
commute with quotient transitions. They are the same projection-adjoint maps as
lem-pur-integral-operations-preserve-constructible. Transport through the finite
presentation comparison integralPullbackReductionIso. This gives the equation below.
4. lem-pur-integral-operations-well-defined descends the representative calculation,
including its actual maps, independently of the chosen good representative. -/
theorem frobeniusIntegralReduction_coherent
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj))
    (P : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (r : ℕ) (_hr : 1 ≤ r) (b a : ℕ) (h : a ≤ b) :
    (frobeniusReduction l E (D.geometricFiber X₀).left b a h).map
        (integralPullbackReductionIso l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) r) K P e b).hom ≫
      (frobeniusFiniteReductionComponent l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) b a h
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (a + 1))
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)).map
        ((frobeniusReductionNormalizationComponent l E (D.geometricFiber X₀).left b a h
        K.obj).hom) =
    (frobeniusReductionNormalizationComponent l E (D.geometricFiber X₀).left b a h
        (((constructibleIntegralPullback l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) r)).obj K).obj)).hom ≫
      (integralPullbackReductionIso l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) K P e a).hom := by
  sorry

/-- The same canonical reduction comparisons are natural in integral constructible K.
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: the functorial quotient tower and its projection maps are natural. Taking their
scalar-extension adjoints preserves naturality. The tensor and localization
comparisons in integralPullbackReductionIso are natural. Compose these squares;
lem-pur-integral-operations-well-defined makes them independent of both resolutions. -/
theorem frobeniusIntegralReduction_natural
    (K L : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj))
    (_hL : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj L.obj))
    (v : K ⟶ L)
    (P Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) (d : DerivedCategory.Q.obj Q.obj ≅ L.obj)
    (r : ℕ) (_hr : 1 ≤ r) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).map
        (((constructibleIntegralPullback l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) r)).map v).hom) ≫
      (integralPullbackReductionIso l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) L Q d n).hom =
    (integralPullbackReductionIso l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) K P e n).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)).map
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).map v.hom) := by
  sorry

omit hsep in
/-- The normalized integral composition comparison already supplied by the DAG.
Its finite-reduction equations determine the map on derived-complete objects, so this
selection retains the canonical comparison rather than an arbitrary isomorphism.
Source: blueprint clause (2); lem-pod-integral-pullback-composition
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence). -/
def frobeniusCoherenceIntegralComposition : IntegralPullbackCompositionFamily l E :=
  (integralPullbackComposition l E).choose

/-- Reduction intertwines composition along any two positive geometric-Frobenius powers.
The composite morphism is g^r followed by g^s, hence the (r+s)-th power.
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: specialize lem-pod-integral-pullback-composition to h=g^r and k=g^s.
Its specified reduction equation is exactly the displayed equation, with the finite
comparison of lem-weil-pbc-proetale-derived-pullback-composition. The canonical
rho maps are those identified in frobeniusIntegralReduction_coherent. -/
theorem frobeniusIntegralReduction_composition
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj))
    (r s : ℕ) (_hr : 1 ≤ r) (_hs : 1 ≤ s)
    (P Q : (integralOperationsGoodComplex l E (D.geometricFiber X₀).left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (d : DerivedCategory.Q.obj Q.obj ≅
      ((constructibleIntegralPullback l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) s)).obj K).obj) (n : ℕ) :
    (scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).map
        (((frobeniusCoherenceIntegralComposition l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) r)
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s)).hom.app K).hom) ≫
      (integralPullbackReductionIso l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)
        ((constructibleIntegralPullback l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s)).obj K) Q d n).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (n + 1))
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)).map
        (integralPullbackReductionIso l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s) K P e n).hom =
    (integralPullbackReductionIso l E
        ((HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) ≫
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s)) K P e n).hom ≫
      (integralFiniteCanonicalPullbackComposition l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) s) n).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj) := by
  sorry

/-- The specified scheme--Galois comparison commutes with every derived quotient.
Here kappa is the recorded `canonicalSchemeGaloisComparison` of
prop-trf-scheme-galois-comparison at the coefficient rings A_(b+1) and A_(a+1).
Source: blueprint clause (2)
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: on simultaneous K-flat reductions, factor kappa into the canonical pullback
composition and the absolute-Frobenius site trivialization, exactly as specified by
prop-trf-scheme-galois-comparison, lem-trf-absolute-frobenius-site and
prop-trf-frobenius-factorization. The site maps relabel sections and the scalar maps
multiply coefficients, so both paths send (x tensor u) tensor v to the same relabelled
x tensor q(u)v. They commute with the differentials and restrictions, descend through
sheafification, and then through localization. This is the coefficient-change square
of lem-trf-scheme-galois-coefficient-change, specialized to B_b to B_a, without flatness.
Postcompose it with pullback of the normalization eta. Naturality of kappa at eta gives
exactly the displayed square on K_b and K_a, for every m at least one. -/
theorem frobeniusSchemeGalois_reduction
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj))
    (m : ℕ) (hm : 1 ≤ m) (b a : ℕ) (h : a ≤ b) :
    (frobeniusReduction l E (D.geometricFiber X₀).left b a h).map
        ((D.canonicalSchemeGaloisComparison X₀ (Padic.coefficientExtensionRing l E (b + 1))
          (frobeniusCoherenceAnnihilator l E D b) m hm).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)) ≫
      (frobeniusFiniteReductionComponent l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m) b a h
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (a + 1))
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) m)).map
        ((frobeniusReductionNormalizationComponent l E (D.geometricFiber X₀).left b a h
        K.obj).hom) =
    (frobeniusFiniteReductionComponent l E (D.schemeFrobeniusIterate X₀ m) b a h
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (a + 1))
        (D.schemeFrobeniusIterate X₀ m)).map
        ((frobeniusReductionNormalizationComponent l E (D.geometricFiber X₀).left b a h
        K.obj).hom) ≫
      (D.canonicalSchemeGaloisComparison X₀ (Padic.coefficientExtensionRing l E (a + 1))
          (frobeniusCoherenceAnnihilator l E D a) m hm).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left a).obj K.obj) := by
  sorry


/-- The finite composition square also commutes with quotient reduction.
Source: blueprint clause (2), composition coherence
(blueprint: lem-trf-frobenius-coefficient-reduction-coherence).
Proof: use the sectionwise site formula for both geometric-Frobenius powers. The
canonical composition isomorphism relabels a section twice instead of once along
the composite. The quotient comparison multiplies its scalar factors. Either path
therefore sends (x tensor u) tensor v to the same twice-relabelled x tensor q(u)v.
These formulas commute with restrictions and differentials and survive localization
on simultaneous flat-term K-flat representatives. Together with the integral
composition equation this proves coherence with both reduction and composition. -/
theorem frobeniusFiniteComposition_reduction
    (K : sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left)
    (_hK : ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n)
      (D.geometricFiber X₀).left
      ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left n).obj K.obj))
    (r s : ℕ) (_hr : 1 ≤ r) (_hs : 1 ≤ s) (b a : ℕ) (h : a ≤ b) :
    (frobeniusReduction l E (D.geometricFiber X₀).left b a h).map
        ((integralFiniteCanonicalPullbackComposition l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) r)
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s) b).hom.app
          ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)) ≫
      (frobeniusFiniteReductionComponent l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) b a h
        ((proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (b + 1))
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s)).obj
          ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj
            K.obj))).hom ≫
      (proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E (a + 1))
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)).map
        ((frobeniusFiniteReductionComponent l E
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s) b a h
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj
          K.obj)).hom) =
    (frobeniusFiniteReductionComponent l E
        ((HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r) ≫
          (HPow.hPow (α := End (D.geometricFiber X₀).left)
            (D.geometricGaloisFrobenius X₀) s)) b a h
        ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj)).hom ≫
      (integralFiniteCanonicalPullbackComposition l E
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) r)
        (HPow.hPow (α := End (D.geometricFiber X₀).left)
          (D.geometricGaloisFrobenius X₀) s) a).hom.app
        ((frobeniusReduction l E (D.geometricFiber X₀).left b a h).obj
          ((scalarReductionDerivedExtension.{u, u} l E (D.geometricFiber X₀).left b).obj K.obj))
    := by
  sorry

end FiniteFieldDatum

end WeilConjectures
