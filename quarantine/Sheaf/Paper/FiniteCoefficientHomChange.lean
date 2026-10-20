/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.FiniteCoefficientSiteHomArrow
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.FiniteConstructibleHom
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.FiniteFieldFiber
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.Etale.Derived.Hom
import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import Sheaf.Paper.FiniteTorAmplitudeSites

import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Paper.FiniteCoefficientFlatModel
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.Algebra.Homology.HomTensorTotal
import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
import Sheaf.SixFunctors.EtaleHomThickLocus
import Sheaf.SixFunctors.FlatModelGeneration
import Sheaf.CategoryTheory.DerivedCategory.BoundedFiniteTorPerfect
import Sheaf.Paper.OpenComplementUnconditional
import Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude
import Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Paper.CoefficientRingedTensorHomModel
import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
import Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Sheaf.Paper.EtaleLocallyClosedShriek
import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
import Sheaf.Paper.FiniteCoefficientDirectImage
import Sheaf.SixFunctors.EtaleOpenTensor
import Sheaf.AlgebraicGeometry.ProperProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.Paper.InternalAdjunctionPairingChange
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ComparisonTorAmplitude
import Sheaf.SixFunctors.CoefMonoidalSquareHomTransport
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.SixFunctors.FiniteDualitySiteComparison

/-! # Finite coefficient change for internal Hom

Source: blueprint sec-six-functors/sk-prop-sf-biduality-general,
node thm-coef-finite-hom (blueprint: thm-coef-finite-hom).
Indices n and m below denote exponents n + 1 and m + 1; thus every positive
exponent, including the identity quotient, occurs. All comparison maps are
closed transposes of reduced evaluation, never choices of arbitrary arrows.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u a b w c d e f g
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Evaluation identity and uniqueness of its transpose, for the actual base-change arrow.
Source: blueprint evaluation paragraph (blueprint: thm-coef-finite-hom). -/
def FiniteHomEvaluation
    {A : Type a} {B : Type a} [Category.{b} A] [Category.{b} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) : Prop :=
  ∀ K M : A,
    SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ K M) (𝟙 (F.obj K))) ≫
        SB.evaluation (F.obj K) (F.obj M) =
      μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) ∧
    ∀ v : F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M),
      SB.tensor.map (Prod.mkHom v (𝟙 (F.obj K))) ≫
          SB.evaluation (F.obj K) (F.obj M) =
        μ.inv.app (HA.obj (op K, M), K) ≫ F.map (SA.evaluation K M) →
      v = coefficientBaseChangeHom SA SB F μ K M

/-- Coherence under composition of coefficient functors, with all three canonical arrows.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomQuotientCocycleAux
    {A B C : Type a} [Category.{b} A] [Category.{b} B] [Category.{b} C]
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B) (HC : Cᵒᵖ × C ⥤ C)
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C) (α : F ⋙ G ≅ J)
    (v : ∀ K M : A, F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
    (w : ∀ K M : B, G.obj (HB.obj (op K, M)) ⟶ HC.obj (op (G.obj K), G.obj M))
    (z : ∀ K M : A, J.obj (HA.obj (op K, M)) ⟶ HC.obj (op (J.obj K), J.obj M)) : Prop :=
  ∀ K M : A, α.hom.app (HA.obj (op K, M)) ≫ z K M =
    G.map (v K M) ≫ w (F.obj K) (F.obj M) ≫
      HC.map (Prod.mkHom (α.inv.app K).op (α.hom.app M))

/-- The intrinsic quotient cocycle, including both input associators and the Hom associator.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
structure FiniteHomIntrinsicCocycle {n m : ℕ} (h : m ≤ n) : Prop where
  coherence : ∀ (r : ℕ) (k : r ≤ m), FiniteHomQuotientCocycleAux
    (coefficientFiniteInternalHom l E X n) (coefficientFiniteInternalHom l E X m)
    (coefficientFiniteInternalHom l E X r)
    (coefficientFiniteQuotientDerived l E X h) (coefficientFiniteQuotientDerived l E X k)
    (coefficientFiniteQuotientDerived l E X (k.trans h)) (finiteHomIntrinsicAssoc l E X h k)
    (proEtaleFiniteHomCanonical l E X h) (proEtaleFiniteHomCanonical l E X k)
    (proEtaleFiniteHomCanonical l E X (k.trans h))

/-- The cocycle for canonical transposes, with the quotient diagram's data shared.
Source: blueprint A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomQuotientClosedData.Cocycle
    {C : ℕ → Type a} [∀ n : ℕ, Category.{b} (C n)]
    {H : ∀ n : ℕ, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m : ℕ}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (α : ∀ {n m r : ℕ} (h : m ≤ n) (k : r ≤ m), F h ⋙ F k ≅ F (k.trans h))
    {n m : ℕ} (h : m ≤ n) : Prop :=
  ∀ (r : ℕ) (k : r ≤ m), FiniteHomQuotientCocycleAux (H n) (H m) (H r)
    (F h) (F k) (F (k.trans h)) (α h k)
    (S.comparison h) (S.comparison k) (S.comparison (k.trans h))

/-- The etale quotient cocycle with the canonical input identifications.
Source: blueprint displayed A to B to C equation (blueprint: thm-coef-finite-hom). -/
def FiniteHomEtaleCocycle {n m : ℕ} (h : m ≤ n) : Prop :=
  (finiteHomEtaleData l E X).Cocycle (finiteHomEtaleAssoc l E X) h

/-- The coefficient-change square under site comparison, expressed with shared functors.
Source: blueprint final site-comparison sentence (blueprint: thm-coef-finite-hom). -/
def FiniteHomSiteSquareAux
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{e} A] [Category.{f} B] [Category.{g} C] [Category.{w} D]
    (HA : Aᵒᵖ × A ⥤ A) (HB : Bᵒᵖ × B ⥤ B)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (F : A ⥤ B) (G : C ⥤ D) (U : A ⥤ C) (V : B ⥤ D)
    (β : U ⋙ G ⟶ F ⋙ V) [IsIso β]
    (v : ∀ K M : A, F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M))
    (w : ∀ K M : C, G.obj (HC.obj (op K, M)) ⟶ HD.obj (op (G.obj K), G.obj M))
    (s : ∀ K M : A, U.obj (HA.obj (op K, M)) ⟶ HC.obj (op (U.obj K), U.obj M))
    (t : ∀ K M : B, V.obj (HB.obj (op K, M)) ⟶ HD.obj (op (V.obj K), V.obj M)) : Prop :=
  ∀ K M : A, β.app (HA.obj (op K, M)) ≫ V.map (v K M) ≫ t (F.obj K) (F.obj M) =
    G.map (s K M) ≫ w (U.obj K) (U.obj M) ≫
      HD.map (Prod.mkHom (inv (β.app K)).op (β.app M))

/-- The beta/nu_X^* square for the two evaluation-defined finite comparisons.
The inverse beta in the contravariant input is essential.
Source: blueprint final site-comparison sentence (blueprint: thm-coef-finite-hom). -/
structure FiniteHomSiteFormula {n m : ℕ} (h : m ≤ n) : Prop where
  square : FiniteHomSiteSquareAux (finiteHomEtaleInternalHom l E X n)
    (finiteHomEtaleInternalHom l E X m)
    (coefficientFiniteInternalHom l E X n) (coefficientFiniteInternalHom l E X m)
    (finiteHomEtaleReduction l E X h) (coefficientFiniteQuotientDerived l E X h)
    (finiteHomNu l E X n) (finiteHomNu l E X m) (finiteHomSiteBeta l E X h)
    (etaleFiniteHomCanonical l E X h) (proEtaleFiniteHomCanonical l E X h)
    (finiteHomSiteHom l E X n) (finiteHomSiteHom l E X m)

/-- Finite coefficient change for internal Hom, including the canonical-map equations.
Source: blueprint thm-coef-finite-hom, evaluation and coefficient-change paragraphs
(blueprint: thm-coef-finite-hom).

Proof:
1. A finite-type scheme over k is Noetherian. Derived scalar extension is computed
on K-flat resolutions, even for a nonflat quotient. A bounded flat constructible
model reduces to a bounded flat constructible model with the same Tor interval.
2. Resolve tensor inputs K-flat and the Hom target K-injective. The total-complex
Hom-tensor identity gives the closed adjunction. Transpose reduced evaluation;
this is exactly coefficientBaseChangeHom and finiteIntrinsicReductionHom.
Finite constructible Hom and scalar reduction put both endpoints in D^b_ctf.
3. For fixed M the invertibility locus in K is thick, by the evaluation-normalized
shift and connecting-map comparison. The flat-model generation theorem supplies
locally closed generators Rs_!L = g_*j_!L with L finite locally projective. On an
etale cover L is finite free, including rank zero, so the bounded-free Hom model
identifies its comparison with the identity on finite sums of the reduced model.
For N = Rs^!M = j^*Rg^!M, the general quasi-compact-open complement theorem
applies over the separably closed field, with l-primary finite coefficients and
finite dimension d. It gives constructibility and cohomological bound 2d on
all sheaves. The closed-exceptional Tor theorem then puts Rg^!M in the Tor
interval [a,b+2d+1]; open pullback preserves the resulting finite-Tor domain.
Finite constructible Hom therefore puts Q = H(L,N) in the required domain.
Locally closed shriek coefficient change supplies its counit-normalized
comparisons. Internal adjunction identifies the generator Hom with Rs_*Q;
finite direct-image coefficient change applies to Q. Compose this comparison,
the local finite-free Hom comparison, and the exceptional comparison. The
open projection formula and the proper projection formula for the closed factor
identify the resulting pairing with reduced evaluation, by their counit identities.
Uniqueness of transpose identifies this invertible composite with the specified v.
Thus v is invertible on every generator. Thick closure, followed by the finite
stupid-truncation triangles of a bounded flat model, proves the etale assertion.
4. The closed transpose bijection proves the evaluation identity and its
uniqueness. Transposing after arbitrary input maps gives naturality; applying it
to an arbitrary tensor-Hom transpose gives the adjunction equation. Uncurry
internal composition to its two evaluations to obtain the composition equation.
5. On three quotient levels the canonical tensor associators identify the two
reduced evaluations. Their unique transposes agree. This gives precisely both
cocycle equations, including the contravariant inverse input associator.
6. Exact comparison nu_X^* commutes with scalar extension by the specified beta
mate and with tensor by its pure-tensor comparison. Applying it to evaluation
and transposing gives FiniteHomSiteFormula. The finite-duality site comparison
identifies internal Hom on finite-Tor constructible etale origins, and every
intrinsic constructible complex has such an origin. This transfers invertibility
and constructibility to the pro-etale site. Evaluation, transpose, naturality,
composition and quotient coherence are the same identities before site transport. -/
theorem finiteCoefficient_derivedHom_change
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (n m : ℕ) (h : m ≤ n) :
    CoefficientEvaluationCompatible
      (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    FiniteHomEvaluation (finiteHomEtaleClosed l E X n) (finiteHomEtaleClosed l E X m)
      (finiteHomEtaleReduction l E X h) (finiteHomEtaleTensor l E X h) ∧
    (∀ K M : finiteHomEtale l E X n,
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructibleEtale l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((finiteHomEtaleReduction l E X h).obj
          ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X)).obj (op K, M))) ∧
      finiteTorConstructibleEtale l E (m + 1) (Nat.succ_pos m) X
        ((Functor.uncurry.obj (Etale.derivedHom (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (m + 1)))) X)).obj
          (op ((finiteHomEtaleReduction l E X h).obj K),
            (finiteHomEtaleReduction l E X h).obj M)) ∧
      IsIso (etaleFiniteHomCanonical l E X h K M)) ∧
    CoefficientEvaluationCompatible (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    FiniteHomEvaluation (finiteIntrinsicClosed l E X n) (finiteIntrinsicClosed l E X m)
      (coefficientFiniteQuotientDerived l E X h)
      ((coefficientDerivedSystemEvaluationCalculus l E X).choose.quotientCalculus.tensor h) ∧
    (∀ K M : normalizedDVRDerived l E X n,
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X K →
      finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X M →
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteQuotientDerived l E X h).obj
          ((coefficientFiniteInternalHom l E X n).obj (op K, M))) ∧
      finiteTorConstructible l E (m + 1) (Nat.succ_pos m) X
        ((coefficientFiniteInternalHom l E X m).obj
          (op ((coefficientFiniteQuotientDerived l E X h).obj K),
            (coefficientFiniteQuotientDerived l E X h).obj M)) ∧
      IsIso (proEtaleFiniteHomCanonical l E X h K M)) ∧
    FiniteHomEtaleCocycle l E X h ∧ FiniteHomIntrinsicCocycle l E X h ∧
    FiniteHomSiteFormula l E X h := by
  sorry

end WeilConjectures
