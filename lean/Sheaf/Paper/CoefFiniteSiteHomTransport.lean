/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q128
-/
module

public import Sheaf.Paper.CoefFiniteHomSiteDescent
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteCoefficientHomChange
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Transport of finite coefficient target families and their Hom maps

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-tower,
cor-coef-finite-verdier.proof.md, evaluation, double-dual and quotient-cocycle sentences
(blueprint: lem-coef-finite-site-hom-transport).

An index n denotes exponent n+1. Fin (N+1) therefore indexes exactly the nonempty
finite range of positive levels 1,...,N+1. The two symmetry witnesses in the conclusion
are pinned to the existing signed total tensors; they are not extra input hypotheses.
All scalar, site and Hom maps below are the published canonical maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a b va vb
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- The canonical etale identity-quotient unit, not an identity chosen on objects.
Source: blueprint quotient-unit convention
(blueprint: lem-coef-finite-site-hom-transport). -/
def coefFiniteSiteEtaleUnit (n : ℕ) :
    finiteHomEtaleReduction l E X (Nat.le_refl n) ≅ 𝟭 _ :=
  ProEtale.normalizedOriginScalarUnit X.smallEtaleTopology
    (finiteHomQuotient l E (Nat.le_refl n))
    (congrArg RingHom.ulift (Ideal.Quotient.factor_eq
      (S := Padic.coefficientExtensionIdeal l E (n + 1))))

/-- The prescribed transported target transition: chi inverse followed by F(u).
Source: blueprint transported quotient cocycle
(blueprint: lem-coef-finite-site-hom-transport). -/
def coefFiniteSiteTargetMap {n m : ℕ} (h : m ≤ n)
    {W : finiteHomEtale l E X n} {V : finiteHomEtale l E X m}
    (f : (finiteHomEtaleReduction l E X h).obj W ⟶ V) :
    (coefficientFiniteQuotientDerived l E X h).obj ((finiteHomNu l E X n).obj W) ⟶
      (finiteHomNu l E X m).obj V :=
  (coefFiniteHomSiteIso l E X h).inv.app W ≫ (finiteHomNu l E X m).map f

/-- Etale h is quotient Hom comparison followed by changing its second argument.
Source: blueprint finite coefficient Hom comparison with transported target
(blueprint: lem-coef-finite-site-hom-transport). -/
def coefFiniteSiteEtaleHom {n m : ℕ} (h : m ≤ n)
    (K W : finiteHomEtale l E X n) (V : finiteHomEtale l E X m)
    (f : (finiteHomEtaleReduction l E X h).obj W ⟶ V) :=
  etaleFiniteHomCanonical l E X h K W ≫
    (finiteHomEtaleInternalHom l E X m).map
      (Prod.mkHom (𝟙 (op ((finiteHomEtaleReduction l E X h).obj K))) f)

/-- Pro-etale h uses precisely the transported target map and quotient transpose.
Source: blueprint finite coefficient Hom comparison with transported target
(blueprint: lem-coef-finite-site-hom-transport). -/
def coefFiniteSiteProHom {n m : ℕ} (h : m ≤ n)
    (K W : normalizedDVRDerived l E X n) (V : normalizedDVRDerived l E X m)
    (f : (coefficientFiniteQuotientDerived l E X h).obj W ⟶ V) :=
  proEtaleFiniteHomCanonical l E X h K W ≫
    (coefficientFiniteInternalHom l E X m).map
      (Prod.mkHom (𝟙 (op ((coefficientFiniteQuotientDerived l E X h).obj K))) f)

/-- Evaluation and signed-evaluation transposes commute with the specified comparison.
This predicate writes delta as its defining transpose, for an arbitrary target W.
Source: blueprint evaluation and double-dual sentences
(blueprint: lem-coef-finite-site-hom-transport). -/
def CoefFiniteSitePairingTransport
    {A : Type a} {B : Type b} [Category.{va} A] [Category.{vb} B]
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (SA : CoefficientClosedStructure HA) (SB : CoefficientClosedStructure HB)
    (sA : @SymmetricCategory A _ SA.monoidal)
    (sB : @SymmetricCategory B _ SB.monoidal)
    (F : A ⥤ B) (μ : SA.tensor ⋙ F ≅ F.prod F ⋙ SB.tensor) (T W : A) : Prop :=
  SB.tensor.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ T W) (𝟙 (F.obj T))) ≫
      SB.evaluation (F.obj T) (F.obj W) =
    μ.inv.app (HA.obj (op T, W), T) ≫ F.map (SA.evaluation T W) ∧
  F.map (SA.transpose T (HA.obj (op T, W)) W
      ((sA.toBraidedCategory.braiding T (HA.obj (op T, W))).hom ≫ SA.evaluation T W)) ≫
      coefficientBaseChangeHom SA SB F μ (HA.obj (op T, W)) W =
    SB.transpose (F.obj T) (HB.obj (op (F.obj T), F.obj W)) (F.obj W)
      ((sB.toBraidedCategory.braiding (F.obj T)
        (HB.obj (op (F.obj T), F.obj W))).hom ≫ SB.evaluation (F.obj T) (F.obj W)) ≫
      HB.map (Prod.mkHom (coefficientBaseChangeHom SA SB F μ T W).op (𝟙 (F.obj W)))

/-- The target-dependent scalar/site square, with chi in the contravariant input.
Source: blueprint 'the two comparisons already proved'
(blueprint: lem-coef-finite-site-hom-transport). -/
def CoefFiniteSiteTargetSquare {n m : ℕ} (h : m ≤ n)
    (K W : finiteHomEtale l E X n) (V : finiteHomEtale l E X m)
    (f : (finiteHomEtaleReduction l E X h).obj W ⟶ V) : Prop :=
  (finiteHomNu l E X m).map (coefFiniteSiteEtaleHom l E X h K W V f) ≫
      finiteHomSiteHom l E X m ((finiteHomEtaleReduction l E X h).obj K) V =
    (coefFiniteHomSiteIso l E X h).hom.app
        ((finiteHomEtaleInternalHom l E X n).obj (op K, W)) ≫
      (coefficientFiniteQuotientDerived l E X h).map (finiteHomSiteHom l E X n K W) ≫
      coefFiniteSiteProHom l E X h ((finiteHomNu l E X n).obj K)
        ((finiteHomNu l E X n).obj W) ((finiteHomNu l E X m).obj V)
        (coefFiniteSiteTargetMap l E X h f) ≫
      (coefficientFiniteInternalHom l E X m).map
        (Prod.mkHom ((coefFiniteHomSiteIso l E X h).hom.app K).op
          (𝟙 ((finiteHomNu l E X m).obj V)))

/-- All three transport clauses, keeping the given finite family and its actual maps.
Tor intervals [a,b] are ordered (a ≤ b), as in the intrinsic pro-etale predicate.
The existential symmetries merely specify the signed symmetries already used by the
closed derived tensors: Koszul on etale complexes and the signed representative model
on intrinsic pro-etale complexes. Source: blueprint finite pro-etale realization
(blueprint: lem-coef-finite-site-hom-transport). -/
def CoefFiniteSiteTargetTransport (N : ℕ)
    (Ω : ∀ i : Fin (N + 1), finiteHomEtale l E X i.val)
    (uΩ : ∀ (i j : Fin (N + 1)) (h : j.val ≤ i.val),
      (finiteHomEtaleReduction l E X h).obj (Ω i) ≅ Ω j) : Prop :=
  (∀ j : Fin (N + 1),
    finiteTorConstructible l E (j.val + 1) (Nat.succ_pos j.val) X
      ((finiteHomNu l E X j.val).obj (Ω j)) ∧
    ∀ a b : ℤ, a ≤ b → Etale.DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (j.val + 1))) X a b (Ω j) →
      HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (j.val + 1))
        ((finiteHomNu l E X j.val).obj (Ω j)) a b) ∧
  (∀ (i j : Fin (N + 1)) (h : j.val ≤ i.val),
    IsIso (coefFiniteSiteTargetMap l E X h (uΩ i j h).hom)) ∧
  (∀ i : Fin (N + 1),
    coefFiniteSiteTargetMap l E X (Nat.le_refl i.val) (uΩ i i (Nat.le_refl i.val)).hom =
      (coefFiniteHomProUnit l E X i.val).hom.app ((finiteHomNu l E X i.val).obj (Ω i))) ∧
  (∀ (i j r : Fin (N + 1)) (h : j.val ≤ i.val) (k : r.val ≤ j.val),
    (finiteHomIntrinsicAssoc l E X h k).hom.app ((finiteHomNu l E X i.val).obj (Ω i)) ≫
        coefFiniteSiteTargetMap l E X (k.trans h) (uΩ i r (k.trans h)).hom =
      (coefficientFiniteQuotientDerived l E X k).map
          (coefFiniteSiteTargetMap l E X h (uΩ i j h).hom) ≫
        coefFiniteSiteTargetMap l E X k (uΩ j r k).hom) ∧
  (∀ (i j : Fin (N + 1)) (h : j.val ≤ i.val) (K : finiteHomEtale l E X i.val),
    finiteTorConstructibleEtale l E (i.val + 1) (Nat.succ_pos i.val) X K →
      CoefFiniteSiteTargetSquare l E X h K (Ω i) (Ω j) (uΩ i j h).hom) ∧
  ∃ βet : ∀ j : Fin (N + 1), @SymmetricCategory (finiteHomEtale l E X j.val) _
      (finiteHomEtaleClosed l E X j.val).monoidal,
    ∃ βpro : ∀ j : Fin (N + 1), @SymmetricCategory (normalizedDVRDerived l E X j.val) _
        (finiteIntrinsicClosed l E X j.val).monoidal,
      (∀ (j : Fin (N + 1)) (P Q : finiteHomEtale l E X j.val),
        HEq ((βet j).toBraidedCategory.braiding P Q)
          (finiteHomKoszulIso (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
            (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (j.val + 1))))) P Q)) ∧
      (∀ j : Fin (N + 1), Nonempty (RingedDerivedTensorCoherence
        (ProEt.topology X) (integralCoefficientCommRingSheaf l E X j.val)
        (finiteIntrinsicClosed l E X j.val) (finiteIntrinsicTensorModels l E X j.val)
        (βpro j))) ∧
      ∀ (j : Fin (N + 1)) (T : finiteHomEtale l E X j.val),
        finiteTorConstructibleEtale l E (j.val + 1) (Nat.succ_pos j.val) X T →
          CoefFiniteSitePairingTransport (finiteHomEtaleClosed l E X j.val)
            (finiteIntrinsicClosed l E X j.val) (βet j) (βpro j)
            (finiteHomNu l E X j.val) (finiteHomNuTensor l E X j.val) T (Ω j)

/-- Site pullback transports the supplied coefficient-compatible targets, their quotient
Hom maps, evaluations and signed double-dual maps. Source: blueprint main-20261015,
cor-coef-finite-verdier.proof.md, finite pro-etale realization
(blueprint: lem-coef-finite-site-hom-transport).

Proof, following the node's six steps:
1. Apply lem-coef-finite-hom-site-descent at each level to preserve bounded
constructibility and every Tor interval. Its linear scalar/site isomorphism chi and
functoriality make chi inverse followed by F(u) invertible.
2. For i >= j >= r, use successive-quotient coherence of chi and its naturality at u.
Substitution reduces the transported cocycle to the given etale cocycle. The identity
case of the same coherence, with the scalar units, makes chi the unit identification;
together with the given identity equation this proves the pro-etale identity equation.
3. Untranspose beta naturality in the second Hom input. Both composites are F(u)
after pulled-back evaluation; injectivity of the closed adjunction gives equality
(def-sf-evaluation-hom-site-comparison, lem-sf-ringed-derived-closed-symmetric-monoidal).
4. Apply the square of lem-coef-finite-hom-site-descent to (K,Omega_i), then postcompose
with Hom(chi_K,u_pro). Bifunctoriality cancels chi_K inverse and substitutes
u_pro chi_Omega = F(u). Step 3 identifies the result with the etale h route.
The comparison maps are those of thm-coef-finite-hom; no invertibility of v is needed.
5. Untransposing beta gives the evaluation equation directly. At the first dual its
comparison is still defined: thm-coef-finite-hom with the identity quotient puts that
dual in the finite-Tor constructible domain, under the scalar unit.
6. Untranspose both double-dual composites. Naturality of the canonical tensor
comparison moves F(delta) through tensor; compatibility with the signed symmetry
identifies the first untranspose with F(evaluation) after signed interchange. Evaluation
naturality and step 5 give the same expression for the second. Injectivity of the
adjunction proves equality. The signed monoidal comparisons are those of
lem-sfb-ringed-derived-monoidal-comparisons and lem-sf-comparison-pullback-exact.
No invertibility of the double-dual map or exceptional adjoint is asserted. -/
theorem coefFiniteSiteHomTransport
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    (N : ℕ) (Ω : ∀ i : Fin (N + 1), finiteHomEtale l E X i.val)
    (uΩ : ∀ (i j : Fin (N + 1)) (h : j.val ≤ i.val),
      (finiteHomEtaleReduction l E X h).obj (Ω i) ≅ Ω j)
    (_hΩ : ∀ i : Fin (N + 1),
      finiteTorConstructibleEtale l E (i.val + 1) (Nat.succ_pos i.val) X (Ω i))
    (_hunit : ∀ i : Fin (N + 1), (uΩ i i (Nat.le_refl i.val)).hom =
      (coefFiniteSiteEtaleUnit l E X i.val).hom.app (Ω i))
    (_hcocycle : ∀ (i j r : Fin (N + 1)) (h : j.val ≤ i.val) (k : r.val ≤ j.val),
      (finiteHomEtaleAssoc l E X h k).hom.app (Ω i) ≫
          (uΩ i r (k.trans h)).hom =
        (finiteHomEtaleReduction l E X k).map (uΩ i j h).hom ≫ (uΩ j r k).hom) :
    CoefFiniteSiteTargetTransport l E X N Ω uΩ := by
  sorry

end WeilConjectures
