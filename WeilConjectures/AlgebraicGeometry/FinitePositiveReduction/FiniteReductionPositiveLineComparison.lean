/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientReductionFlatModel
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.SmoothPurity.Supporting.TwistPreservesFiniteness
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule

/-! # Normalized finite reduction of native positive Tate lines

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2, coefficient twists and associativity.
(blueprint: lem-pur-finite-reduction-positive-line-comparison)

Indices `m,n` denote the positive exponents `m+1,n+1`. All coefficients are the
published discrete condensed quotient rings, pulled back to the small pro-etale site.
Normalization is expressed by the scalar adjunction: its transpose is the actual
semilinear root-power map and its tensor powers. This specifies the displayed
primitive-root rule without making a choice of root cover or basis.

## Main definitions and statement

- `quotient`, `roots`, `semilinear`: the coefficient quotient and root-normalized map.
- `reduction`, `Normalized`, `derivedMap`: derived scalar extension and its canonical arrow.
- `product`, `pull`, `scalarTensor`: the specific comparisons in the coherence squares.
- `finiteReduction_positiveLineComparison`: unique normalized isomorphisms and coherence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale.FinitePositiveReduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E] [Algebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

/-- The actual quotient of discrete condensed rings, including equal levels.
Source: Step 2, reduction A_n -> A_m
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def quotient (m n : ℕ) (hmn : m ≤ n) : twistFiniteRing ℓ E n ⟶ twistFiniteRing ℓ E m :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E (n + 1)) := ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E (m + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E (m + 1)) := ⟨rfl⟩
  twistContinuousMap
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn)))
    continuous_of_discreteTopology

variable (T : Scheme.{u})

/-- The published native positive line, with its regular coefficient unit in degree zero.
Source: def-coefficient-twists-detailed, nonnegative powers
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
abbrev line (n r : ℕ) :=
  coefficientTwistNat T (condensedRingObj (twistFiniteRing ℓ E n) T)
    (coefficientFiniteTwistOne ℓ E T n) r

/-- The actual root power mu_(ell^(n+1)) -> mu_(ell^(m+1)).
Source: Step 2, compatible primitive roots
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def roots (m n : ℕ) (hmn : m ≤ n) :
    rootsOfUnitySheaf T (ℓ ^ (n + 1)) ⟶ rootsOfUnitySheaf T (ℓ ^ (m + 1)) :=
  eqToHom (congrArg (rootsOfUnitySheaf T)
    (by rw [← pow_add]; congr 1; omega : ℓ ^ (n + 1) = ℓ ^ (n - m) * ℓ ^ (m + 1))) ≫
      rootsOfUnitySheafPow T (ℓ ^ (m + 1)) (ℓ ^ (n - m))

/-- Native derived scalar extension, computed by K-flat resolutions.
Source: Step 2, finite reduction is derived tensor, not an exact scalar functor
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
abbrev reduction (m n : ℕ) (hmn : m ≤ n) :=
  (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).leftDerivedFunctor

/-- Regroup the ordered positive tensor powers by the canonical associator and unit.
Source: Step 2, product identifications of positive twists
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def product (n r : ℕ) : (s : ℕ) → line ℓ E T n r ⊗ line ℓ E T n s ≅ line ℓ E T n (r + s)
  | 0 => ρ_ _
  | s + 1 => (α_ _ _ _).symm ≪≫ tensorIso (product n r s) (Iso.refl _)

/-- Fibre-product projection, before passing to global sections or roots.
Source: Step 2, pullback of root generators
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def projection {X : Scheme.{u}} (f : X ⟶ T) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ f ⋙
      Scheme.ProEt.forget X ⋙ Over.forget X ⟶ Scheme.ProEt.forget T ⋙ Over.forget T where
  app U := pullback.fst U.hom f
  naturality U V g := by
    dsimp
    simp [MorphismProperty.Over.pullback]

set_option maxHeartbeats 1200000 in
-- Sheafification and pushforward on the large pro-etale site need extra elaboration work.
/-- Pullback of roots along the actual projection, extended by sheafification.
Source: Step 2, roots are pulled back without changing the power transition
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def rootsDirect {X : Scheme.{u}} (f : X ⟶ T) (N : ℕ) :
    rootsOfUnitySheaf T N ⟶ (ProEtale.lowerStar Ab.{u + 1} f).obj (rootsOfUnitySheaf X N) :=
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  let a : rootsOfUnityPresheaf T N ⟶ G.op ⋙ rootsOfUnityPresheaf X N :=
    Functor.whiskerRight (NatTrans.op (projection T f))
      (Scheme.Γ ⋙ CommRingCat.rootsOfUnityFunctor N)
  let b : rootsOfUnityPresheaf T N ⟶ G.op ⋙ (rootsOfUnitySheaf X N).obj :=
    a ≫ Functor.whiskerLeft G.op
      (toSheafify (Scheme.ProEt.topology X) (rootsOfUnityPresheaf X N))
  ((sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).homEquiv
    (rootsOfUnityPresheaf T N)
    ((ProEtale.lowerStar Ab.{u + 1} f).obj (rootsOfUnitySheaf X N))).symm
      (b ≫ (G.sheafPushforwardContinuousCompSheafToPresheafIso Ab.{u + 1}
        (Scheme.ProEt.topology T) (Scheme.ProEt.topology X)).inv.app (rootsOfUnitySheaf X N))

end AlgebraicGeometry.ProEtale.FinitePositiveReduction
