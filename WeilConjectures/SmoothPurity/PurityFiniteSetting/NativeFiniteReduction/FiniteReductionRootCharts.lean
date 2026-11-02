/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteReductionCharts.FiniteReductionChartCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Primitive-root charts for actual finite reduction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2.
(blueprint: def-pur-finite-reduction-root-charts).

The index `n` denotes the positive level `n+1`, as in `twistFiniteRing`.
Everything takes place in the ordinary derived category of modules over the
pulled-back condensed coefficient ring. The section formula fixes the root chart
uniquely; its ordered powers, shifts and pullback use no purity orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.MonObj

section

attribute [-instance] CategoryTheory.sfbSheafTensor_hasWeakSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify

namespace WeilConjectures.PurityFiniteSetting.NativeFiniteReduction

variable (P : PurityFiniteSetting.{u})

/-- The actual quotient, at positive levels n+1 and m+1.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def quotient (n m : ℕ) (h : m ≤ n) :
    Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) →+*
      Padic.coefficientExtensionRing P.coefficients.l P.extension (m + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))

/-- The quotient map of discrete condensed coefficient rings, with its genuine scalar map.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def coefficientQuotient (n m : ℕ) (h : m ≤ n) :
    twistFiniteRing P.coefficients.l P.extension n ⟶ twistFiniteRing P.coefficients.l P.extension m
      :=
  letI : TopologicalSpace (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) :=
    ⟨rfl⟩
  letI : TopologicalSpace (Padic.coefficientExtensionRing P.coefficients.l P.extension (m + 1)) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing P.coefficients.l P.extension (m + 1)) :=
    ⟨rfl⟩
  twistContinuousMap (quotient P n m h) continuous_of_discreteTopology

/-- The quotient preserves the ring operations.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts).
Proof: the quotient is a unital ring homomorphism; applying continuous-function
sheaves and forgetting to abelian ring objects preserves its multiplication and unit. -/
theorem coefficientQuotient_isMonHom (n m : ℕ) (h : m ≤ n) :
    IsMonHom (coefficientQuotient P n m h) := by
  sorry

attribute [instance] coefficientQuotient_isMonHom

/-- Actual derived extension, retaining the target coefficient action. No flatness
hypothesis on the quotient is used.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def reduction (n m : ℕ) (h : m ≤ n) (T : Scheme.{u}) :
    DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)) ⥤
    DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension m) T)) :=
  (Mod.extendScalars (coefficientMap (coefficientQuotient P n m h) T)).leftDerivedFunctor

/-- Reduction preserves bounded constructibility and every given Tor interval.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts).
Proof: represent an input of amplitude [a,b] by a bounded flat complex in those
same degrees. Tensor termwise with the smaller quotient, whose action is retained;
the resulting terms are flat over that quotient, so the same Tor interval works.
On a finite constructible stratification, these are finite locally constant
coefficient complexes, and extension preserves their finite presentation.
Their cohomology is therefore constructible and bounded. This argument uses
associativity of relative tensor, never flatness of the quotient over the source. -/
theorem reduction_preserves (n m : ℕ) (h : m ≤ n) (T : Scheme.{u})
    (K : DerivedCategory.{u + 1}
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))
    (hK : CondensedRing.condensedConstructibleFiniteTor (twistFiniteRing P.coefficients.l
      P.extension n) T K) :
    CondensedRing.condensedConstructibleFiniteTor (twistFiniteRing P.coefficients.l P.extension m) T
        ((reduction P n m h T).obj K) ∧
      ∀ a b : ℤ, a ≤ b → DerivedCategory.torAmplitudeIn _ a b K →
        DerivedCategory.torAmplitudeIn _ a b ((reduction P n m h T).obj K) := by
  sorry

variable (n : ℕ) (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]

/-- The base-field primitive root restricted to a test scheme, then sheafified.
This is the actual root, not a choice of a section or of a basis.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def rootSection (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1)))
    (W : T.ProEtᵒᵖ) : (rootsOfUnitySheaf T (P.coefficients.l ^ (n + 1))).obj.obj W :=
  letI : NeZero (P.coefficients.l ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime
    P.coefficients.l).ne_zero⟩
  let ρ := (Scheme.ΓSpecIso (.of P.field.k)).inv ≫
    (T ↘ Spec (.of P.field.k)).appTop ≫
      ((Scheme.ProEt.forget T).obj W.unop).hom.appTop
  (toSheafify (Scheme.ProEt.topology T) (rootsOfUnityPresheaf T (P.coefficients.l ^ (n + 1)))).app W
    (ULift.up (Additive.ofMul ((restrictRootsOfUnity ρ.hom (P.coefficients.l ^ (n + 1)))
      hζ.toRootsOfUnity)))

/-- The root-line chart is uniquely determined on every local scalar section by
`a ↦ a ⊗ ζ`. The tensor comparison here is the canonical lax-monoidal map of
sheaf-to-presheaf, so this also specifies the formula on constant sections.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts).
Proof: the primitive root identifies the constant Z/l^(n+1) sheaf with roots of
unity, sending j to ζ^j. Extend this map by the coefficient ring. Balancing gives
 a ⊗ ζ^j = aj ⊗ ζ; thus the inverse sends that tensor to aj. These formulas give
both inverse identities and determine the sheaf map uniquely, since pure tensors
locally generate. The etale/pro-etale root comparison preserves the same unit ζ,
and comparison inverse image preserves the balanced tensor and constant scalars.
Consequently this is also the chart obtained by comparison inverse image. -/
theorem existsUnique_rootChart (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    ∃! t : (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing
      P.coefficients.l P.extension n) T))) ≅ coefficientFiniteTwistOne P.coefficients.l P.extension
      T n,
      ∀ (W : T.ProEtᵒᵖ) (a : ((condensedRingObj (twistFiniteRing P.coefficients.l P.extension n)
        T)).obj.obj W),
        t.hom.hom.hom.app W a =
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T) (rootsOfUnitySheaf
              T (P.coefficients.l ^ (n + 1)))).app W)
              (a ⊗ₜ[ℤ] rootSection P n T ζ hζ W) := by
  sorry

/-- The uniquely section-normalized coefficient-root chart.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def rootChart (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing
      P.coefficients.l P.extension n) T))) ≅ coefficientFiniteTwistOne P.coefficients.l P.extension
      T n :=
  (existsUnique_rootChart P n T ζ hζ).choose

/-- The ordered ordinary tensor powers of the inverse line chart: zero is the
unit identity, successors tensor the preceding chart with the fixed line chart
and then use the right unitor. These are exactly the coefficient twist powers.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def powerChart (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) (d : ℕ) :
    coefficientTwistNat T (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)
      (coefficientFiniteTwistOne P.coefficients.l P.extension T n) d ≅ (𝟙_ (Mod (Sheaf
      (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing P.coefficients.l
      P.extension n) T))) :=
  CondensedRing.FiniteReductionCharts.orderedPower (curriedTensor (Mod (Sheaf (Scheme.ProEt.topology
    T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))
    (coefficientTwistNat T (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)
      (coefficientFiniteTwistOne P.coefficients.l P.extension T n))
    (fun _ ↦ 𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing
      P.coefficients.l P.extension n) T))) (coefficientFiniteTwistOne P.coefficients.l P.extension T
      n) (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj (twistFiniteRing
      P.coefficients.l P.extension n) T)))
    (Iso.refl _) (rootChart P n T ζ hζ).symm
    (fun _ ↦ Iso.refl _) (fun _ ↦ ρ_ (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))) d

/-- Place the prescribed power chart in degree zero, shift by 2d, and identify
the derived single of the unit with the derived unit using its canonical map.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def shiftedPowerChart (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) (d : ℕ)
  :
    ((DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)) 0).obj
      (coefficientTwistNat T (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)
        (coefficientFiniteTwistOne P.coefficients.l P.extension T n) d))⟦2 * (d : ℤ)⟧ ≅
        (𝟙_ (DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T))))⟦2 * (d : ℤ)⟧ :=
  (shiftFunctor (DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T))) (2 * (d : ℤ))).mapIso
    ((DerivedCategory.singleFunctor (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)) 0).mapIso (powerChart P
      n T ζ hζ d) ≪≫
      DerivedCategory.singleFunctorObjUnitIso (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))

/-- The exact purity-source chart: the canonical second-variable tensor-shift
reassociation, then the shifted root-power chart, then the tensor-unit shift map.
Source: finite-reduction proof Step 2 and smooth-purity-map source reassociation
(blueprint: def-pur-finite-reduction-root-charts). -/
def sourceChart (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1)))
    (d : ℕ) (M : (DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))) :
    ((coefficientFiniteTwistFunctor P.coefficients.l P.extension T n (d : ℤ)).obj M)⟦2 * (d : ℤ)⟧ ≅
      M⟦2 * (d : ℤ)⟧ :=
  letI := DerivedCategory.commShiftTensorLeft (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)) M
  (((curriedTensor (DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)))).obj M).commShiftIso (2
    * (d : ℤ))).symm.app _ ≪≫
    ((CondensedRing.derivedTensor (twistFiniteRing P.coefficients.l P.extension n) T).obj M).mapIso
      (shiftedPowerChart P n T ζ hζ d) ≪≫
        CondensedRing.FiniteReductionCharts.tensorUnit (twistFiniteRing P.coefficients.l P.extension
          n) T M
          (2 * (d : ℤ))

/-- Specialize the chart to the genuine ordinary derived inverse image. Its domain
is Lf* K(d)[2d], the source of smooth purity. This construction works for every
morphism and input, hence in particular on the stipulated smooth finite-type ctf
inputs, and never uses a purity orientation or exceptional inverse image.
Source: finite-reduction proof Step 2 (blueprint: def-pur-finite-reduction-root-charts). -/
def pullbackSourceChart {Y : Scheme.{u}} (f : T ⟶ Y)
    (ζ : P.field.k) (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) (d : ℕ)
    (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) Y))) :=
  sourceChart P n T ζ hζ d
    ((CondensedRing.upperStar (twistFiniteRing P.coefficients.l P.extension n)
      f).leftDerivedFunctor.obj K)

end WeilConjectures.PurityFiniteSetting.NativeFiniteReduction

end
