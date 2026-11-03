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
public import WeilConjectures.AlgebraicGeometry.Native.NativeFiniteTwistLocalLine
public import WeilConjectures.AlgebraicGeometry.PoincareDuality.CompatiblePrimitiveRoots

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
  unfold coefficientQuotient
  infer_instance

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

private def normalizedRootSheafIso (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod (P.coefficients.l ^ (n + 1))))) ≅
      rootsOfUnitySheaf T (P.coefficients.l ^ (n + 1)) := by
  let N := P.coefficients.l ^ (n + 1)
  let : NeZero N := ⟨pow_ne_zero _ (Fact.out : Nat.Prime P.coefficients.l).ne_zero⟩
  let φ : P.field.k →+* Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (.of P.field.k)).inv ≫
      (T ↘ Spec (.of P.field.k)).appTop).hom
  let z : Γ(T, ⊤)ˣ := Units.map φ.toMonoidHom hζ.toRootsOfUnity.val
  have hzval : (z : Γ(T, ⊤)) = φ ζ := by
    change φ hζ.toRootsOfUnity.val.val = φ ζ
    rw [hζ.val_toRootsOfUnity_coe]
  have hz : z ^ N = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    rw [hzval, ← map_pow, hζ.pow_eq_one, map_one]
  apply constantRootsIso N z hz
  intro i hi j hj hij
  rw [hzval, ← map_pow, ← map_pow, ← map_sub]
  apply IsUnit.map
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr
    (fun he ↦ hij (hζ.pow_inj hi hj he)))

private def normalizedRootModuleIso (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    (𝟙_ (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T))) ≅
        coefficientFiniteTwistOne P.coefficients.l P.extension T n :=
  (freeConstantResidueIso _ (P.coefficients.l ^ (n + 1))
    (finiteRing_nsmul P.coefficients.l P.extension T n)).symm ≪≫
      (Mod.freeFunctor _).mapIso (normalizedRootSheafIso P n T ζ hζ)

private theorem tensorUnitSection
    (R M : Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (b : 𝟙_ _ ⟶ M) (W : T.ProEtᵒᵖ) (a : R.obj.obj W) :
    (((ρ_ R).inv ≫ R ◁ b).hom.app W) a =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        R M).app W
          (a ⊗ₜ[ℤ] (b.hom.app W
            ((Functor.LaxMonoidal.ε
              (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})).app W (ULift.up 1)))) := by
  let U := sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  have he : U.map ((ρ_ R).inv ≫ R ◁ b) =
      (ρ_ (U.obj R)).inv ≫
        U.obj R ◁ (Functor.LaxMonoidal.ε U ≫ U.map b) ≫
          Functor.LaxMonoidal.μ U R M := by
    rw [Functor.map_comp,
      ← Functor.LaxMonoidal.right_unitality_inv U R]
    simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp,
      Functor.LaxMonoidal.μ_natural_right]
  exact ConcreteCategory.congr_hom (congr_app he W) a

private def normalizedRootUnitMap (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    𝟙_ (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ⟶
      rootsOfUnitySheaf T (P.coefficients.l ^ (n + 1)) :=
  (Functor.Monoidal.εIso
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1})).hom ≫
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (AddCommGrpCat.intResidue (P.coefficients.l ^ (n + 1))) ≫
          (normalizedRootSheafIso P n T ζ hζ).hom

private theorem normalizedRootModuleIso_hom (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) :
    (normalizedRootModuleIso P n T ζ hζ).hom.hom =
      (ρ_ (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)).inv ≫
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T) ◁
          normalizedRootUnitMap P n T ζ hζ := by
  change ((ρ_ _).inv ≫ _ ◁ (Functor.Monoidal.εIso
    (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1})).hom) ≫
      _ ◁ (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (AddCommGrpCat.intResidue (P.coefficients.l ^ (n + 1))) ≫
          _ ◁ (normalizedRootSheafIso P n T ζ hζ).hom = _
  simp only [normalizedRootUnitMap, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rfl

private theorem constantSheafUnitNormalization :
    Functor.LaxMonoidal.ε
        (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}) ≫
      (Functor.Monoidal.εIso
        (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1})).hom.hom =
      toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1})) := by
  let L := presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  let U := sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}
  have he : (Functor.Monoidal.εIso
      (constantSheaf (Scheme.ProEt.topology T) Ab.{u + 1})).hom =
        Functor.LaxMonoidal.ε L := by
    change Functor.LaxMonoidal.ε
      ((Functor.const T.ProEtᵒᵖ) ⋙ L) = _
    rw [Functor.LaxMonoidal.comp_ε]
    change Functor.LaxMonoidal.ε L ≫ L.map (𝟙 _) = _
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [he]
  change Functor.LaxMonoidal.ε U ≫ U.map (Functor.LaxMonoidal.ε L) = _
  rw [← (sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).unit_app_unit_comp_map_η]
  simp only [Category.assoc]
  rfl

private theorem normalizedRootUnitMap_section (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1))) (W : T.ProEtᵒᵖ) :
    (normalizedRootUnitMap P n T ζ hζ).hom.app W
        ((Functor.LaxMonoidal.ε
          (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})).app W (ULift.up 1)) =
      rootSection P n T ζ hζ W := by
  let N := P.coefficients.l ^ (n + 1)
  let : NeZero N := ⟨pow_ne_zero _ (Fact.out : Nat.Prime P.coefficients.l).ne_zero⟩
  let φ : P.field.k →+* Γ(T, ⊤) :=
    ((Scheme.ΓSpecIso (.of P.field.k)).inv ≫
      (T ↘ Spec (.of P.field.k)).appTop).hom
  let z : Γ(T, ⊤)ˣ := Units.map φ.toMonoidHom hζ.toRootsOfUnity.val
  have hz : z ^ N = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_one]
    change (φ hζ.toRootsOfUnity.val.val) ^ N = 1
    rw [hζ.val_toRootsOfUnity_coe, ← map_pow, hζ.pow_eq_one, map_one]
  let σ := zmodToRootsPresheaf T N z hz
  let J := Scheme.ProEt.topology T
  let C := constantSheaf J Ab.{u + 1}
  have he : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
      (normalizedRootUnitMap P n T ζ hζ).hom =
        (Functor.const T.ProEtᵒᵖ).map (AddCommGrpCat.intResidue N) ≫
          σ ≫ toSheafify J (rootsOfUnityPresheaf T N) := by
    change _ ≫ ((Functor.Monoidal.εIso C).hom.hom ≫
      (C.map (AddCommGrpCat.intResidue N)).hom ≫
        (normalizedRootSheafIso P n T ζ hζ).hom.hom) = _
    rw [← Category.assoc, ← Category.assoc, constantSheafUnitNormalization]
    change (toSheafify J ((Functor.const T.ProEtᵒᵖ).obj (𝟙_ Ab.{u + 1})) ≫
      ((presheafToSheaf J Ab.{u + 1}).map
        ((Functor.const T.ProEtᵒᵖ).map (AddCommGrpCat.intResidue N))).hom) ≫
          ((presheafToSheaf J Ab.{u + 1}).map σ).hom = _
    rw [Category.assoc]
    change toSheafify J _ ≫
      (((presheafToSheaf J Ab.{u + 1}).map
        ((Functor.const T.ProEtᵒᵖ).map (AddCommGrpCat.intResidue N))) ≫
          (presheafToSheaf J Ab.{u + 1}).map σ).hom = _
    rw [← Functor.map_comp]
    simpa only [Category.assoc] using (toSheafify_naturality J
      ((Functor.const T.ProEtᵒᵖ).map (AddCommGrpCat.intResidue N) ≫ σ)).symm
  have hv := ConcreteCategory.congr_hom (congr_app he W) (ULift.up 1)
  have h1 : AddCommGrpCat.intResidue N (ULift.up 1) = ULift.up (1 : ZMod N) := by
    apply ULift.ext
    change ((1 : ℤ) : ZMod N) = 1
    exact Int.cast_one
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hv
  change _ = (toSheafify J (rootsOfUnityPresheaf T N)).app W
    (σ.app W (AddCommGrpCat.intResidue N (ULift.up 1))) at hv
  rw [h1] at hv
  refine hv.trans ?_
  change (toSheafify J (rootsOfUnityPresheaf T N)).app W _ =
    (toSheafify J (rootsOfUnityPresheaf T N)).app W _
  apply congrArg ((toSheafify J (rootsOfUnityPresheaf T N)).app W)
  apply ULift.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  have hh := zmodToRootsPresheaf_app_natCast N z hz W 1
  simp only [Nat.cast_one, pow_one] at hh
  exact hh.trans (by rfl)

private theorem normalizedRootModuleIso_section (ζ : P.field.k)
    (hζ : IsPrimitiveRoot ζ (P.coefficients.l ^ (n + 1)))
    (W : T.ProEtᵒᵖ)
    (a : (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T).obj.obj W) :
    (normalizedRootModuleIso P n T ζ hζ).hom.hom.hom.app W a =
      (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)
          (rootsOfUnitySheaf T (P.coefficients.l ^ (n + 1)))).app W
            (a ⊗ₜ[ℤ] rootSection P n T ζ hζ W) := by
  let R := condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T
  let M := rootsOfUnitySheaf T (P.coefficients.l ^ (n + 1))
  let b := normalizedRootUnitMap P n T ζ hζ
  have he := congrArg (fun f : R ⟶ R ⊗ M ↦ f.hom.app W a)
    (normalizedRootModuleIso_hom P n T ζ hζ)
  refine he.trans ((tensorUnitSection T R M b W a).trans ?_)
  apply congrArg ((Functor.LaxMonoidal.μ
    (sheafToPresheaf (Scheme.ProEt.topology T) Ab.{u + 1}) R M).app W)
  exact congrArg (fun z ↦ a ⊗ₜ[ℤ] z) (normalizedRootUnitMap_section P n T ζ hζ W)

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
  refine ⟨normalizedRootModuleIso P n T ζ hζ,
    normalizedRootModuleIso_section P n T ζ hζ, ?_⟩
  intro t ht
  apply Iso.ext
  apply Mod.hom_ext
  ext W a
  exact (ht W a).trans (normalizedRootModuleIso_section P n T ζ hζ W a).symm

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
