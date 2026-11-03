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
public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FinitePositiveReductionPullback
public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FiniteRootScalarIsomorphism
public import WeilConjectures.CategoryTheory.Adjunction.FlatSingleAdjointTranspose

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

/-- The semilinear root map, uniquely determined on the underlying tensor by
`a tensor u` mapping to `bar a tensor u^(ell^(n-m))`.
Source: Step 2, explicit finite twist formula
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def rootMap (m n : ℕ) (hmn : m ≤ n) :
    coefficientFiniteTwistOne ℓ E T n ⟶
      (Mod.comap (coefficientMap (quotient ℓ E m n hmn) T)).obj
        (coefficientFiniteTwistOne ℓ E T m) :=
  (Mod.comapId _).inv.app _ ≫
    (coefficientFreeTensor_linear (𝟙 (condensedRingObj (twistFiniteRing ℓ E n) T))
      (coefficientMap (quotient ℓ E m n hmn) T)
      (coefficientMap (quotient ℓ E m n hmn) T) (Category.id_comp _)
      (roots ℓ T m n hmn)).exists.choose

/-- Tensor the root map, using multiplication of reduced scalars; power zero is
exactly the coefficient homomorphism. No flatness is used in this construction.
Source: Step 2, finite twist tensor powers
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def semilinear (m n : ℕ) (hmn : m ≤ n) :
    (r : ℕ) → line ℓ E T n r ⟶
      (Mod.comap (coefficientMap (quotient ℓ E m n hmn) T)).obj (line ℓ E T m r)
  | 0 => Mod.comapUnitHom (coefficientMap (quotient ℓ E m n hmn) T)
  | r + 1 => (semilinear m n hmn r ⊗ₘ rootMap ℓ E T m n hmn) ≫
      Mod.comapTensorHom (coefficientMap (quotient ℓ E m n hmn) T)
        (line ℓ E T m r) (coefficientFiniteTwistOne ℓ E T m)

/-- Ordinary balanced scalar extension of the specified semilinear root map.
Source: Step 2, a e tensor b maps to bar a b e
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def sheafMap (m n : ℕ) (hmn : m ≤ n) (r : ℕ) :
    (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).obj
      (line ℓ E T n r) ⟶ line ℓ E T m r :=
  Mod.extendHom _ (semilinear ℓ E T m n hmn r)

/-- Native derived scalar extension, computed by K-flat resolutions.
Source: Step 2, finite reduction is derived tensor, not an exact scalar functor
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
abbrev reduction (m n : ℕ) (hmn : m ≤ n) :=
  (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).leftDerivedFunctor

/-- The line as its single complex in any degree, using the ordinary unbounded category.
Source: Step 2, shifts of the degree-zero line
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
abbrev single (n r : ℕ) (i : ℤ) := (DerivedCategory.singleFunctor _ i).obj (line ℓ E T n r)

/-- Derived normalization: the adjoint transpose is the single of the actual semilinear map.
It determines an arrow uniquely, and implements the primitive-root formula locally.
Source: Step 2, scalar adjunction and single-complex normalization
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def Normalized (m n : ℕ) (hmn : m ≤ n) (r : ℕ) (i : ℤ)
    (f : (reduction ℓ E T m n hmn).obj (single ℓ E T n r i) ⟶ single ℓ E T m r i) : Prop :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (quotient ℓ E m n hmn) T)).homEquiv _ _ f =
    (DerivedCategory.singleFunctor _ i).map (semilinear ℓ E T m n hmn r) ≫
      ((Mod.comap
        (coefficientMap (quotient ℓ E m n hmn) T)).mapDerivedCategorySingleFunctor i).inv.app
        (line ℓ E T m r)

/-- The canonical normalized derived arrow, obtained from the actual scalar adjunction.
Source: Step 2, canonical finite reduction comparison
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def derivedMap (m n : ℕ) (hmn : m ≤ n) (r : ℕ) (i : ℤ) :
    (reduction ℓ E T m n hmn).obj (single ℓ E T n r i) ⟶ single ℓ E T m r i :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap (quotient ℓ E m n hmn) T)).homEquiv _ _).symm
    ((DerivedCategory.singleFunctor _ i).map (semilinear ℓ E T m n hmn r) ≫
      ((Mod.comap
        (coefficientMap (quotient ℓ E m n hmn) T)).mapDerivedCategorySingleFunctor i).inv.app
        (line ℓ E T m r))

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

/-- The root-line inverse-image comparison is the free-module adjunct of root pullback,
then the module-pullback adjunct. This fixes its scalar action and root normalization.
Source: Step 2, native Tate lines commute with pullback
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def pullOne {X : Scheme.{u}} (f : X ⟶ T) (n : ℕ) :
    (CondensedRing.upperStar (twistFiniteRing ℓ E n) f).obj
      (coefficientFiniteTwistOne ℓ E T n) ⟶ coefficientFiniteTwistOne ℓ E X n :=
  ((CondensedRing.upperStarLowerStarAdjunction (twistFiniteRing ℓ E n) f).homEquiv
    (coefficientFiniteTwistOne ℓ E T n) (coefficientFiniteTwistOne ℓ E X n)).symm
    (((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing ℓ E n) T)).homEquiv
      (rootsOfUnitySheaf T (ℓ ^ (n + 1)))
      ((CondensedRing.lowerStar (twistFiniteRing ℓ E n) f).obj
        (coefficientFiniteTwistOne ℓ E X n))).symm
      (rootsDirect T f (ℓ ^ (n + 1)) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing ℓ E n) X)).unit.app
            (rootsOfUnitySheaf X (ℓ ^ (n + 1))))))

/-- Pull back positive powers through the canonical monoidal comparison.
Source: Step 2, pullback and tensor associativity
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def pull {X : Scheme.{u}} (f : X ⟶ T) (n : ℕ) :
    (r : ℕ) → (CondensedRing.upperStar (twistFiniteRing ℓ E n) f).obj
      (line ℓ E T n r) ⟶ line ℓ E X n r
  | 0 => (Functor.Monoidal.εIso (CondensedRing.upperStar (twistFiniteRing ℓ E n) f)).inv
  | r + 1 =>
      (Functor.Monoidal.μIso (CondensedRing.upperStar (twistFiniteRing ℓ E n) f)
        (line ℓ E T n r) (coefficientFiniteTwistOne ℓ E T n)).inv ≫
          (pull f n r ⊗ₘ pullOne ℓ E T f n)

/-- The scalar tensorator with its specific balanced-tensor normalization.
Source: Step 2, tensor products and coefficient reduction
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
def scalarTensor (m n : ℕ) (hmn : m ≤ n) (r s : ℕ) :
    (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).obj
      (line ℓ E T n r ⊗ line ℓ E T n s) ⟶
    (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).obj (line ℓ E T n r) ⊗
      (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).obj (line ℓ E T n s) :=
  letI := Mod.extendScalarsOplaxMonoidal (coefficientMap (quotient ℓ E m n hmn) T)
  Functor.OplaxMonoidal.δ _ _ _

end AlgebraicGeometry.ProEtale.FinitePositiveReduction

namespace AlgebraicGeometry.ProEtale.FinitePositiveReduction

/-- Normalization is precisely equality to the canonical adjoint transpose.
Source: scalar adjunction, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem normalized_iff (m n : ℕ) (hmn : m ≤ n) (r : ℕ) (i : ℤ)
    (f : (reduction ℓ E T m n hmn).obj (single ℓ E T n r i) ⟶ single ℓ E T m r i) :
    Normalized ℓ E T m n hmn r i f ↔ f = derivedMap ℓ E T m n hmn r i := by
  exact (Equiv.eq_symm_apply _).symm

/-- An invertible canonical arrow gives the unique normalized isomorphism.
Source: uniqueness in Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem normalized_iso (m n : ℕ) (hmn : m ≤ n) (r : ℕ) (i : ℤ)
    [IsIso (derivedMap ℓ E T m n hmn r i)] :
    ∃! e : (reduction ℓ E T m n hmn).obj (single ℓ E T n r i) ≅
        single ℓ E T m r i, Normalized ℓ E T m n hmn r i e.hom := by
  refine ⟨asIso (derivedMap ℓ E T m n hmn r i), ?_, ?_⟩
  · exact (normalized_iff ℓ E T m n hmn r i _).2 rfl
  · intro e he
    apply Iso.ext
    exact (normalized_iff ℓ E T m n hmn r i _).1 he

/-- Equal-level reduction is the identity coefficient morphism.
Source: equal-level normalization, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem quotient_self (n : ℕ) : quotient ℓ E n n le_rfl = 𝟙 _ := by
  let : TopologicalSpace (Padic.coefficientExtensionRing ℓ E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing ℓ E (n + 1)) := ⟨rfl⟩
  ext V a
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change Ideal.Quotient.factor
    (le_refl (Padic.coefficientExtensionIdeal ℓ E (n + 1))) (a.down x) = a.down x
  rw [Ideal.Quotient.factor_eq]
  rfl

/-- Power one induces the identity map of root sheaves.
Source: equal-level normalization, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem roots_power_one (N : ℕ) :
    eqToHom (congrArg (rootsOfUnitySheaf T) (one_mul N).symm) ≫
      rootsOfUnitySheafPow T N 1 = 𝟙 _ := by
  have hh (N M : ℕ) (h : N = M) :
      eqToHom (congrArg (rootsOfUnitySheaf T) h) =
      (presheafToSheaf (Scheme.ProEt.topology T) Ab.{u + 1}).map
        (eqToHom (congrArg (rootsOfUnityPresheaf T) h)) := by
    subst M
    simp only [eqToHom_refl, CategoryTheory.Functor.map_id]
    rfl
  rw [hh N (1 * N) (one_mul N).symm, rootsOfUnitySheafPow, ← Functor.map_comp]
  have hp :
      eqToHom (congrArg (rootsOfUnityPresheaf T) (one_mul N).symm) ≫
        Functor.whiskerLeft ((Scheme.ProEt.forget T ⋙ Over.forget T).op ⋙ Scheme.Γ)
          (CommRingCat.rootsOfUnityPow N 1) = 𝟙 _ := by
    have hp' : CommRingCat.rootsOfUnityPow N 1 =
        eqToHom (congrArg CommRingCat.rootsOfUnityFunctor (one_mul N)) := by
      ext R x
      have he (n m : ℕ) (h : n = m) (x : (CommRingCat.rootsOfUnityFunctor n).obj R) :
          (eqToHom (congrArg CommRingCat.rootsOfUnityFunctor h)).app R x =
            (eqToHom (congrArg (fun k ↦ (CommRingCat.rootsOfUnityFunctor k).obj R) h)) x := by
        subst m
        rfl
      rw [he (1 * N) N (one_mul N)]
      apply ULift.ext
      apply Subtype.ext
      apply Units.ext
      simp only [CommRingCat.rootsOfUnityPow, CommRingCat.rootsOfUnityPowHom]
      have hc (a b : ℕ) (h : a = b)
          (x : (CommRingCat.rootsOfUnityFunctor a).obj R) :
          ((eqToHom (congrArg (fun k ↦ (CommRingCat.rootsOfUnityFunctor k).obj R) h))
            x).down.toMul.val = x.down.toMul.val := by
        subst b
        rfl
      change (x.down.toMul.val ^ 1).val = _
      rw [pow_one]
      exact (congrArg Units.val (hc (1 * N) N (one_mul N) x)).symm
    have hw (a b : ℕ) (h : a = b) :
        Functor.whiskerLeft ((Scheme.ProEt.forget T ⋙ Over.forget T).op ⋙ Scheme.Γ)
          (eqToHom (congrArg CommRingCat.rootsOfUnityFunctor h)) =
          eqToHom (congrArg (rootsOfUnityPresheaf T) h) := by
      subst b
      rfl
    rw [hp', hw (1 * N) N (one_mul N), eqToHom_trans]
    simp
  rw [hp]
  exact CategoryTheory.Functor.map_id _ _

/-- The equal-level arithmetic cast does not change the power-one map.
Source: equal-level normalization, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem roots_self (n : ℕ) : roots ℓ T n n le_rfl = 𝟙 _ := by
  have hh (k N : ℕ) (h : N = k * N) (hk : k = 1) :
      eqToHom (congrArg (rootsOfUnitySheaf T) h) ≫ rootsOfUnitySheafPow T N k = 𝟙 _ := by
    subst k
    exact roots_power_one T N
  exact hh _ _ (by simp) (by simp)

/-- The underlying first-line map is the specified coefficient tensor root map.
Source: tensor normalization, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem rootMap_hom (m n : ℕ) (hmn : m ≤ n) :
    (rootMap ℓ E T m n hmn).hom =
      coefficientMap (quotient ℓ E m n hmn) T ⊗ₘ roots ℓ T m n hmn := by
  unfold rootMap
  rw [Mod.comp_hom']
  have h := (coefficientFreeTensor_linear
    (𝟙 (condensedRingObj (twistFiniteRing ℓ E n) T))
    (coefficientMap (quotient ℓ E m n hmn) T)
    (coefficientMap (quotient ℓ E m n hmn) T) (Category.id_comp _)
    (roots ℓ T m n hmn)).exists.choose_spec
  change (𝟙 _ ≫ _) = _
  simpa only [Category.id_comp] using h

/-- The semilinear equal-level comparison has the identity underlying sheaf map.
Source: equal-level normalization, Step 2
(blueprint: lem-pur-finite-reduction-positive-line-comparison). -/
private theorem semilinear_self (n r : ℕ) :
    (semilinear ℓ E T n n le_rfl r).hom = 𝟙 _ := by
  have hφ : coefficientMap (quotient ℓ E n n le_rfl) T = 𝟙 _ := by
    rw [quotient_self, coefficientMap_id]
  have hroot : (rootMap ℓ E T n n le_rfl).hom = 𝟙 _ := by
    calc
      _ = coefficientMap (quotient ℓ E n n le_rfl) T ⊗ₘ roots ℓ T n n le_rfl :=
        rootMap_hom ℓ E T n n le_rfl
      _ = 𝟙 _ := by simp only [hφ, roots_self, MonoidalCategory.tensorHom_def, id_whiskerRight,
        whiskerLeft_id, Category.id_comp]
  induction r with
  | zero => exact hφ
  | succ r ih =>
    apply (cancel_epi (Mod.tensorObjπ (line ℓ E T n r)
      (coefficientFiniteTwistOne ℓ E T n))).1
    change _ ≫ (semilinear ℓ E T n n le_rfl r ⊗ₘ
      rootMap ℓ E T n n le_rfl).hom ≫ _ = _
    rw [← Category.assoc, Mod.tensorObjπ_tensorHom_hom_whisker, Category.assoc]
    simp only [ih, hroot, id_whiskerRight, whiskerLeft_id, Category.id_comp]
    rw [Mod.tensorObjπ_comapTensorHom_hom]
    change Mod.tensorObjπ (line ℓ E T n r) (coefficientFiniteTwistOne ℓ E T n) =
      Mod.tensorObjπ (line ℓ E T n r) (coefficientFiniteTwistOne ℓ E T n) ≫ 𝟙 _
    rw [Category.comp_id]

/-- Scalar adjunction transposes tensor products through its oplax tensorator. -/
private theorem transpose_tensor {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.OplaxMonoidal] [G.LaxMonoidal]
    (adj : F ⊣ G) [adj.IsMonoidal]
    {X Y : C} {A B : D} (f : X ⟶ G.obj A) (g : Y ⟶ G.obj B) :
    (adj.homEquiv _ _).symm ((f ⊗ₘ g) ≫ Functor.LaxMonoidal.μ G A B) =
      Functor.OplaxMonoidal.δ F X Y ≫
        ((adj.homEquiv _ _).symm f ⊗ₘ (adj.homEquiv _ _).symm g) := by
  simp only [adj.homEquiv_counit, F.map_comp]
  rw [Category.assoc, adj.map_μ_comp_counit_app_tensor,
    ← Functor.OplaxMonoidal.δ_natural_assoc, tensorHom_comp_tensorHom]

/-- Tensor recursion for the ordinary reduction map. -/
private theorem sheafMap_succ (m n : ℕ) (hmn : m ≤ n) (r : ℕ) :
    letI := Mod.extendScalarsOplaxMonoidal (coefficientMap (quotient ℓ E m n hmn) T)
    sheafMap ℓ E T m n hmn (r + 1) =
      Functor.OplaxMonoidal.δ
        (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T))
        (line ℓ E T n r) (coefficientFiniteTwistOne ℓ E T n) ≫
        (sheafMap ℓ E T m n hmn r ⊗ₘ Mod.extendHom _ (rootMap ℓ E T m n hmn)) := by
  let φ := coefficientMap (quotient ℓ E m n hmn) T
  let := Mod.comapLaxMonoidal φ
  let := Mod.extendScalarsOplaxMonoidal φ
  have : (Mod.extendRestrictAdjunction φ).IsMonoidal := by infer_instance
  have ht (A) (B) (f : A ⟶ (Mod.comap φ).obj B) :
      ((Mod.extendRestrictAdjunction φ).homEquiv _ _).symm f = Mod.extendHom φ f := by
    unfold Mod.extendRestrictAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have hh := transpose_tensor (Mod.extendRestrictAdjunction φ)
    (semilinear ℓ E T m n hmn r) (rootMap ℓ E T m n hmn)
  rw [ht, ht, ht] at hh
  exact hh

/-- Oplax associativity with three specified outgoing maps. -/
private theorem product_step {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal]
    (X Y Z : C) (A B C' P : D) (a : F.obj X ⟶ A) (b : F.obj Y ⟶ B)
    (c : F.obj Z ⟶ C') (p : A ⊗ B ⟶ P) :
    F.map (α_ X Y Z).inv ≫ Functor.OplaxMonoidal.δ F (X ⊗ Y) Z ≫
      ((Functor.OplaxMonoidal.δ F X Y ≫ (a ⊗ₘ b) ≫ p) ⊗ₘ c) =
    Functor.OplaxMonoidal.δ F X (Y ⊗ Z) ≫
      (a ⊗ₘ (Functor.OplaxMonoidal.δ F Y Z ≫ (b ⊗ₘ c))) ≫
      (α_ A B C').inv ≫ (p ⊗ₘ 𝟙 C') := by
  calc
    _ = F.map (α_ X Y Z).inv ≫ Functor.OplaxMonoidal.δ F (X ⊗ Y) Z ≫
        (Functor.OplaxMonoidal.δ F X Y ⊗ₘ 𝟙 (F.obj Z)) ≫
        ((a ⊗ₘ b) ⊗ₘ c) ≫ (p ⊗ₘ 𝟙 C') := by
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = Functor.OplaxMonoidal.δ F X (Y ⊗ Z) ≫
        (𝟙 (F.obj X) ⊗ₘ Functor.OplaxMonoidal.δ F Y Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
        ((a ⊗ₘ b) ⊗ₘ c) ≫ (p ⊗ₘ 𝟙 C') := by
      simp only [tensorHom_id, id_tensorHom]
      rw [← Functor.OplaxMonoidal.associativity_inv_assoc]
    _ = _ := by
      rw [← associator_inv_naturality_assoc]
      simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]

/-- Products of the specified reduction maps concatenate the ordered generators. -/
private theorem sheafMap_product (m n : ℕ) (hmn : m ≤ n) (r s : ℕ) :
    (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T)).map
        (product ℓ E T n r s).hom ≫ sheafMap ℓ E T m n hmn (r + s) =
      scalarTensor ℓ E T m n hmn r s ≫
        (sheafMap ℓ E T m n hmn r ⊗ₘ sheafMap ℓ E T m n hmn s) ≫
          (product ℓ E T m r s).hom := by
  let φ := coefficientMap (quotient ℓ E m n hmn) T
  let F := Mod.extendScalars φ
  let := Mod.extendScalarsOplaxMonoidal φ
  have hδ (r s : ℕ) : scalarTensor ℓ E T m n hmn r s =
      Functor.OplaxMonoidal.δ F (line ℓ E T n r) (line ℓ E T n s) :=
    (Mod.extendScalarsOplaxMonoidal_δ φ _ _).symm
  have hη : sheafMap ℓ E T m n hmn 0 = Functor.OplaxMonoidal.η F :=
    (Mod.extendScalarsOplaxMonoidal_η φ).symm
  simp only [hδ]
  induction s with
  | zero =>
    change F.map (ρ_ (line ℓ E T n r)).hom ≫ sheafMap ℓ E T m n hmn r =
      Functor.OplaxMonoidal.δ F (line ℓ E T n r) (𝟙_ _) ≫
        (sheafMap ℓ E T m n hmn r ⊗ₘ sheafMap ℓ E T m n hmn 0) ≫
        (ρ_ (line ℓ E T m r)).hom
    rw [hη]
    change F.map (ρ_ _).hom ≫ sheafMap ℓ E T m n hmn r =
      Functor.OplaxMonoidal.δ F _ (𝟙_ _) ≫
        (sheafMap ℓ E T m n hmn r ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (ρ_ _).hom
    rw [tensorHom_def', Category.assoc, rightUnitor_naturality]
    simp only [Functor.OplaxMonoidal.right_unitality_hom_assoc]
  | succ s ih =>
    simp only [Nat.add_succ]
    rw [sheafMap_succ ℓ E T m n hmn (r + s), sheafMap_succ ℓ E T m n hmn s]
    change F.map ((α_ (line ℓ E T n r) (line ℓ E T n s)
      (coefficientFiniteTwistOne ℓ E T n)).inv ≫
      ((product ℓ E T n r s).hom ⊗ₘ 𝟙 _)) ≫ _ =
      _ ≫ _ ≫ ((α_ (line ℓ E T m r) (line ℓ E T m s)
        (coefficientFiniteTwistOne ℓ E T m)).inv ≫
        ((product ℓ E T m r s).hom ⊗ₘ 𝟙 _))
    let g : F.obj (coefficientFiniteTwistOne ℓ E T n) ⟶
        coefficientFiniteTwistOne ℓ E T m := Mod.extendHom φ (rootMap ℓ E T m n hmn)
    change F.map ((α_ _ _ _).inv ≫ ((product ℓ E T n r s).hom ⊗ₘ 𝟙 _)) ≫
      (Functor.OplaxMonoidal.δ F _ _ ≫ (sheafMap ℓ E T m n hmn (r + s) ⊗ₘ g)) =
      Functor.OplaxMonoidal.δ F _ _ ≫
        (sheafMap ℓ E T m n hmn r ⊗ₘ
          (Functor.OplaxMonoidal.δ F _ _ ≫ (sheafMap ℓ E T m n hmn s ⊗ₘ g))) ≫
        (α_ _ _ _).inv ≫ ((product ℓ E T m r s).hom ⊗ₘ 𝟙 _)
    rw [F.map_comp, Category.assoc, ← Functor.OplaxMonoidal.δ_natural_assoc]
    rw [tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [ih]
    exact product_step F _ _ _ _ _ _ _ _ _ _ _

/-- The compatible scalar adjunction carries shifted transposes to transposed shifts. -/
private theorem homEquiv_shift {C D : Type*} [Category C] [Category D]
    [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {G : D ⥤ C} [F.CommShift ℤ] [G.CommShift ℤ] (adj : F ⊣ G) [adj.CommShift ℤ]
    (i : ℤ) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    adj.homEquiv _ _ ((F.commShiftIso i).hom.app X ≫ f⟦i⟧') =
      (adj.homEquiv _ _ f)⟦i⟧' ≫ (G.commShiftIso i).inv.app Y := by
  have hu : adj.unit.app (X⟦i⟧) ≫ G.map ((F.commShiftIso i).hom.app X) =
      (adj.unit.app X)⟦i⟧' ≫ (G.commShiftIso i).inv.app (F.obj X) := by
    apply (cancel_mono ((G.commShiftIso i).hom.app (F.obj X))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    change adj.unit.app (X⟦i⟧) ≫ G.map ((F.commShiftIso i).hom.app X) ≫
      (G.commShiftIso i).hom.app (F.obj X) = (adj.unit.app X)⟦i⟧' ≫ 𝟙 _
    rw [Category.comp_id]
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      adj.unit_app_commShiftIso_hom_app ℤ i X
  rw [adj.homEquiv_unit, G.map_comp, ← Category.assoc, hu, Category.assoc]
  have hn := (G.commShiftIso i).inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rw [adj.homEquiv_unit, (shiftFunctor C i).map_comp, Category.assoc]

/-- Shifting a normalized reduction map retains the same semilinear transpose. -/
private theorem derivedMap_shift (m n : ℕ) (hmn : m ≤ n) (r : ℕ)
    (i a b : ℤ) (h : i + a = b) :
    (reduction ℓ E T m n hmn).map
        (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
          (line ℓ E T n r)) ≫ derivedMap ℓ E T m n hmn r a =
      ((reduction ℓ E T m n hmn).commShiftIso i).hom.app (single ℓ E T n r b) ≫
        (derivedMap ℓ E T m n hmn r b)⟦i⟧' ≫
          (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
            (line ℓ E T m r)) := by
  let U : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing ℓ E m) T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing ℓ E n) T) :=
    Mod.comap (coefficientMap (quotient ℓ E m n hmn) T)
  let adj : reduction ℓ E T m n hmn ⊣ U.mapDerivedCategory :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (quotient ℓ E m n hmn) T)
  have : adj.CommShift ℤ := Adjunction.commShift_of_rightAdjoint (A := ℤ) adj
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [← Category.assoc (((reduction ℓ E T m n hmn).commShiftIso i).hom.app
    (single ℓ E T n r b)) ((derivedMap ℓ E T m n hmn r b)⟦i⟧') _]
  rw [Adjunction.homEquiv_naturality_right]
  have hh := homEquiv_shift (F := reduction ℓ E T m n hmn)
    (G := U.mapDerivedCategory) adj i (derivedMap ℓ E T m n hmn r b)
  change (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
      (line ℓ E T n r)) ≫ adj.homEquiv _ _ (derivedMap ℓ E T m n hmn r a) =
    adj.homEquiv ((single ℓ E T n r b)⟦i⟧) ((single ℓ E T m r b)⟦i⟧)
      (((reduction ℓ E T m n hmn).commShiftIso i).hom.app
        (single ℓ E T n r b) ≫ (derivedMap ℓ E T m n hmn r b)⟦i⟧') ≫
      U.mapDerivedCategory.map (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
        (line ℓ E T m r))
  rw [hh]
  have ht (j : ℤ) : adj.homEquiv _ _ (derivedMap ℓ E T m n hmn r j) =
      (DerivedCategory.singleFunctor _ j).map (semilinear ℓ E T m n hmn r) ≫
        (U.mapDerivedCategorySingleFunctor j).inv.app (line ℓ E T m r) :=
    Equiv.apply_symm_apply _ _
  rw [ht, ht]
  have hn := (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.naturality
    (semilinear ℓ E T m n hmn r))
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, (shiftFunctor _ i).map_comp, Category.assoc]
  simp only [Category.assoc]
  refine congrArg (fun z ↦ (((DerivedCategory.singleFunctors _).functor b).map
    (semilinear ℓ E T m n hmn r))⟦i⟧' ≫ z) ?_
  apply (cancel_mono ((U.mapDerivedCategorySingleFunctor a).hom.app
    (line ℓ E T m r))).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [U.mapDerivedCategorySingleFunctor_hom_app_shiftIso]
  simp only [Iso.inv_hom_id_app_assoc,
    ← (shiftFunctor _ i).map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id, (shiftFunctor _ i).map_id, Category.id_comp]

/-- Strong monoidality extends the rank-one comparison to all nonnegative powers. -/
private theorem sheafMap_isIso [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (r : ℕ) : IsIso (sheafMap ℓ E T m n hmn r) := by
  let φ := coefficientMap (quotient ℓ E m n hmn) T
  let := Mod.extendScalarsOplaxMonoidal φ
  have hroot := rootScalar_isIso ℓ E T m n hmn
  induction r with
  | zero =>
    have he : sheafMap ℓ E T m n hmn 0 = Functor.OplaxMonoidal.η (Mod.extendScalars φ) :=
      (Mod.extendScalarsOplaxMonoidal_η φ).symm
    rw [he]
    exact Mod.isIso_extendScalarsOplaxMonoidal_η φ
  | succ r ih =>
    rw [sheafMap_succ]
    have := Mod.isIso_extendScalarsOplaxMonoidal_δ φ (line ℓ E T n r)
      (coefficientFiniteTwistOne ℓ E T n)
    infer_instance

/-- Flat ordinary lines compute the normalized derived arrow in degree zero. -/
private theorem derivedMap_zero_isIso (m n : ℕ) (hmn : m ≤ n) (r : ℕ)
    (hf : ObjectProperty.flat (line ℓ E T n r))
    [IsIso (sheafMap ℓ E T m n hmn r)] :
    IsIso (derivedMap ℓ E T m n hmn r 0) := by
  let φ := coefficientMap (quotient ℓ E m n hmn) T
  let F := Mod.extendScalars φ
  let U : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (twistFiniteRing ℓ E m) T) ⥤
      Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
        (condensedRingObj (twistFiniteRing ℓ E n) T) := Mod.comap φ
  have ht : ((Mod.extendRestrictAdjunction φ).homEquiv _ _).symm
      (semilinear ℓ E T m n hmn r) = sheafMap ℓ E T m n hmn r := by
    unfold Mod.extendRestrictAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  have : IsIso (((Mod.extendRestrictAdjunction φ).homEquiv _ _).symm
      (semilinear ℓ E T m n hmn r)) := ht.symm ▸ inferInstance
  exact Adjunction.isIso_single_transpose F U (Mod.extendRestrictAdjunction φ)
    (Mod.derivedExtendMapDerivedCategoryAdjunction φ) _ _
    (semilinear ℓ E T m n hmn r) hf

/-- Shift coherence transports the flat comparison to every single degree. -/
private theorem derivedMap_isIso (m n : ℕ) (hmn : m ≤ n) (r : ℕ) (i : ℤ)
    (hf : ObjectProperty.flat (line ℓ E T n r))
    [IsIso (sheafMap ℓ E T m n hmn r)] :
    IsIso (derivedMap ℓ E T m n hmn r i) := by
  have := derivedMap_zero_isIso ℓ E T m n hmn r hf
  have hs := derivedMap_shift ℓ E T m n hmn r (-i) i 0 (by omega)
  have hi : IsIso ((reduction ℓ E T m n hmn).map
      (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (by omega)).hom.app
        (line ℓ E T n r)) ≫ derivedMap ℓ E T m n hmn r i) := by
    rw [hs]
    infer_instance
  exact IsIso.of_isIso_comp_left ((reduction ℓ E T m n hmn).map
    (((DerivedCategory.singleFunctors _).shiftIso (-i) i 0 (neg_add_cancel i)).hom.app
      (line ℓ E T n r))) (derivedMap ℓ E T m n hmn r i)

/-- Native local freeness supplies flatness without assuming flatness of the quotient. -/
private theorem line_flat [∀ x : T, Invertible (ℓ : T.residueField x)] (n r : ℕ) :
    ObjectProperty.flat (line ℓ E T n r) := by
  obtain ⟨L, hL, hfin⟩ := (twist_preserves_native_finiteness ℓ E T).1 n
  have he := congrFun hL (r : ℤ)
  change coefficientTwistNat T _ (coefficientFiniteTwistOne ℓ E T n) r = _ at he
  rw [show line ℓ E T n r = coefficientSignedTwist T _ L (r : ℤ) from he]
  exact (hfin.locallyFree r).flat

/-- The characteristic assumption makes ℓ a unit over the geometric base. -/
private theorem prime_unit (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p) :
    IsUnit (ℓ : D.k) := by
  classical
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let _ : Fact D.p.Prime := ⟨D.prime⟩
  let _ : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  have hunit : IsUnit (ℓ : D.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime D.k₀ (Fact.out : ℓ.Prime) hℓ.symm).isUnit
  simpa only [map_natCast] using hunit.map (algebraMap D.k₀ D.k)

/-- The normalized line isomorphism exists uniquely, with the canonical product,
pullback, shift and equal-level normalizations.

Source: latest blueprint, thm-pur-finite-reduction-of-purity.proof.md, Step 2;
constituent comparison lem-pur-finite-reduction-positive-line-comparison.
(blueprint: lem-pur-finite-reduction-positive-line-comparison).

Proof: by [def-coefficient-twists-detailed] and [def-pur-sheaf-tensor-product],
the root map is additive and balanced. Its scalar adjunct carries
(a e_n) tensor b to bar a b e_m on every compatible primitive-root cover.
Tensor powers give the same rule in degree r, and at r=0 it is coefficient
multiplication. The bases of [det-def-sp-tate-twist-locally-free] identify this
map with A_n tensor A_m -> A_m,
whose inverse sends b to 1 tensor b, so the map is globally invertible.
Uniqueness follows on these bases and then from the sheaf axiom, as in
[lem-sfb-sheaf-cover-local-isomorphism]. The positive lines are locally free,
hence flat; their single complexes are K-flat. Equivalently use
[prop-weil-twist-preserves], [lem-sf-flat-model], and [lem-sf-reduction-flat-model]
for the degree-zero bounded flat models. By [def-weil-derived-tensor] these
compute derived reduction even when the coefficient quotient is not flat.
Consequently the derived scalar adjunction gives exactly the ordinary balanced
map in each degree, and its normalization determines the derived arrow uniquely.
The single-degree identification also follows from
[lem-weil-pbc-derived-single-fully-faithful]. By
[det-prop-sfb-cartesian-coefficients-twists] and
[lem-sfb-kflat-scalar-comparison-normalization], both pullback routes preserve
the roots and send each pure tensor to the same
reduced scalar times the pulled-back generator. Both product routes multiply
the reduced scalars and concatenate the ordered generators. The comparisons
are those of [lem-sfb-ringed-derived-monoidal-comparisons]. Thus the displayed
ordinary squares commute; the same squares represent the derived squares on
these flat single complexes. The single-functor shift isomorphisms give the shift
square. At equal levels the root power is one and the semilinear map is identity
on the underlying abelian sheaf, including r=0 and the empty scheme.
-/
theorem finiteReduction_positiveLineComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hℓ : ℓ ≠ D.p)
    (T : Over (Spec (.of D.k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (m n : ℕ) (hmn : m ≤ n) :
    (∀ (r : ℕ) (i : ℤ), ∃! e :
      (reduction ℓ E T.left m n hmn).obj (single ℓ E T.left n r i) ≅
        single ℓ E T.left m r i,
      Normalized ℓ E T.left m n hmn r i e.hom) ∧
    (∀ r : ℕ, IsIso (sheafMap ℓ E T.left m n hmn r)) ∧
    (∀ r s : ℕ,
      (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) T.left)).map
          (product ℓ E T.left n r s).hom ≫ sheafMap ℓ E T.left m n hmn (r + s) =
        scalarTensor ℓ E T.left m n hmn r s ≫
          (sheafMap ℓ E T.left m n hmn r ⊗ₘ sheafMap ℓ E T.left m n hmn s) ≫
            (product ℓ E T.left m r s).hom) ∧
    (∀ (X : Over (Spec (.of D.k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      (f : X ⟶ T) (r : ℕ),
      (Mod.extendScalars (coefficientMap (quotient ℓ E m n hmn) X.left)).map
          (pull ℓ E T.left f.left n r) ≫ sheafMap ℓ E X.left m n hmn r =
        (CondensedRing.pullIso (quotient ℓ E m n hmn) f.left).hom.app
            (line ℓ E T.left n r) ≫
          (CondensedRing.upperStar (twistFiniteRing ℓ E m) f.left).map
            (sheafMap ℓ E T.left m n hmn r) ≫ pull ℓ E T.left f.left m r) ∧
    (∀ (r : ℕ) (i a b : ℤ) (h : i + a = b),
      (reduction ℓ E T.left m n hmn).map
          (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
            (line ℓ E T.left n r)) ≫ derivedMap ℓ E T.left m n hmn r a =
        ((reduction ℓ E T.left m n hmn).commShiftIso i).hom.app
            (single ℓ E T.left n r b) ≫
          (derivedMap ℓ E T.left m n hmn r b)⟦i⟧' ≫
            (((DerivedCategory.singleFunctors _).shiftIso i a b h).hom.app
              (line ℓ E T.left m r))) ∧
    (∀ r : ℕ, (semilinear ℓ E T.left n n le_rfl r).hom = 𝟙 _) := by
  have : ∀ x : T.left, Invertible (ℓ : T.left.residueField x) := fun x ↦
    (by
      simpa only [map_natCast] using (prime_unit ℓ D hℓ).map
        (T.hom.residueFieldAlgebraMap x) : IsUnit (ℓ : T.left.residueField x)).invertible
  have hsheaf (r : ℕ) := sheafMap_isIso ℓ E T.left m n hmn r
  refine ⟨?_, hsheaf, sheafMap_product ℓ E T.left m n hmn, ?_,
    derivedMap_shift ℓ E T.left m n hmn, semilinear_self ℓ E T.left n⟩
  · intro r i
    have := derivedMap_isIso ℓ E T.left m n hmn r i (line_flat ℓ E T.left n r)
    exact normalized_iso ℓ E T.left m n hmn r i
  · intro X _ _ _ f r
    exact sheafMap_pullback ℓ E T.left f.left m n hmn r

end AlgebraicGeometry.ProEtale.FinitePositiveReduction
