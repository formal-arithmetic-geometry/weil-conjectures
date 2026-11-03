/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.FinitePositiveReduction.FiniteReductionPositiveLineComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistIntegralBasis
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import WeilConjectures.AlgebraicGeometry.FiniteRootPowerTensor

/-! # Finite Kummer level with native condensed coefficients

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
lem-pur-finite-kummer-level.md and lem-pur-finite-kummer-level.proof.md.
(blueprint: lem-pur-finite-kummer-level).
The coefficient rings and finite twist are the current pulled-back condensed constructions.
The comparison is the existing Kummer root-power map, with no choice of frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.FiniteKummer

/-- The specified Kummer comparison from exponent n+1 to exponent N+1.
Source: finite-level comparison and its root-power normalization
(blueprint: lem-pur-finite-kummer-level). -/
def comparison (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n N : ℕ) (h : N ≤ n) :
    coefficientFiniteTwistOne l E T n ⟶ coefficientFiniteRootLine l E T n N :=
  eqToHom (congrArg (coefficientFiniteRootLine l E T n)
    (Nat.add_sub_of_le h).symm) ≫ coefficientFiniteRootComparison l E T n N (n - N)

/-- Pullback of any root presentation with the fixed native finite coefficient ring.
The map is the free-module adjunct of the actual root pullback and then the module adjunct.
Source: root pullback and tensor naturality in the final sentence of the proof
(blueprint: lem-pur-finite-kummer-level). -/
def pull (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {X T : Scheme.{u}} (f : X ⟶ T) (n r : ℕ) :
    (CondensedRing.upperStar (twistFiniteRing l E n) f).obj
      (coefficientFiniteRootLine l E T n r) ⟶ coefficientFiniteRootLine l E X n r :=
  ((CondensedRing.upperStarLowerStarAdjunction (twistFiniteRing l E n) f).homEquiv
    (coefficientFiniteRootLine l E T n r) (coefficientFiniteRootLine l E X n r)).symm
    (((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing l E n) T)).homEquiv
      (rootsOfUnitySheaf T (l ^ (r + 1)))
      ((CondensedRing.lowerStar (twistFiniteRing l E n) f).obj
        (coefficientFiniteRootLine l E X n r))).symm
      (FinitePositiveReduction.rootsDirect T f (l ^ (r + 1)) ≫
        (ProEtale.lowerStar Ab.{u + 1} f).map
          ((Mod.freeForgetAdjunction (condensedRingObj (twistFiniteRing l E n) X)).unit.app
            (rootsOfUnitySheaf X (l ^ (r + 1))))))

private theorem rootsDirect_power {T X : Scheme.{u}} (f : X ⟶ T) (m k : ℕ) :
    rootsOfUnitySheafPow T m k ≫ FinitePositiveReduction.rootsDirect T f m =
      FinitePositiveReduction.rootsDirect T f (k * m) ≫
        (lowerStar Ab.{u + 1} f).map (rootsOfUnitySheafPow X m k) := by
  let G := MorphismProperty.Over.pullback @WeaklyEtale ⊤ f
  have hu (q : ℕ) :
      toSheafify (Scheme.ProEt.topology T) (rootsOfUnityPresheaf T q) ≫
        (FinitePositiveReduction.rootsDirect T f q).hom =
      Functor.whiskerRight (NatTrans.op (FinitePositiveReduction.projection T f))
          (Scheme.Γ ⋙ CommRingCat.rootsOfUnityFunctor q) ≫
        Functor.whiskerLeft G.op
          (toSheafify (Scheme.ProEt.topology X) (rootsOfUnityPresheaf X q)) := by
    change (sheafificationAdjunction (Scheme.ProEt.topology T) Ab.{u + 1}).homEquiv
      _ _ (FinitePositiveReduction.rootsDirect T f q) = _
    simp only [FinitePositiveReduction.rootsDirect, Equiv.apply_symm_apply]
    rfl
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (Scheme.ProEt.topology T) _ _
    ((lowerStar Ab.{u + 1} f).obj (rootsOfUnitySheaf X m)).property
  change toSheafify (Scheme.ProEt.topology T) (rootsOfUnityPresheaf T (k * m)) ≫
      sheafifyMap (Scheme.ProEt.topology T)
        (Functor.whiskerLeft ((Scheme.ProEt.forget T ⋙ Over.forget T).op ⋙ Scheme.Γ)
          (CommRingCat.rootsOfUnityPow m k)) ≫ _ = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  erw [hu m]
  change _ = (toSheafify (Scheme.ProEt.topology T)
    (rootsOfUnityPresheaf T (k * m)) ≫
      (FinitePositiveReduction.rootsDirect T f (k * m)).hom) ≫ _
  rw [hu (k * m)]
  apply NatTrans.ext
  funext U
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc]
  change _ ≫ _ ≫ (toSheafify (Scheme.ProEt.topology X)
      (rootsOfUnityPresheaf X m)).app (G.op.obj U) =
    _ ≫ (toSheafify (Scheme.ProEt.topology X)
      (rootsOfUnityPresheaf X (k * m))).app (G.op.obj U) ≫
      (sheafifyMap (Scheme.ProEt.topology X)
        (Functor.whiskerLeft ((Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ)
          (CommRingCat.rootsOfUnityPow m k))).app (G.op.obj U)
  rw [← NatTrans.comp_app, ← toSheafify_naturality]
  have hh := congrArg (fun z ↦ z ≫ (toSheafify (Scheme.ProEt.topology X)
    (rootsOfUnityPresheaf X m)).app (G.op.obj U))
      ((CommRingCat.rootsOfUnityPow m k).naturality
        (Scheme.Γ.map ((FinitePositiveReduction.projection T f).app U.unop).op)).symm
  dsimp only [rootsOfUnityPresheaf, Functor.comp_obj, Functor.comp_map,
    Functor.whiskerLeft_app, NatTrans.op_app] at hh ⊢
  exact hh

private theorem rootsDirect_power_reindex {T X : Scheme.{u}} (f : X ⟶ T)
    (a b k : ℕ) (h : a = k * b) :
    (eqToHom (congrArg (rootsOfUnitySheaf T) h) ≫ rootsOfUnitySheafPow T b k) ≫
        FinitePositiveReduction.rootsDirect T f b =
      FinitePositiveReduction.rootsDirect T f a ≫ (lowerStar Ab.{u + 1} f).map
        (eqToHom (congrArg (rootsOfUnitySheaf X) h) ≫ rootsOfUnitySheafPow X b k) := by
  subst a
  simpa only [eqToHom_refl, Category.id_comp] using rootsDirect_power f b k

private theorem pull_free_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T X : Scheme.{u}} (f : X ⟶ T) (n r s : ℕ)
    (vT : rootsOfUnitySheaf T (l ^ (r + 1)) ⟶ rootsOfUnitySheaf T (l ^ (s + 1)))
    (vX : rootsOfUnitySheaf X (l ^ (r + 1)) ⟶ rootsOfUnitySheaf X (l ^ (s + 1)))
    (hv : vT ≫ FinitePositiveReduction.rootsDirect T f (l ^ (s + 1)) =
      FinitePositiveReduction.rootsDirect T f (l ^ (r + 1)) ≫
        (lowerStar Ab.{u + 1} f).map vX) :
    (CondensedRing.upperStar (twistFiniteRing l E n) f).map
        ((Mod.freeFunctor _).map vT) ≫ pull l E f n s =
      pull l E f n r ≫ (Mod.freeFunctor _).map vX := by
  let R := condensedRingObj (twistFiniteRing l E n) T
  let S := condensedRingObj (twistFiniteRing l E n) X
  let A := CondensedRing.upperStarLowerStarAdjunction (twistFiniteRing l E n) f
  let B := Mod.freeForgetAdjunction R
  let C := Mod.freeForgetAdjunction S
  let g : rootsOfUnitySheaf T (l ^ (s + 1)) ⟶ (Mod.forget R).obj
      ((CondensedRing.lowerStar (twistFiniteRing l E n) f).obj
        ((Mod.free S).obj (rootsOfUnitySheaf X (l ^ (s + 1))))) :=
    FinitePositiveReduction.rootsDirect T f (l ^ (s + 1)) ≫
    (lowerStar Ab.{u + 1} f).map (C.unit.app (rootsOfUnitySheaf X (l ^ (s + 1))))
  let h : rootsOfUnitySheaf T (l ^ (r + 1)) ⟶ (Mod.forget R).obj
      ((CondensedRing.lowerStar (twistFiniteRing l E n) f).obj
        ((Mod.free S).obj (rootsOfUnitySheaf X (l ^ (r + 1))))) :=
    FinitePositiveReduction.rootsDirect T f (l ^ (r + 1)) ≫
    (lowerStar Ab.{u + 1} f).map (C.unit.app (rootsOfUnitySheaf X (l ^ (r + 1))))
  let L := lowerStar Ab.{u + 1} f
  let d (j : ℕ) := FinitePositiveReduction.rootsDirect T f (l ^ (j + 1))
  let unitMap (j : ℕ) := C.unit.app (rootsOfUnitySheaf X (l ^ (j + 1)))
  let w := (Mod.forget S).map ((Mod.free S).map vX)
  have hn : vX ≫ unitMap s = unitMap r ≫ w := C.unit.naturality vX
  have hb : vT ≫ g = h ≫ (Mod.forget R).map
      ((CondensedRing.lowerStar (twistFiniteRing l E n) f).map ((Mod.free S).map vX)) := by
    change vT ≫ (d s ≫ L.map (unitMap s)) = (d r ≫ L.map (unitMap r)) ≫ L.map w
    calc
      vT ≫ (d s ≫ L.map (unitMap s)) = (vT ≫ d s) ≫ L.map (unitMap s) :=
        (Category.assoc _ _ _).symm
      _ = (d r ≫ L.map vX) ≫ L.map (unitMap s) :=
        congrArg (fun z ↦ z ≫ L.map (unitMap s)) hv
      _ = d r ≫ L.map (vX ≫ unitMap s) := by rw [L.map_comp, Category.assoc]
      _ = d r ≫ L.map (unitMap r ≫ w) := congrArg (fun z ↦ d r ≫ L.map z) hn
      _ = (d r ≫ L.map (unitMap r)) ≫ L.map w := by rw [L.map_comp, Category.assoc]
  have hc := B.homEquiv_naturality_right_square vT g h
    ((CondensedRing.lowerStar (twistFiniteRing l E n) f).map ((Mod.free S).map vX)) hb
  have hd := A.homEquiv_naturality_right_square ((Mod.free R).map vT)
    ((B.homEquiv _ _).symm g) ((B.homEquiv _ _).symm h)
    ((Mod.free S).map vX) hc
  exact hd

private theorem finiteRing_killed (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n N : ℕ)
    (ha : (l ^ (N + 1) : Padic.coefficientExtensionRing l E (n + 1)) = 0) :
    l ^ (N + 1) • 𝟙 (condensedRingObj (twistFiniteRing l E n) T) = 0 := by
  let : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let : DiscreteTopology (Padic.coefficientExtensionRing l E (n + 1)) := ⟨rfl⟩
  have hp : l ^ (N + 1) • 𝟙 (twistFiniteRing l E n) = 0 := by
    apply Sheaf.hom_ext
    ext V f
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    change l ^ (N + 1) • _ = (0 : Padic.coefficientExtensionRing l E (n + 1))
    rw [nsmul_eq_mul, Nat.cast_pow, ha, zero_mul]
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint T) :=
    adj.leftAdjoint_preservesColimits
  have : PreservesBinaryBiproducts (upperStarFromPoint T) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (upperStarFromPoint T).Additive := Functor.additive_of_preservesBinaryBiproducts _
  change l ^ (N + 1) • 𝟙 ((upperStarFromPoint T).obj (twistFiniteRing l E n)) = 0
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hp, Functor.map_zero]

private theorem comparison_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n N : ℕ)
    (h : N ≤ n) (hT : ∀ x : T, IsUnit (l : T.presheaf.stalk x))
    (ha : (l ^ (N + 1) : Padic.coefficientExtensionRing l E (n + 1)) = 0) :
    IsIso (comparison l E T n N h) := by
  have hl : IsUnit (l : Γ(T, ⊤)) := by
    apply T.toRingedSpace.isUnit_of_isUnit_germ ⊤ _
    intro x hx
    simpa only [map_natCast] using hT x
  let R := condensedRingObj (twistFiniteRing l E n) T
  have hm : n + 1 = (N + 1) + (n - N) := by omega
  have hi := free_rootPower_isIso T l hl R (n + 1) N (n - N) hm
    (finiteRing_killed l E T n N ha)
  have he : comparison l E T n N h =
      (Mod.freeFunctor R).map
        (eqToHom (by rw [hm, ← pow_add]; congr 2; omega :
          rootsOfUnitySheaf T (l ^ (n + 1)) =
            rootsOfUnitySheaf T (l ^ (n - N) * l ^ (N + 1))) ≫
          rootsOfUnitySheafPow T (l ^ (N + 1)) (l ^ (n - N))) := by
    simp only [comparison, coefficientFiniteRootComparison, Functor.map_comp,
      eqToHom_map, eqToHom_trans_assoc]
    rfl
  rw [he]
  exact hi

private theorem kummer_finite_basis (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (n N : ℕ)
    (hn : P.level = n + 1) (hN : P.kummerLevel = N + 1)
    (a : ZMod (P.coefficients.l ^ (N + 1)) →+*
      Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) :
    ∃ f : ℕ,
      Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
        P.coefficients.l ^ f ∧
      ∃ b : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) ≃+
          (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
        ∀ (z : ZMod (P.coefficients.l ^ (N + 1)))
          (x : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)),
          b (a z * x) = z • b x := by
  obtain ⟨f, d, hf, hd, ⟨b⟩⟩ := kummer_basis_rank P
  subst d
  obtain ⟨q⟩ := finite_basis_quotient P.coefficients.l P.extension _ b (N + 1)
  have hI : Padic.coefficientExtensionIdeal P.coefficients.l P.extension (n + 1) =
      Ideal.span {((P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension) ^ (N + 1))} := by
    rw [← hn]
    simpa only [exponent, hN, Nat.cast_pow] using kummer_ideal P h
  let e := (Ideal.quotEquivOfEq hI).toAddEquiv.trans q
  refine ⟨f, hf, e, ?_⟩
  intro z x
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← zsmul_eq_mul, map_zsmul, Int.cast_smul_eq_zsmul]

private theorem kummer_basis_rank (P : PurityFiniteSetting.{u}) :
    ∃ f d : ℕ,
      Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
        P.coefficients.l ^ f ∧
      d = P.ramificationIndex * f ∧
      Nonempty (@Module.Basis (Fin d) ℤ_[P.coefficients.l]
        (Padic.coefficientExtensionIntegers P.coefficients.l P.extension) _ _
        (Module.compHom _ (Scheme.purTwistIntegersMap P.coefficients.l P.extension))) := by
  classical
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have hO := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hO.2.2.2.1
  have : IsDiscreteValuationRing O := hO.2.2.2.2.2.2.2.1
  have : m.IsMaximal := hO.2.2.2.2.1
  have : Finite (O ⧸ m) := hO.2.2.2.2.2.2.2.2.2.2.2.1
  let : Fintype (O ⧸ m) := Fintype.ofFinite _
  have hl : (l : O ⧸ m) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    apply (hO.2.1 (l : O)).mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  let : Field (O ⧸ m) := Ideal.Quotient.field m
  have : CharP (O ⧸ m) l := (CharP.charP_iff_prime_eq_zero
    (Fact.out : l.Prime)).mpr hl
  obtain ⟨f, _, hf⟩ := FiniteField.card (O ⧸ m) l
  have hf' : Nat.card (Padic.coefficientExtensionResidueField l E) = l ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hf
  obtain ⟨d, ⟨b⟩⟩ := Scheme.purTwistIntegralBasis l E
  obtain ⟨q⟩ := finite_basis_quotient l E d b 1
  have hcard : Nat.card (O ⧸ Ideal.span {(l : O)}) = l ^ d := by
    simpa only [pow_one, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
      Nat.card_congr q.toEquiv
  have hgen : Ideal.span ({π} : Set O) = m :=
    hO.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hI : Ideal.span {(l : O)} = m ^ P.ramificationIndex := by
    rw [← hgen, Ideal.span_singleton_pow]
    exact Ideal.span_singleton_eq_span_singleton.mpr (kummer_prime_power P).2
  have hp : m.IsPrime := inferInstance
  have hc := cardQuot_pow_of_prime (P := m) hO.2.2.2.2.2.2.2.2.2.1
    (i := P.ramificationIndex)
  simp only [Submodule.cardQuot_apply] at hc
  rw [← hI, hcard, hf', ← pow_mul] at hc
  have hd : d = P.ramificationIndex * (f : ℕ) := by
    simpa only [Nat.mul_comm] using
      Nat.pow_right_injective (Fact.out : l.Prime).two_le hc
  exact ⟨f, d, hf', hd, ⟨b⟩⟩

private theorem finite_basis_quotient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : ℕ) (b : @Module.Basis (Fin d) ℤ_[l]
      (Padic.coefficientExtensionIntegers l E) _ _
      (Module.compHom _ (Scheme.purTwistIntegersMap l E))) (r : ℕ) :
    Nonempty ((Padic.coefficientExtensionIntegers l E ⧸
      Ideal.span {((l : Padic.coefficientExtensionIntegers l E) ^ r)}) ≃+
        (Fin d → ZMod (l ^ r))) := by
  classical
  let O := Padic.coefficientExtensionIntegers l E
  let : Algebra ℤ_[l] O := (Scheme.purTwistIntegersMap l E).toAlgebra
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ r}
  let J : Ideal O := Ideal.span {(l : O) ^ r}
  let M : Submodule ℤ_[l] O := J.restrictScalars ℤ_[l]
  let B : Submodule ℤ_[l] (Fin d → ℤ_[l]) := Submodule.pi Set.univ fun _ ↦ I
  have hm : M.map b.equivFun.toLinearMap = B := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ∀ i, i ∈ Set.univ → b.equivFun y i ∈ I
      intro i _
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
      have hs : ((l : ℤ_[l]) ^ r) • z = (l : O) ^ r * z := by
        rw [Algebra.smul_def, map_pow, map_natCast]
      rw [← hs]
      rw [map_smul]
      exact Ideal.mem_span_singleton.mpr ⟨b.equivFun z i, rfl⟩
    · intro hx
      have hx' : ∀ i, ((l : ℤ_[l]) ^ r) ∣ x i := by
        intro i
        exact Ideal.mem_span_singleton.mp (hx i (Set.mem_univ _))
      choose y hy using hx'
      refine ⟨((l : ℤ_[l]) ^ r) • b.equivFun.symm y, ?_, ?_⟩
      · change ((l : ℤ_[l]) ^ r) • b.equivFun.symm y ∈ J
        apply Ideal.mem_span_singleton.mpr
        refine ⟨b.equivFun.symm y, ?_⟩
        rw [Algebra.smul_def, map_pow, map_natCast]
      · rw [map_smul]
        change ((l : ℤ_[l]) ^ r) • b.equivFun (b.equivFun.symm y) = x
        rw [LinearEquiv.apply_symm_apply]
        exact funext fun i ↦ (hy i).symm
  let e : (O ⧸ M) ≃ₗ[ℤ_[l]] ((Fin d → ℤ_[l]) ⧸ B) :=
    Submodule.Quotient.equiv M B b.equivFun hm
  let e' : (O ⧸ M) ≃ₗ[ℤ_[l]] (Fin d → ℤ_[l] ⧸ I) :=
    e.trans (Submodule.quotientPi fun _ : Fin d ↦ I)
  let q : ℤ_[l] ⧸ I ≃+* ZMod (l ^ r) :=
    (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow r).symm).trans
      ((PadicInt.toZModPow r).quotientKerEquivOfSurjective (ZMod.ringHom_surjective _))
  exact ⟨e'.toAddEquiv.trans (AddEquiv.piCongrRight fun _ ↦ q.toAddEquiv)⟩

private theorem kummer_quotient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    ∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set _)),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set _)) x := by
  exact ⟨Ideal.quotEquivOfEq (kummer_ideal P h), fun _ ↦ rfl⟩

private theorem kummer_minimal (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (j : ℕ)
    (hj : ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0) : P.kummerLevel ≤ j := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  have hdvr := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := hdvr.2.2.2.1
  have : IsDiscreteValuationRing O := hdvr.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = Padic.coefficientExtensionMaximalIdeal l E :=
    hdvr.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  change ((l ^ j : ℕ) : O ⧸ Padic.coefficientExtensionIdeal l E P.level) = 0 at hj
  rw [← map_natCast (Ideal.Quotient.mk
    (Padic.coefficientExtensionIdeal l E P.level)), Ideal.Quotient.eq_zero_iff_mem] at hj
  change ((l ^ j : ℕ) : O) ∈ Ideal.span {π} ^ P.level at hj
  rw [Nat.cast_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hj
  have hd : π ^ P.level ∣ π ^ (P.ramificationIndex * j) := by
    rw [pow_mul]
    exact (Associated.pow_pow (n := j) (kummer_prime_power P).2).dvd_iff_dvd_right.mp hj
  have he := (kummer_prime_power P).1
  have hn := (kummer_positive P h).2
  have := (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).mp hd
  nlinarith

private theorem kummer_log_uniformizer (P : PurityFiniteSetting.{u}) :
    -Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹ := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hp : 1 < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl : Real.log (l : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  obtain ⟨he, v, hv⟩ := kummer_prime_power P
  have hv1 : abv ((v : O) : E) = 1 := (h.2.2.1 (v : O)).mp v.isUnit
  have hval := congrArg (fun x : O ↦ abv (x : E)) hv
  simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_pow, map_mul,
    map_pow, hv1, mul_one] at hval
  have hlog := congrArg Real.log hval
  rw [Real.log_pow] at hlog
  have hnorm : abv (l : E) = (l : ℝ)⁻¹ := by
    change spectralNorm ℚ_[l] E (l : E) = _
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E), Padic.norm_p]
  rw [hnorm, Real.log_inv] at hlog
  have he' : (P.ramificationIndex : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  change -Real.log (abv (π : E)) / Real.log (l : ℝ) = _
  field_simp
  nlinarith

private theorem kummer_log_prime (P : PurityFiniteSetting.{u}) :
    -Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1 := by
  have hp : 1 < (P.coefficients.l : ℝ) := by
    exact_mod_cast (Fact.out : P.coefficients.l.Prime).one_lt
  have hl : Real.log (P.coefficients.l : ℝ) ≠ 0 := (Real.log_pos hp).ne'
  have ha : Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension) = (P.coefficients.l : ℝ)⁻¹ := by
    change spectralNorm ℚ_[P.coefficients.l] P.extension (P.coefficients.l : P.extension) = _
    rw [← map_natCast (algebraMap ℚ_[P.coefficients.l] P.extension),
      spectralNorm_extends (K := ℚ_[P.coefficients.l]) (L := P.extension), Padic.norm_p]
  rw [ha, Real.log_inv, neg_neg, div_self hl]

private theorem kummer_ideal (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set _) := by
  have hn := (kummer_positive P h).2
  change Ideal.span {Padic.coefficientExtensionUniformizer P.coefficients.l P.extension} ^
    P.level = Ideal.span {((P.coefficients.l ^ P.kummerLevel : ℕ) :
      Padic.coefficientExtensionIntegers P.coefficients.l P.extension)}
  rw [Nat.cast_pow, hn, pow_mul, Ideal.span_singleton_pow,
    Ideal.span_singleton_pow]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    (Associated.pow_pow (n := P.kummerLevel) (kummer_prime_power P).2).symm

private theorem kummer_positive (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧ P.level = P.ramificationIndex * P.kummerLevel := by
  have he := (kummer_prime_power P).1
  have hn : P.level = P.ramificationIndex * P.kummerLevel :=
    (Nat.mul_div_cancel' h).symm
  exact ⟨by have := P.level_pos; nlinarith [hn], hn⟩

private theorem kummer_prime_power (P : PurityFiniteSetting.{u}) :
    0 < P.ramificationIndex ∧
      Associated (P.coefficients.l : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension ^
          P.ramificationIndex) := by
  let l := P.coefficients.l
  let E := P.extension
  let O := Padic.coefficientExtensionIntegers l E
  let m := Padic.coefficientExtensionMaximalIdeal l E
  let π := Padic.coefficientExtensionUniformizer l E
  let abv := Padic.coefficientExtensionAbsoluteValue l E
  have h := (Padic.extension_integers_dvr l E abv
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsLocalRing O := h.2.2.2.1
  have : IsDiscreteValuationRing O := h.2.2.2.2.2.2.2.1
  have hπ : Ideal.span ({π} : Set O) = m :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : IsLocalRing.maximalIdeal O = m :=
    h.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal O)
  have hirr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr (hm.trans hπ.symm)
  have : CharZero E := charZero_of_injective_algebraMap
    (algebraMap ℚ_[l] E).injective
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hsmall : abv (l : E) < 1 := by
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E),
      spectralNorm_extends (K := ℚ_[l]) (L := E)]
    exact Padic.norm_p_lt_one
  have hnonunit : ¬IsUnit (l : O) := by
    intro hu
    exact (ne_of_lt hsmall) ((h.2.2.1 (l : O)).mp hu)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hirr
  have heq : P.ramificationIndex = e := by
    change (emultiplicity π (l : O)).toNat = e
    rw [emultiplicity_eq_of_associated_right he,
      emultiplicity_pow_self hirr.ne_zero hirr.not_isUnit, ENat.toNat_natCast]
  rw [heq]
  refine ⟨Nat.pos_of_ne_zero ?_, he⟩
  intro he0
  apply hnonunit
  exact he.isUnit_iff.mpr (by simp [he0])

end AlgebraicGeometry.ProEtale.FiniteKummer

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry.ProEtale.FiniteKummer

/-- The arithmetic level and canonical finite Kummer isomorphism, with derived tensor and
arbitrary base change compatibility.

Source: latest blueprint `lem-pur-finite-kummer-level`, statement and companion proof.
Proof (blueprint steps 1--6):
(1) In the DVR write l = u*pi_E^e with u a unit. Applying the normalized valuation gives
v_l(pi_E)=1/e. Since the divisibility hypothesis gives n=e*N, positivity gives N≥1 and
(pi_E^n)=(l^N); moreover l^j belongs to (pi_E^n) exactly when e*j≥n, proving minimality.
(2) Choose an integral basis of size d. Reduction modulo l^N gives A ≅ (Z/l^N)^d.
At N=1, cardinalities of the residue quotient and the maximal-ideal filtration give
d=e*f, hence the displayed finite-free additive presentation and its scalar equation.
(3) On a compatible-root cover, the root-power diagram is the constant cyclic-residue
diagram. The cyclic group Z/l^j is the cokernel of l^j on Z. Constant sheaves and
free coefficient modules preserve this cokernel; when l^j kills the coefficient ring,
its quotient arrow is an isomorphism. The commuting integer-reduction triangle then
makes the specified transition from level n+1 to N+1 invertible after tensoring.
(4) Free modules commute with inverse image by uniqueness of left adjoints. Conservative
covering restrictions descend the preceding isomorphism. Its equality transports are
exactly those in `comparison`; no choice of frame defines the comparison itself.
This is the finite-stage cyclic presentation of the blueprint's tensor-cokernel argument.
(5) The single-degree derived embedding and tensor-with-K functor preserve this isomorphism.
(6) Before sheafification, root pullback commutes with powers by naturality of the power
map. Naturality of the sheafification unit extends this square to sheaves. Transfer it
through the free-module and module-pullback adjunctions to obtain exactly the displayed
base-change equation. Equality induction handles its root-index transports.
(blueprint: lem-pur-finite-kummer-level).
-/
theorem finiteKummerLevel_condensed (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) :
    1 ≤ P.kummerLevel ∧
    P.level = P.ramificationIndex * P.kummerLevel ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (P.coefficients.l : P.extension)) / Real.log P.coefficients.l = 1) ∧
    (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
      (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
        Real.log P.coefficients.l = (P.ramificationIndex : ℝ)⁻¹) ∧
    (P.level : ℝ) *
      (-Real.log (Padic.coefficientExtensionAbsoluteValue P.coefficients.l P.extension
        (Padic.coefficientExtensionUniformizer P.coefficients.l P.extension).val) /
          Real.log P.coefficients.l) = P.kummerLevel ∧
    Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level =
      Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
        P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)) ∧
    (∃ r : P.Ring ≃+* (Padic.coefficientExtensionIntegers P.coefficients.l P.extension ⧸
        Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))),
      ∀ x : Padic.coefficientExtensionIntegers P.coefficients.l P.extension,
        r (Ideal.Quotient.mk
          (Padic.coefficientExtensionIdeal P.coefficients.l P.extension P.level) x) =
        Ideal.Quotient.mk (Ideal.span ({(P.exponent : Padic.coefficientExtensionIntegers
          P.coefficients.l P.extension)} : Set (Padic.coefficientExtensionIntegers
            P.coefficients.l P.extension))) x) ∧
    (P.exponent : P.Ring) = 0 ∧
    (∀ j : ℕ, ((P.coefficients.l ^ j : ℕ) : P.Ring) = 0 → P.kummerLevel ≤ j) ∧
    ∀ n : ℕ, P.level = n + 1 →
      ∃ N : ℕ, P.kummerLevel = N + 1 ∧
        ∃ a : ZMod (P.coefficients.l ^ (N + 1)) →+*
            Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1),
          ∃ f : ℕ,
            Nat.card (Padic.coefficientExtensionResidueField P.coefficients.l P.extension) =
              P.coefficients.l ^ f ∧
            (∃ b : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) ≃+
                (Fin (P.ramificationIndex * f) → ZMod (P.coefficients.l ^ (N + 1))),
              ∀ (z : ZMod (P.coefficients.l ^ (N + 1)))
                (x : Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)),
                b (a z * x) = z • b x) ∧
            ∃ hNn : N ≤ n,
              (∀ (T : Scheme.{u})
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x)),
                IsIso (comparison P.coefficients.l P.extension T n N hNn) ∧
                ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
                    (condensedRingObj (twistFiniteRing P.coefficients.l P.extension n) T)),
                  IsIso (((CondensedRing.derivedTensor
                    (twistFiniteRing P.coefficients.l P.extension n) T).obj K).map
                      ((DerivedCategory.singleFunctor _ 0).map
                        (comparison P.coefficients.l P.extension T n N hNn)))) ∧
              (∀ (T X : Scheme.{u}) (f : X ⟶ T)
                (_hT : ∀ x : T, IsUnit (P.coefficients.l : T.presheaf.stalk x))
                (_hX : ∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x)),
                (CondensedRing.upperStar
                  (twistFiniteRing P.coefficients.l P.extension n) f).map
                    (comparison P.coefficients.l P.extension T n N hNn) ≫
                      pull P.coefficients.l P.extension f n N =
                  pull P.coefficients.l P.extension f n n ≫
                    comparison P.coefficients.l P.extension X n N hNn) := by
  classical
  have hp := kummer_positive P h
  have hz : (P.exponent : P.Ring) = 0 := by
    exact congrArg ULift.down (P.exponent_coefficient_eq_zero h)
  refine ⟨hp.1, hp.2, kummer_log_prime P, kummer_log_uniformizer P, ?_,
    kummer_ideal P h, kummer_quotient P h, hz, kummer_minimal P h, ?_⟩
  · rw [kummer_log_uniformizer]
    have he : (P.ramificationIndex : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (kummer_prime_power P).1)
    have hlevel : (P.level : ℝ) = P.ramificationIndex * P.kummerLevel := by
      exact_mod_cast hp.2
    rw [hlevel]
    field_simp
  · intro n hn
    obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : P.kummerLevel ≠ 0)
    have ha : ((P.coefficients.l ^ (N + 1) : ℕ) :
        Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1)) = 0 := by
      rw [← hn]
      simpa only [exponent, hN] using hz
    let a : ZMod (P.coefficients.l ^ (N + 1)) →+*
        Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1) :=
      ZMod.castHom (ringChar.dvd ha) _
    obtain ⟨f, hf, b, hb⟩ := kummer_finite_basis P h n N hn hN a
    have hNn : N ≤ n := by
      have he := (kummer_prime_power P).1
      rw [hN, hn] at hp
      nlinarith [hp.2]
    refine ⟨N, hN, a, f, hf, ⟨b, hb⟩, hNn, ?_, ?_⟩
    · intro T hT
      have hi := comparison_isIso P.coefficients.l P.extension T n N hNn hT
        (by simpa only [Nat.cast_pow] using ha)
      exact ⟨hi, fun K ↦ by infer_instance⟩
    · intro T X f hT hX
      have hi : P.coefficients.l ^ (n + 1) =
          P.coefficients.l ^ (n - N) * P.coefficients.l ^ (N + 1) := by
        rw [← pow_add]
        congr 1
        omega
      let v (Y : Scheme.{u}) :=
        eqToHom (congrArg (ProEtale.rootsOfUnitySheaf Y) hi) ≫
          rootsOfUnitySheafPow Y (P.coefficients.l ^ (N + 1))
            (P.coefficients.l ^ (n - N))
      have hc (Y : Scheme.{u}) : comparison P.coefficients.l P.extension Y n N hNn =
          (Mod.freeFunctor _).map (v Y) := by
        simp only [comparison, coefficientFiniteRootComparison, v, Functor.map_comp,
          eqToHom_map, eqToHom_trans_assoc]
      rw [hc T, hc X]
      exact pull_free_naturality P.coefficients.l P.extension f n n N (v T) (v X)
        (rootsDirect_power_reindex f _ _ _ hi)

end WeilConjectures.PurityFiniteSetting
