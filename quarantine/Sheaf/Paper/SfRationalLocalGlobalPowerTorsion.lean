/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.IntegralReductionTowerUnrestricted
public import Sheaf.Paper.IntegralConstructibleLinear
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.CategoryTheory.ScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Finite-cover scalar localization gives uniform power torsion

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
  sk-prop-sf-dualizable-biduality/_section.md, proof paragraph “Choose locally a
  bounded complex” and the extracted finite-cover uniform-power argument
  (blueprint: lem-sf-rational-local-global-power-torsion).

The local scalar-localization hypothesis is stated in the slice category of the
small pro-etale site.  Cohomology is expressed by the derived homology functor;
its image of the canonical scalar endomorphism is the stated scalar action on
the cohomology sheaf.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace WeilConjectures

/-- Abelian sheafification on the small pro-etale site, in a coefficient size containing
the site (`max u (t + 1)`). Source: Stacks Tag 03DA
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSiteHasSheafify (X : AlgebraicGeometry.Scheme.{t}) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion on the small pro-etale site.
Source: Stacks Tag 03DA (blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSiteLocallyBijective (X : AlgebraicGeometry.Scheme.{t}) :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} X.ProEt := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Abelian sheafification on a pro-etale slice, in a coefficient size containing the
site (`max u (t + 1)`), so the scheme and coefficient universes stay independent.
Source: Stacks Tag 03DA (blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceHasSheafify
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    HasSheafify ((AlgebraicGeometry.Scheme.ProEt.topology X).over U)
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  hasSheafifyEssentiallySmallSite _ _

/-- The locally bijective sheafification criterion on a pro-etale slice, in the same
coefficient size. Source: Stacks Tag 03DA
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceLocallyBijective
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    ((AlgebraicGeometry.Scheme.ProEt.topology X).over U).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} :=
  letI : EssentiallySmall.{max u (t + 1)} (Over U) := essentiallySmallSelf _
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Slice restriction of completed-coefficient modules is additive; first component of
the recorded exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverAdditive
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U).Additive :=
  (ringedOverFunctor_exactGeneral _ U).1

/-- Slice restriction preserves finite limits; second component of the recorded
exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverFiniteLimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U) :=
  (ringedOverFunctor_exactGeneral _ U).2.1

/-- Slice restriction preserves finite colimits; third component of the recorded
exactness theorem. Source: Stacks Section 03DH
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalOverFiniteColimits
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{max u (t + 1)}
      (completedIntegralCoefficientSheafUnrestricted l E X) U) :=
  (ringedOverFunctor_exactGeneral _ U).2.2

/-- The standard derived localization of modules on a slice. Source: Stacks Tag 05RU
(blueprint: lem-sf-rational-local-global-power-torsion). -/
noncomputable instance sfRationalSliceHasDerivedCategory
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t}) (U : AlgebraicGeometry.Scheme.ProEt X) :
    HasDerivedCategory
      (SheafOfModules.{max u (t + 1)}
        ((completedIntegralCoefficientSheafUnrestricted l E X).over U)) :=
  HasDerivedCategory.standard _

private theorem sfHomology_additive
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A] (d : ℤ) :
    (DerivedCategory.homologyFunctor A d).Additive := by
  have : (DerivedCategory.Qh ⋙ DerivedCategory.homologyFunctor A d).Additive :=
    Functor.additive_of_iso (DerivedCategory.homologyFunctorFactorsh A d).symm
  exact (Localization.functor_additive_iff DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _).mpr inferInstance

private theorem sfScalarLocalization_power
    {R : Type*} [CommRing R] {A : Type*} [Category A] [Preadditive A] [Linear R A]
    (p : R) (K : A)
    (hK : IsZero ((ScalarLocalization.localization R A p).obj K)) :
    ∃ a : ℕ, p ^ a • 𝟙 K = 0 := by
  have h : (TensorProduct.mk R (Localization.Away p) (K ⟶ K) 1) (𝟙 K) = 0 :=
    hK.eq_of_src _ _
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers p)
    (TensorProduct.mk R (Localization.Away p) (K ⟶ K) 1)).mp h
  obtain ⟨k, hk⟩ := a.property
  refine ⟨k, ?_⟩
  change (a : R) • 𝟙 K = 0 at ha
  simpa only [← hk] using ha

private theorem sfUniformizer_prime_factorization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    ∃ (e : ℕ) (v : (Padic.coefficientExtensionIntegers l E)ˣ),
      0 < e ∧ (l : Padic.coefficientExtensionIntegers l E) =
        (v : Padic.coefficientExtensionIntegers l E) *
          Padic.coefficientExtensionUniformizer l E ^ e := by
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  have H := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  rcases H with ⟨hO, hm, hu, hlocal, hmax, hmax_unique, hfrac, hdvr, hpid, hm0,
    hprime, hfinite, hr, hgen, hassoc, hfactor⟩
  let : IsLocalRing R := hlocal
  let : IsDiscreteValuationRing R := hdvr
  have hp : Ideal.span ({p} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hgen.choose_spec
  have hm' : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal R :=
    (hmax_unique _ (IsLocalRing.maximalIdeal.isMaximal R)).symm
  have hpirr : Irreducible p :=
    IsDiscreteValuationRing.irreducible_iff_uniformizer p |>.mpr (hp.trans hm').symm
  have hl0 : (l : R) ≠ 0 := by
    intro h
    have h' : (l : E) = 0 := congrArg (fun x : R ↦ (x : E)) h
    have hq : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    apply hq
    apply (algebraMap ℚ_[l] E).injective
    simpa using h'
  have hlval : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    have h := spectralNorm_extends (K := ℚ_[l]) (L := E) (l : ℚ_[l])
    change spectralNorm ℚ_[l] E (l : E) < 1
    simpa using h.trans_lt (Padic.norm_p_lt_one (p := l))
  have hlnu : ¬ IsUnit (l : R) := by
    intro h
    exact (ne_of_lt hlval) ((hu (l : R)).mp h)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hpirr
  refine ⟨e, v, ?_, hv⟩
  by_contra he
  have he : e = 0 := by omega
  apply hlnu
  rw [hv, he, pow_zero, mul_one]
  exact v.isUnit

private theorem sfPower_smul_zero_of_le
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (p : R) {a b : ℕ} (hab : a ≤ b) {x : M} (hx : p ^ a • x = 0) :
    p ^ b • x = 0 := by
  rw [← Nat.sub_add_cancel hab, pow_add, mul_smul, hx, smul_zero]

private theorem sfSheaf_map_zero_of_cover
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms B]
    {J : GrothendieckTopology A} {I : Type*} {U : I → A} (hU : J.CoversTop U)
    {M N : Sheaf J B} (f : M ⟶ N)
    (hf : ∀ j, (J.overPullback B (U j)).map f = 0) : f = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply N.property.hom_ext (hU.cover V.unop)
  intro T
  obtain ⟨j, ⟨g⟩⟩ := T.hf
  have h := congrArg (fun z ↦ z.hom.app (Opposite.op (Over.mk g))) (hf j)
  change f.hom.app (Opposite.op T.Y) = 0 at h
  rw [← f.hom.naturality]
  simp [h]

private theorem sfModule_map_zero_of_cover
    {A : Type*} [Category A] {J : GrothendieckTopology A}
    (S : Sheaf J RingCat.{u}) {I : Type*} {U : I → A} (hU : J.CoversTop U)
    {M N : SheafOfModules.{u} S} (f : M ⟶ N)
    (hf : ∀ j, (SheafOfModules.overFunctor S (U j)).map f = 0) : f = 0 := by
  apply (SheafOfModules.toSheaf S).map_injective
  apply sfSheaf_map_zero_of_cover hU
  intro j
  change (SheafOfModules.toSheaf (S.over (U j))).map
    ((SheafOfModules.overFunctor S (U j)).map f) = 0
  rw [hf j, Functor.map_zero]

/-- A finite pro-etale cover on which an object becomes zero after inverting the
uniformizer has one uniformizer power annihilating every cohomology sheaf.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-prop-sf-dualizable-biduality/_section.md`, proof paragraph “Choose locally a
bounded complex” and the extracted finite-cover uniform-power argument
(blueprint: lem-sf-rational-local-global-power-torsion).

Proof. The tensor-localization zero criterion supplies a local annihilating
uniformizer power for each cover member. Let `M` be the finite supremum of these
exponents, with `M = 0` for the empty cover. Write `l = v * p^e` in the coefficient
DVR, where `v` is a unit, `p` is the uniformizer, and `e > 0`. Since every local
exponent is at most `e * M`, multiplication by `l^M` annihilates each restricted
object. Natural-number scalar multiplication is repeated addition, so additive
functors preserve it without requiring compatibility of coefficient actions.
Exact slice restriction commutes with derived homology. Thus multiplication by
`l^M` annihilates the restriction of every global cohomology sheaf. Sheaf
separatedness detects that the global scalar morphism is zero, including for an
empty cover. Finally apply homology functoriality and cancel the unit factor in
the derived category to obtain the uniformizer exponent `e * M`, independently
of the cohomological degree. The hypothesis that `l` is invertible on `X` is the
node's standing assumption; the argument does not use it.

The global and slice linear structures are explicit instance arguments; the intended
ones are the canonical constant-section actions (for the global category,
`integralCoefficientLinear` when the scheme and coefficient universes agree).  Since
`l` is a unit times a power of the uniformizer and every linear structure restricts to
the integer action, the hypothesis and the conclusion are equivalent to the
corresponding `l`-power statements, so the statement says the same for every choice.
The scheme lives in universe `t` and the coefficients in `u`, independently.
This statement was checked and delivered by group Q151 on 2026-10-18.
-/
theorem sfRationalLocalGlobalPowerTorsion
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (X : AlgebraicGeometry.Scheme.{t})
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (C : DerivedCategory (integralTowerModules l E X))
    (n : ℕ)
    (U : Fin n → AlgebraicGeometry.Scheme.ProEt X)
    (hU : (AlgebraicGeometry.Scheme.ProEt.topology X).CoversTop U)
    [Linear (Padic.coefficientExtensionIntegers l E)
      (DerivedCategory (integralTowerModules l E X))]
    [∀ j : Fin n,
      Linear (Padic.coefficientExtensionIntegers l E)
        (DerivedCategory
          (SheafOfModules.{max u (t + 1)}
            ((completedIntegralCoefficientSheafUnrestricted l E X).over (U j))))]
    (hzero : ∀ j : Fin n,
      IsZero
        ((ScalarLocalization.localization
          (Padic.coefficientExtensionIntegers l E)
          (DerivedCategory
            (SheafOfModules.{max u (t + 1)}
              ((completedIntegralCoefficientSheafUnrestricted l E X).over (U j))))
          (Padic.coefficientExtensionUniformizer l E)).obj
          ((SheafOfModules.overFunctor.{max u (t + 1)}
            (completedIntegralCoefficientSheafUnrestricted l E X)
            (U j)).mapDerivedCategory.obj C))) :
    ∃ N : ℕ, ∀ d : ℤ,
      (DerivedCategory.homologyFunctor (integralTowerModules l E X) d).map
        ((Padic.coefficientExtensionUniformizer l E) ^ N • 𝟙 C) = 0 := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let p := Padic.coefficientExtensionUniformizer l E
  let S := completedIntegralCoefficientSheafUnrestricted l E X
  let F (j : Fin n) := SheafOfModules.overFunctor.{max u (t + 1)} S (U j)
  obtain ⟨e, v, he, hv⟩ := sfUniformizer_prime_factorization l E
  have hpowers (j : Fin n) : ∃ a : ℕ,
      p ^ a • 𝟙 ((F j).mapDerivedCategory.obj C) = 0 :=
    sfScalarLocalization_power p _ (hzero j)
  choose a ha using hpowers
  let N := Finset.univ.sup a
  have hlocal (j : Fin n) :
      (l ^ N) • 𝟙 ((F j).mapDerivedCategory.obj C) = 0 := by
    have hb : a j ≤ e * N := le_trans
      (Finset.le_sup (f := a) (Finset.mem_univ j))
      (Nat.le_mul_of_pos_left N he)
    have hz := sfPower_smul_zero_of_le p hb (ha j)
    have hcast : (l : R) ^ N • 𝟙 ((F j).mapDerivedCategory.obj C) = 0 := by
      rw [hv, mul_pow, mul_smul, ← pow_mul, hz, smul_zero]
    simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hcast
  have hglobal (d : ℤ) :
      (l ^ N) • 𝟙 ((DerivedCategory.homologyFunctor (integralTowerModules l E X) d).obj C)
        = 0 := by
    let H := DerivedCategory.homologyFunctor (integralTowerModules l E X) d
    apply sfModule_map_zero_of_cover S hU
    intro j
    have hmap : (F j).map ((l ^ N) • 𝟙 (H.obj C)) = 0 := by
      let G := DerivedCategory.homologyFunctor
        (SheafOfModules.{max u (t + 1)} (S.over (U j))) d
      let K := (F j).mapDerivedCategory.obj C
      let α : (F j).obj (H.obj C) ≅ G.obj K :=
        ((F j).mapDerivedCategoryHomologyFunctorIso d).app C
      have : G.Additive := sfHomology_additive _ d
      have hz : G.map ((l ^ N) • 𝟙 K) = G.map 0 := congrArg G.map (hlocal j)
      rw [G.map_nsmul, G.map_id, G.map_zero] at hz
      have hz' : (l ^ N) • 𝟙 ((F j).obj (H.obj C)) = 0 := by
        apply (cancel_mono α.hom).mp
        simpa only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          CategoryTheory.Category.id_comp, CategoryTheory.Category.comp_id, zero_comp,
          comp_zero] using congrArg (fun f ↦ α.hom ≫ f) hz
      rw [(F j).map_nsmul, (F j).map_id]
      exact hz'
    exact hmap
  refine ⟨e * N, ?_⟩
  intro d
  let H := DerivedCategory.homologyFunctor (integralTowerModules l E X) d
  have := sfHomology_additive (integralTowerModules l E X) d
  have hz : H.map ((l : R) ^ N • 𝟙 C) = 0 := by
    dsimp only [H]
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Functor.map_nsmul]
    rw [CategoryTheory.Functor.map_id]
    exact hglobal d
  have hcancel := congrArg (fun f ↦ H.map (((v⁻¹ : Rˣ) : R) ^ N • 𝟙 C) ≫ f) hz
  rw [← H.map_comp] at hcancel
  have hscalar : (((v⁻¹ : Rˣ) : R) ^ N) * (l : R) ^ N = p ^ (e * N) := by
    rw [hv, mul_pow, ← mul_assoc, ← mul_pow]
    simp only [Units.inv_mul, one_pow, one_mul, pow_mul]
    rfl
  simpa only [Linear.smul_comp, Category.id_comp,
    ← mul_smul, hscalar, CategoryTheory.Functor.map_zero, comp_zero] using hcancel

end WeilConjectures
