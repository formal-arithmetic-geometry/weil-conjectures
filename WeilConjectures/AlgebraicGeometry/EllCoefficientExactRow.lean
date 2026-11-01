/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedCoefficientRegularQuotients
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # The exact four-term row of finite coefficient quotients

Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-ell-coefficient-exact-row).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u vC uC r

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})

/-- The existing abelian module-sheaf structure, with sheafification fixed in the
coefficient universe. This explicit specialization prevents the small-site default from
identifying the coefficient universe with the site-object universe. Source: Stacks,
Modules on Sites, and the coefficient setup in sk-lem-sp-tower
(blueprint: lem-sp-ell-coefficient-exact-row). -/
instance (priority := 2000) spCoefficientModulesAbelian
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{max u (t + 1)}) :
    Abelian (SheafOfModules.{max u (t + 1)} R) := by
  letI := integralCoefficientAbSheafify.{t, u} T
  letI := integralCoefficientAbLocallyBijective.{t, u} T
  exact { SheafOfModules.instAbelian R with
    toPreadditive := SheafOfModules.instPreadditive R }

/-- Coefficient reductions are already surjective on sections, hence epic on modules.
Source: sk-lem-sp-tower, quotient coefficients
(blueprint: lem-sp-ell-coefficient-exact-row). -/
theorem spRelativeReduction_epi (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n) :
    Epi (spRelativeReduction l E T N n m hn hm) := by
  apply (SheafOfModules.forget _).epi_of_epi_map
  apply PresheafOfModules.epi_of_surjective
  intro U x
  obtain ⟨y, hy⟩ := projection_surjective l E T _ (ell_normalized l E T m) U x
  refine ⟨(spCompletedEllCommRingProjection l E T n).hom.app U y, ?_⟩
  change (spLevelReduction l E T n m hm).hom.app U
      ((spCompletedEllCommRingProjection l E T n).hom.app U y) = x
  have hp : ((sp_completed_coefficient_limit l E T).choose.hom ≫
      limit.π (spCoefficientRings l E T) (op n)) ≫ spLevelReduction l E T n m hm =
      (sp_completed_coefficient_limit l E T).choose.hom ≫
        limit.π (spCoefficientRings l E T) (op m) := by
    rw [Category.assoc, spLevelReduction, limit.w]
  exact (RingHom.congr_fun (congrArg (fun f => (f.hom.app U).hom) hp) y).trans hy

omit [Fact l.Prime] in
private theorem power_kernel_descend {R A B : Type*} [CommRing R] [Ring A]
    [Ring B] (t : R) (n m : ℕ) (hm : m ≤ n)
    (p : R →+* A) (q : R →+* B) (hq : Function.Surjective q)
    (hp : RingHom.ker p = Ideal.span {t ^ (n + 1)})
    (hk : RingHom.ker q = Ideal.span {t ^ (m + 1)}) :
    ∃ a : B →+ A, ∀ x, a (q x) = p (t ^ (n - m) * x) := by
  let g := p.toAddMonoidHom.comp (AddMonoidHom.mulLeft (t ^ (n - m)))
  have hg : q.toAddMonoidHom.ker ≤ g.ker := by
    intro x hx
    have hx' : x ∈ Ideal.span {t ^ (m + 1)} := by
      rw [← hk]
      exact hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx'
    change p (t ^ (n - m) * x) = 0
    apply RingHom.mem_ker.1
    rw [hp]
    apply Ideal.mem_span_singleton.2
    refine ⟨y, ?_⟩
    rw [hy, ← mul_assoc, ← pow_add]
    congr 2
    omega
  refine ⟨q.toAddMonoidHom.liftOfSurjective hq ⟨g, hg⟩, ?_⟩
  intro x
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

omit [Fact l.Prime] in
private theorem sectionwise_exact {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    (S : ShortComplex (SheafOfModules.{r} R)) [S.HasHomology]
    (h : ∀ (U : Cᵒᵖ) (x : S.X₂.val.obj U), S.g.val.app U x = 0 →
      ∃ y, S.f.val.app U y = x) : S.Exact := by
  rw [S.exact_iff_epi_toCycles]
  apply (SheafOfModules.forget _).epi_of_epi_map
  apply PresheafOfModules.epi_of_surjective
  intro U x
  have hx : S.g.val.app U (S.iCycles.val.app U x) = 0 :=
    congrArg (fun f ↦ f.val.app U x) S.iCycles_g
  obtain ⟨y, hy⟩ := h U (S.iCycles.val.app U x) hx
  refine ⟨y, ?_⟩
  have hi : Function.Injective (S.iCycles.val.app U) := by
    apply (ModuleCat.mono_iff_injective _).1
    exact (SheafOfModules.evaluation R U).map_mono S.iCycles
  apply hi
  exact (congrArg (fun f ↦ f.val.app U y) S.toCycles_i).trans hy

omit [Fact l.Prime] in
private theorem sheaf_nsmul_apply {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {X Y : SheafOfModules.{r} R} (f : X ⟶ Y) (k : ℕ) (U : Cᵒᵖ)
    (x : X.val.obj U) : (k • f).val.app U x = k • f.val.app U x := by
  induction k with
  | zero =>
    simp only [zero_smul]
    rfl
  | succ k ih =>
    rw [succ_nsmul, succ_nsmul]
    change (k • f).val.app U x + f.val.app U x =
      k • f.val.app U x + f.val.app U x
    rw [ih]

private abbrev completedSection (U : T.ProEtᵒᵖ) :=
  (completedIntegralCommRingSheafUnrestricted l E T).obj.obj U

private abbrev coefficientProjection (j : ℕ) (U : T.ProEtᵒᵖ) :
    completedSection l E T U →+* (spCoefficientRing l E T j).obj.obj U :=
  ((spCompletedEllCommRingProjection l E T j).hom.app U).hom

private theorem coefficientProjection_surj (j : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective (coefficientProjection l E T j U) :=
  projection_surjective l E T _ (ell_normalized l E T j) U

private theorem coefficientProjection_ker (j : ℕ) (U : T.ProEtᵒᵖ) :
    RingHom.ker (coefficientProjection l E T j U) =
      Ideal.span {(l : completedSection l E T U) ^ (j + 1)} := by
  have h := ((sp_completed_coefficient_regular_quotients l E T).2.2.2.2.1 j).2.2 U |>.2
  change RingHom.ker (coefficientProjection l E T j U) =
    Ideal.span {scalarHom l E T U l ^ (j + 1)} at h
  simpa only [map_natCast] using h

private theorem coefficientProjection_compat (n m : ℕ) (hm : m ≤ n)
    (U : T.ProEtᵒᵖ) (x : completedSection l E T U) :
    (spLevelReduction l E T n m hm).hom.app U (coefficientProjection l E T n U x) =
      coefficientProjection l E T m U x := by
  have hp : ((sp_completed_coefficient_limit l E T).choose.hom ≫
      limit.π (spCoefficientRings l E T) (op n)) ≫ spLevelReduction l E T n m hm =
      (sp_completed_coefficient_limit l E T).choose.hom ≫
        limit.π (spCoefficientRings l E T) (op m) := by
    rw [Category.assoc, spLevelReduction, limit.w]
  exact RingHom.congr_fun (congrArg (fun f ↦ (f.hom.app U).hom) hp) x

private def coefficientPowerMap (n m : ℕ) (hm : m ≤ n) (U : T.ProEtᵒᵖ) :
    (spCoefficientRing l E T m).obj.obj U →+ (spCoefficientRing l E T n).obj.obj U :=
  (power_kernel_descend (l : completedSection l E T U) n m hm
    (coefficientProjection l E T n U) (coefficientProjection l E T m U)
    (coefficientProjection_surj l E T m U) (coefficientProjection_ker l E T n U)
    (coefficientProjection_ker l E T m U)).choose

private theorem coefficientPowerMap_projection (n m : ℕ) (hm : m ≤ n)
    (U : T.ProEtᵒᵖ) (x : completedSection l E T U) :
    coefficientPowerMap l E T n m hm U (coefficientProjection l E T m U x) =
      coefficientProjection l E T n U ((l : completedSection l E T U) ^ (n - m) * x) :=
  (power_kernel_descend (l : completedSection l E T U) n m hm
    (coefficientProjection l E T n U) (coefficientProjection l E T m U)
    (coefficientProjection_surj l E T m U) (coefficientProjection_ker l E T n U)
    (coefficientProjection_ker l E T m U)).choose_spec x

private theorem coefficientProjection_naturality (j : ℕ) {U V : T.ProEtᵒᵖ}
    (f : U ⟶ V) (x : completedSection l E T U) :
    coefficientProjection l E T j V
        ((completedIntegralCommRingSheafUnrestricted l E T).obj.map f x) =
      (spCoefficientRing l E T j).obj.map f (coefficientProjection l E T j U x) :=
  RingHom.congr_fun (congrArg CommRingCat.Hom.hom
    ((spCompletedEllCommRingProjection l E T j).hom.naturality f)) x

private theorem coefficientProjection_zero (j : ℕ) (U : T.ProEtᵒᵖ)
    (x : completedSection l E T U) :
    coefficientProjection l E T j U x = 0 ↔
      ∃ y, (l : completedSection l E T U) ^ (j + 1) * y = x := by
  rw [← RingHom.mem_ker, coefficientProjection_ker, Ideal.mem_span_singleton]
  constructor <;> rintro ⟨y, hy⟩ <;> exact ⟨y, hy.symm⟩

private theorem completedPower_regular (k : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Injective (fun x : completedSection l E T U ↦
      (l : completedSection l E T U) ^ k * x) := by
  cases k with
  | zero =>
    intro x y h
    simpa only [pow_zero, one_mul] using h
  | succ k =>
    have h := ((sp_completed_coefficient_regular_quotients l E T).2.2.2.1 k U).2
    change Function.Injective (fun x : completedSection l E T U ↦
      scalarHom l E T U l ^ (k + 1) * x) at h
    simpa only [map_natCast] using h

private theorem coefficientPowerMap_inj (n m : ℕ) (hm : m ≤ n) (U : T.ProEtᵒᵖ) :
    Function.Injective (coefficientPowerMap l E T n m hm U) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T m U x
  rw [coefficientPowerMap_projection] at hx
  obtain ⟨y, hy⟩ := (coefficientProjection_zero l E T n U _).1 hx
  apply (coefficientProjection_zero l E T m U x).2
  refine ⟨y, ?_⟩
  apply completedPower_regular l E T (n - m) U
  dsimp only
  rw [← mul_assoc, ← pow_add, show n - m + (m + 1) = n + 1 by omega]
  exact hy

private theorem coefficientProjection_smul (j k : ℕ) (U : T.ProEtᵒᵖ)
    (x : completedSection l E T U) :
    coefficientProjection l E T j U ((l : completedSection l E T U) ^ k * x) =
      l ^ k • coefficientProjection l E T j U x := by
  simp only [map_mul, map_pow, map_natCast, nsmul_eq_mul, Nat.cast_pow]

private theorem coefficient_killed (j : ℕ) (U : T.ProEtᵒᵖ)
    (x : (spCoefficientRing l E T j).obj.obj U) : l ^ (j + 1) • x = 0 := by
  obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T j U x
  rw [← coefficientProjection_smul]
  exact (coefficientProjection_zero l E T j U _).2 ⟨x, rfl⟩

private theorem coefficientPowerMap_smul (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (U : T.ProEtᵒᵖ) (b : (spCoefficientRing l E T N).obj.obj U)
    (x : (spCoefficientRing l E T m).obj.obj U) :
    coefficientPowerMap l E T n m hm U
        ((spLevelReduction l E T N m (hm.trans hn)).hom.app U b * x) =
      (spLevelReduction l E T N n hn).hom.app U b *
        coefficientPowerMap l E T n m hm U x := by
  obtain ⟨b, rfl⟩ := coefficientProjection_surj l E T N U b
  obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T m U x
  rw [coefficientProjection_compat, coefficientProjection_compat, ← map_mul,
    coefficientPowerMap_projection, coefficientPowerMap_projection, ← map_mul]
  exact congrArg (coefficientProjection l E T n U) (mul_left_comm _ _ _)

private theorem coefficientPowerMap_naturality (n m : ℕ) (hm : m ≤ n)
    {U V : T.ProEtᵒᵖ} (f : U ⟶ V) (x : (spCoefficientRing l E T m).obj.obj U) :
    coefficientPowerMap l E T n m hm V ((spCoefficientRing l E T m).obj.map f x) =
      (spCoefficientRing l E T n).obj.map f (coefficientPowerMap l E T n m hm U x) := by
  obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T m U x
  rw [← coefficientProjection_naturality, coefficientPowerMap_projection,
    coefficientPowerMap_projection, ← coefficientProjection_naturality]
  congr 1
  simp only [map_mul, map_pow, map_natCast]

omit [Fact l.Prime] in
private def restrictedAdditiveMap {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} {R A B : Sheaf J RingCat.{r}}
    (p : R ⟶ A) (q : R ⟶ B) (a : ∀ U : Cᵒᵖ, A.obj.obj U →+ B.obj.obj U)
    (ha : ∀ (U : Cᵒᵖ) (b : R.obj.obj U) (x : A.obj.obj U),
      a U (p.hom.app U b * x) = q.hom.app U b * a U x)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : A.obj.obj U),
      a V (A.obj.map f x) = B.obj.map f (a U x)) :
    (SheafOfModules.restrictScalars p).obj (SheafOfModules.unit A) ⟶
      (SheafOfModules.restrictScalars q).obj (SheafOfModules.unit B) where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := ((SheafOfModules.restrictScalars p).obj (SheafOfModules.unit A)).val.obj U)
        (Y := ((SheafOfModules.restrictScalars q).obj (SheafOfModules.unit B)).val.obj U)
        { toFun := a U
          map_add' := map_add _
          map_smul' := fun b x ↦ ha U b x }
      naturality := by
        intro U V f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact hnat f x }

private def relativePowerMap (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n) :
    spRelativeCoefficient l E T N m (hm.trans hn) ⟶
      spRelativeCoefficient l E T N n hn :=
  restrictedAdditiveMap (spLevelReduction l E T N m (hm.trans hn))
    (spLevelReduction l E T N n hn) (coefficientPowerMap l E T n m hm)
    (coefficientPowerMap_smul l E T N n m hn hm)
    (coefficientPowerMap_naturality l E T n m hm)

/-- The four-term exact quotient row over a common upper coefficient ring.
Source: sk-lem-sp-tower, coefficient calculation
(blueprint: lem-sp-ell-coefficient-exact-row).

Proof. Write R for the completed coefficient sheaf and t for ell. The specified
projections identify B_(j+1) with R/t^(j+1), and are surjective on sections.
Define a by lifting a section of B_(m+1) to R, multiplying by t^(n-m), and reducing
to B_(n+1). Another lift differs by t^(m+1), so the result is independent of the
lift. It is natural on site objects and linear over B_(N+1). The equation q a =
t^(n-m) follows on lifts. Cancellation of the regular power t^(n-m) in R proves
injectivity. If t^(m+1)x is zero modulo t^(n+1), regular cancellation expresses
x modulo t^(n+1) as t^(n-m)y, proving exactness at the first middle term.
The kernel of q consists of multiples of t^(m+1), proving exactness at the second.
The sectionwise quotient map is surjective and hence epic. These arguments also
cover n=m, where a is the identity and the middle differential is zero. -/
theorem sp_ell_coefficient_exact_row (N n m : ℕ) (hn : n ≤ N) (hm : m ≤ n) :
    ∃ a : spRelativeCoefficient l E T N m (hm.trans hn) ⟶
        spRelativeCoefficient l E T N n hn,
      spRelativeReduction l E T N n m hn hm ≫ a =
        l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn) ∧
      Mono a ∧ Epi (spRelativeReduction l E T N n m hn hm) ∧
      ∃ (had : a ≫ (l ^ (m + 1) • 𝟙 _) = 0)
        (hdq : (l ^ (m + 1) • 𝟙 _) ≫ spRelativeReduction l E T N n m hn hm = 0),
        (ShortComplex.mk a (l ^ (m + 1) • 𝟙 _) had).Exact ∧
        (ShortComplex.mk (l ^ (m + 1) • 𝟙 _) _ hdq).Exact := by
  let a := relativePowerMap l E T N n m hn hm
  have ha : spRelativeReduction l E T N n m hn hm ≫ a =
      l ^ (n - m) • 𝟙 (spRelativeCoefficient l E T N n hn) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (spCoefficientRing l E T n).obj.obj U at x
    obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T n U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, sheaf_nsmul_apply]
    change coefficientPowerMap l E T n m hm U
        ((spLevelReduction l E T n m hm).hom.app U
          (coefficientProjection l E T n U x)) =
      l ^ (n - m) • coefficientProjection l E T n U x
    rw [coefficientProjection_compat, coefficientPowerMap_projection,
      coefficientProjection_smul]
  have hmono : Mono a := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact coefficientPowerMap_inj l E T n m hm U
  have had : a ≫ (l ^ (m + 1) • 𝟙 _) = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (spCoefficientRing l E T m).obj.obj U at x
    obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T m U x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, sheaf_nsmul_apply]
    change l ^ (m + 1) •
      coefficientPowerMap l E T n m hm U (coefficientProjection l E T m U x) = 0
    rw [coefficientPowerMap_projection, ← coefficientProjection_smul]
    apply (coefficientProjection_zero l E T n U _).2
    refine ⟨x, ?_⟩
    rw [← mul_assoc, ← pow_add, show m + 1 + (n - m) = n + 1 by omega]
  have hdq : (l ^ (m + 1) • 𝟙 _) ≫
      spRelativeReduction l E T N n m hn hm = 0 := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (spCoefficientRing l E T n).obj.obj U at x
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, sheaf_nsmul_apply]
    change (spLevelReduction l E T n m hm).hom.app U (l ^ (m + 1) • x) = 0
    rw [map_nsmul]
    exact coefficient_killed l E T m U _
  refine ⟨a, ha, hmono, spRelativeReduction_epi l E T N n m hn hm,
    had, hdq, ?_, ?_⟩
  · apply sectionwise_exact
    intro U x hx
    change (spCoefficientRing l E T n).obj.obj U at x
    simp only [sheaf_nsmul_apply] at hx
    change l ^ (m + 1) • x = 0 at hx
    obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T n U x
    rw [← coefficientProjection_smul] at hx
    obtain ⟨y, hy⟩ := (coefficientProjection_zero l E T n U _).1 hx
    have he : (l : completedSection l E T U) ^ (n - m) * y = x := by
      apply completedPower_regular l E T (m + 1) U
      dsimp only
      rw [← mul_assoc, ← pow_add, show m + 1 + (n - m) = n + 1 by omega]
      exact hy
    refine ⟨coefficientProjection l E T m U y, ?_⟩
    change coefficientPowerMap l E T n m hm U (coefficientProjection l E T m U y) = _
    rw [coefficientPowerMap_projection, he]
  · apply sectionwise_exact
    intro U x hx
    change (spCoefficientRing l E T n).obj.obj U at x
    change (spLevelReduction l E T n m hm).hom.app U x = 0 at hx
    obtain ⟨x, rfl⟩ := coefficientProjection_surj l E T n U x
    rw [coefficientProjection_compat] at hx
    obtain ⟨y, hy⟩ := (coefficientProjection_zero l E T m U x).1 hx
    refine ⟨coefficientProjection l E T n U y, ?_⟩
    simp only [sheaf_nsmul_apply]
    change l ^ (m + 1) • coefficientProjection l E T n U y = _
    rw [← coefficientProjection_smul, hy]

end AlgebraicGeometry.ProEtale
