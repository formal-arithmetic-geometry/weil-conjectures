/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Algebra.Homology.RegularScalarQuotientNotation
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-! # The module presentation of a regular power quotient

Source: blueprint sk-lem-sp-tower, first proof paragraph;
Stacks Project, Tag 03EI, lemma-sheafification-exact.
(blueprint: lem-sp-regular-scalar-quotient-presentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.RegularScalarQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J CommRingCat.{r}]
  (R : Sheaf J CommRingCat.{r}) (t : (unit R).sections)

private instance quotientLocallyBijectiveCommRing :
    J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r}
      (CategoryTheory.forget CommRingCat.{r}) := preservesFilteredColimitsOfSize_shrink _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

private def rawQuotient (k : ℕ) :
    PresheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj :=
  (PresheafOfModules.restrictScalars
    (Functor.whiskerRight (sectionPowerQuotientProjection R t (k + 1))
      (forget₂ CommRingCat RingCat))).obj
    (PresheafOfModules.unit
      (sectionPowerQuotientPresheaf R t (k + 1) ⋙ forget₂ CommRingCat RingCat))

private def rawUnit (k : ℕ) : rawQuotient R t k ⟶ (Q R t k).val where
  app U := by
    unfold Q B projection principalPowerRingQuotient
    exact ModuleCat.ofHom
      (X := (rawQuotient R t k).obj U)
      (Y := (ModuleCat.restrictScalars
        (((toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U).hom.comp
          (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U)))).obj
            (ModuleCat.of ((sheafify J (sectionPowerQuotientPresheaf R t (k + 1))).obj U)
              ((sheafify J (sectionPowerQuotientPresheaf R t (k + 1))).obj U)))
      { toFun := fun x ↦ (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U x
        map_add' :=
          ((toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U).hom.map_add
        map_smul' b x := by
          change R.obj.obj U at b
          change R.obj.obj U ⧸ sectionPowerIdeal R t (k + 1) U at x
          change (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U
              (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) b * x) =
            (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U
              (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) b) *
                (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).app U x
          exact map_mul _ _ _ }
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    unfold Q B projection principalPowerRingQuotient at *
    exact ConcreteCategory.congr_hom
      ((toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))).naturality f) x

private instance rawUnit_injective (k : ℕ) :
    PresheafOfModules.IsLocallyInjective J (rawUnit R t k) := by
  constructor
  intro U x y h
  unfold rawUnit Q B projection principalPowerRingQuotient at h
  exact Presheaf.equalizerSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))) x y h

private instance rawUnit_surjective (k : ℕ) :
    PresheafOfModules.IsLocallySurjective J (rawUnit R t k) := by
  constructor
  intro U x
  unfold Q B projection principalPowerRingQuotient at x
  unfold rawUnit Q B projection principalPowerRingQuotient
  exact Presheaf.imageSieve_mem J
    (toSheafify J (sectionPowerQuotientPresheaf R t (k + 1))) x

omit [HasSheafify J CommRingCat.{r}] in
private theorem power_apply (k : ℕ) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (endoPow (globalSectionMultiplication R t) k).val.app U x =
      (@id (R.obj.obj U) (t.val U)) ^ k * x := by
  induction k with
  | zero => simp [endoPow]
  | succ k ih =>
    change (@id (R.obj.obj U)
      ((endoPow (globalSectionMultiplication R t) k).val.app U x)) *
        (@id (R.obj.obj U) (t.val U)) = _
    rw [ih, pow_succ]
    dsimp only [id]
    ac_rfl

omit [EssentiallySmall.{r} C] in
private theorem rawUnit_class (k : ℕ) (U : Cᵒᵖ) (x : R.obj.obj U) :
    (rawUnit R t k).app U (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) x) =
      (ringMap (projection R t k)).val.app U x := by
  change (projection R t k).hom.app U x = (projection R t k).hom.app U x * 1
  exact (mul_one _).symm

private theorem projection_zero (k : ℕ) :
    endoPow (globalSectionMultiplication R t) (k + 1) ≫
      ringMap (projection R t k) = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change R.obj.obj U at x
  change (ringMap (projection R t k)).val.app U
    ((endoPow (globalSectionMultiplication R t) (k + 1)).val.app U x) = 0
  rw [power_apply, ← rawUnit_class]
  have hz : Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U)
      ((@id (R.obj.obj U) (t.val U)) ^ (k + 1) * x) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.2
    exact Ideal.mem_span_singleton.2 ⟨x, rfl⟩
  rw [hz]
  exact map_zero _

private def rawDesc (k : ℕ) {M : Modules R} (g : unit R ⟶ M)
    (hg : endoPow (globalSectionMultiplication R t) (k + 1) ≫ g = 0) :
    rawQuotient R t k ⟶ M.val where
  app U := ModuleCat.ofHom (X := (rawQuotient R t k).obj U) (Y := M.val.obj U)
    ((sectionPowerIdeal R t (k + 1) U).liftQ (g.val.app U).hom (by
      intro x hx
      change x ∈ Ideal.span {(@id (R.obj.obj U) (t.val U)) ^ (k + 1)} at hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
      rw [hy]
      change (g.val.app U) ((@id (R.obj.obj U) (t.val U)) ^ (k + 1) * y) = 0
      rw [← power_apply R t]
      exact congrArg (fun f ↦ f.val.app U y) hg))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact congrArg (fun h ↦ h x) (g.val.naturality f)

omit [HasSheafify J CommRingCat.{r}] in
private theorem rawDesc_class (k : ℕ) {M : Modules R} (g : unit R ⟶ M)
    (hg : endoPow (globalSectionMultiplication R t) (k + 1) ≫ g = 0)
    (U : Cᵒᵖ) (x : R.obj.obj U) :
    (rawDesc R t k g hg).app U
      (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) x) = g.val.app U x := rfl

omit [HasSheafify J CommRingCat.{r}] in
private theorem power_mono (k : ℕ)
    (hregular : ∀ U : Cᵒᵖ, Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x)) :
    Mono (endoPow (globalSectionMultiplication R t) k) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U x y hxy
  change (endoPow (globalSectionMultiplication R t) k).val.app U x =
    (endoPow (globalSectionMultiplication R t) k).val.app U y at hxy
  rw [power_apply, power_apply] at hxy
  have hp (j : ℕ) : Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) ^ j * x) := by
    induction j with
    | zero =>
      intro x y h
      simpa only [pow_zero, one_mul] using h
    | succ j hj =>
      intro x y h
      apply hj
      apply hregular U
      simpa only [pow_succ', mul_assoc] using h
  exact hp k hxy

/-- The quotient projection is the cokernel of multiplication by the positive scalar power,
and regularity makes this sequence short exact.

Proof: cancel t successively to see that multiplication by t^(k+1) is injective
on every R(U). Its sectionwise cokernel is R(U)/(t^(k+1)). Regard these quotients
as presheaves of modules over R. The sheafification functor is exact, so the
sheafified sequence is short exact. The underlying abelian sheaf of this module
sheafification agrees with that of ring sheafification, by preservation of
sheafification by the forgetful functors. The induced module structure is the
one obtained by restricting the regular quotient module along its projection:
on representatives both actions send (r,[x]) to [rx]. The comparison thus
identifies the last arrow with ringMap of the canonical quotient projection.
No nonzero assumption is needed: a unit scalar and the zero ring give zero
quotients and the same exact sequence.
Source: Stacks Project, Tag 03EI, lemma-sheafification-exact.
(blueprint: lem-sp-regular-scalar-quotient-presentation). -/
theorem regularScalarQuotient_presentation
    (hregular : ∀ U : Cᵒᵖ, Function.Injective
      (fun x : R.obj.obj U ↦ (@id (R.obj.obj U) (t.val U)) * x)) (k : ℕ) :
    ∃ hz : endoPow (globalSectionMultiplication R t) (k + 1) ≫
        ringMap (projection R t k) = 0,
      (ShortComplex.mk (endoPow (globalSectionMultiplication R t) (k + 1))
        (ringMap (projection R t k)) hz).ShortExact := by
  let f := endoPow (globalSectionMultiplication R t) (k + 1)
  let q := ringMap (projection R t k)
  have hz : f ≫ q = 0 := projection_zero R t k
  have hmono : Mono f := power_mono R t (k + 1) hregular
  have hext {M : Modules R} {a b : Q R t k ⟶ M} (h : q ≫ a = q ≫ b) : a = b := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := rawUnit R t k) M.isSheaf).injective
    ext U x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change a.val.app U ((rawUnit R t k).app U _) =
      b.val.app U ((rawUnit R t k).app U _)
    rw [rawUnit_class]
    exact congrArg (fun g ↦ g.val.app U x) h
  let desc {M : Modules R} (g : unit R ⟶ M) (hg : f ≫ g = 0) : Q R t k ⟶ M :=
    ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
      (f := rawUnit R t k) M.isSheaf).symm (rawDesc R t k g hg)⟩
  have hd {M : Modules R} (g : unit R ⟶ M) (hg : f ≫ g = 0) : q ≫ desc g hg = g := by
    have hunit := (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := rawUnit R t k) M.isSheaf).apply_symm_apply (rawDesc R t k g hg)
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := congrArg (fun h ↦ h.app U
      (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) x)) hunit
    change (desc g hg).val.app U (q.val.app U x) = g.val.app U x
    change (desc g hg).val.app U
      ((rawUnit R t k).app U
        (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) x)) =
      (rawDesc R t k g hg).app U
        (Ideal.Quotient.mk (sectionPowerIdeal R t (k + 1) U) x) at h
    rw [rawUnit_class, rawDesc_class] at h
    exact h
  have hc : IsColimit (CokernelCofork.ofπ q hz) :=
    CokernelCofork.IsColimit.ofπ q hz (fun g hg ↦ desc g hg) hd
      (fun g hg m hm ↦ hext (hm.trans (hd g hg).symm))
  exact ⟨hz, { exact := ShortComplex.exact_of_g_is_cokernel _ hc
               mono_f := hmono
               epi_g := epi_of_isColimit_cofork hc }⟩

end CategoryTheory.RegularScalarQuotient
