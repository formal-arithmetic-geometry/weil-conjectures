/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.Paper.FiniteCoefficientPoint
import Sheaf.Paper.PointSectionsDerivedReduction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Integral point sections detect zero objects

Source: the reduction and completeness argument in step 8 of
`lem-weil-point-fibre-equivalence` (blueprint: lem-weil-point-integral-sections-conservative).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Integral sections detect zero objects once the finite fibres are equivalences.
Source: geometric-point fibre equivalence, step 8; Stacks Tags 093M and 06YL
(blueprint: lem-weil-point-integral-sections-conservative).

Proof: compare the two presentations of the module derived category using their
cohomology functors. Derived reduction of the zero section complex is zero, because
derived tensor is triangulated. The normalized sections/reduction comparison makes
sections of each finite reduction zero. The finite fibre equivalences make those
reductions zero. Restriction of scalars preserves zero, so all entries of the
reduction tower vanish. Its product is zero by the product universal property.
The defining completeness triangle then has its last two vertices zero; hence
its first vertex, the original integral complex, is zero. The argument includes
the zero complex and every positive reduction level, with no boundedness assertion
about the chosen resolutions.
-/
theorem pointIntegralSections_conservative
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (hf : ∀ (n : ℕ) (hn : 1 ≤ n), (pointFiniteFibre D l hl E n hn).IsEquivalence)
    (K : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
    (hK : IsZero ((pointFibreIntegralAmbient D l E).obj K.obj)) : IsZero K.obj := by
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let Γ := pointIntegralSections l E D.k
  have hΓ : IsZero (Γ.mapDerivedCategory.{u + 2, u + 2}.obj K.obj) := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    have h : IsZero (Γ.obj ((DerivedCategory.homologyFunctor _ i).obj K.obj)) := by
      let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} R) :=
        HasDerivedCategory.ofIsGrothendieckAbelian _
      exact ((DerivedCategory.homologyFunctor _ i).map_isZero hK).of_iso
        ((Γ.mapDerivedCategoryHomologyFunctorIso i).app K.obj)
    exact h.of_iso ((Γ.mapDerivedCategoryHomologyFunctorIso i).app K.obj).symm
  have hred (n : ℕ) :
      IsZero ((scalarReductionDerivedExtension l E (Spec (.of D.k)) n).obj K.obj) := by
    let N := (HomologicalComplex.single _ (.up ℤ) 0).obj
      (ModuleCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
    let t := (DerivedCategory.exists_derivedTensor_second_factor_functor
      (pointReductionQuotient l E n)).2
    obtain ⟨c, ht⟩ := t.choose_spec.choose_spec.2.1 N
    let := c
    have := ht
    have hT : IsZero ((pointReductionTensorSections D l E n).obj K) :=
      (t.choose.obj N).map_isZero hΓ
    obtain ⟨e⟩ := (point_sections_derived_reduction D l E hl n).1
    have hS : IsZero ((pointReductionSectionsTensor D l E n).obj K) :=
      hT.of_iso (e.app K).symm
    let A := Padic.coefficientExtensionRing l E (n + 1)
    let X := (scalarReductionDerivedExtension l E (Spec (.of D.k)) n).obj K.obj
    let F := pointFiniteSections D.k A
    have hR (i : ℤ) : IsZero (F.obj ((DerivedCategory.homologyFunctor _ i).obj X)) :=
      ((DerivedCategory.homologyFunctor _ i).map_isZero hS).of_iso
        ((F.mapDerivedCategoryHomologyFunctorIso i).app X)
    let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :=
      HasDerivedCategory.ofIsGrothendieckAbelian _
    have hsmall : IsZero (F.mapDerivedCategory.{u + 2, u + 1}.obj X) := by
      apply DerivedCategory.isZero_of_forall_isZero_homology
      intro i
      exact (hR i).of_iso ((F.mapDerivedCategoryHomologyFunctorIso i).app X).symm
    obtain ⟨a, b, hab, hb⟩ := K.property.2
    let X' : (intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))).FullSubcategory :=
      ⟨X, (hb n).1⟩
    have := hf (n + 1) (by omega)
    have hz : IsZero ((pointFiniteFibre D l hl E (n + 1) (by omega)).obj X') := by
      exact IsZero.of_full_of_faithful_of_isZero
        (DerivedCategory.pointFiniteCohomology (ULift.{u + 1, u} A)).ι _ hsmall
    have hz' : IsZero X' :=
      IsZero.of_full_of_faithful_of_isZero
        (pointFiniteFibre D l hl E (n + 1) (by omega)) _ hz
    exact (intrinsicFiniteTorsionConstructible l E (n + 1) _ (Spec (.of D.k))).ι.map_isZero hz'
  let T := fun n : ℕ ↦ (sfDerivedReductionRestricted l E (Spec (.of D.k)) n).obj K.obj
  obtain ⟨hp, δ, hδ⟩ := K.property.1
  let := hp
  have hz (n : ℕ) : IsZero (T n) :=
    (scalarReductionRestriction l E (Spec (.of D.k)) n).mapDerivedCategory.map_isZero (hred n)
  have hprod : IsZero (∏ᶜ T) :=
    (limit.isLimit (Discrete.functor T)).isZero_pt (Functor.isZero _ (fun n ↦ hz n.as))
  exact Triangle.isZero₁_of_isZero₂₃ _ hδ hprod hprod

end WeilConjectures
