/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernel
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp

/-! # Ordinary integral quotient Roos exact sequence

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-roos)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

/-- A constructible integral module has its ordinary quotient product resolution.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-roos).

Proof: write Q_n = M/ell^(n+1)M with its cokernel projection. The transition
Q_(n+1) -> Q_n is induced by the identity of M, hence is epimorphic. On a
w-contractible affine presentation test of each stratum the presentation matrix
has continuous integral entries on an extremally disconnected component space.
The spaces of integral solutions are compact. Projectivity of the component
space supplies continuous compatible lifts of quotient solutions. Thus the
finite presentation is separated and complete for these ordinary quotients.
The ell powers and uniformizer powers are cofinal. Restriction to constructible
strata preserves limits, and exact open/closed localization reassembles the
finite stratification, giving M = lim Q_n as sheaves. The pro-etale topos is
replete, so inverse limit of this epimorphic tower has no higher cohomology.
The canonical map from M to product Q_n and one minus the shift induced by
the quotient transitions therefore form the asserted short exact Roos sequence.
Empty schemes and zero modules give zero sequences; torsion is allowed. The
statement uses ordinary quotients and does not assert constructibility of
negative derived-reduction cohomology. -/
theorem originalIntegralOrdinaryQuotientRoos
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (X : Scheme.{u})
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X))
    (hM : IsConstructibleModuleObject
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) X) M) :
    (OriginalIntegralQuotientSequence.sequence ell M).ShortExact := by
  classical
  let F : ℕᵒᵖ ⥤ _ := Functor.ofOpSequence
    (X := fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M))
    (fun n ↦ OriginalIntegralQuotientSequence.transition ell n M)
  have hF (n : ℕ) : Epi (F.map (homOfLE n.le_succ).op) := by
    simpa [F, Functor.ofOpSequence_map_homOfLE_succ] using
      (inferInstance : Epi (OriginalIntegralQuotientSequence.transition ell n M))
  let P : Fan (fun n : ℕ ↦ F.obj (op n)) :=
    Fan.mk (∏ᶜ (fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 M)))
      (fun n ↦ Pi.π _ n)
  have hP : IsLimit P := by
    exact productIsProduct _
  let t := OriginalIntegralQuotientSequence.shift ell M
  have ht (n : ℕ) : t ≫ P.proj n =
      P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op := by
    simp [t, P, F, OriginalIntegralQuotientSequence.shift,
      Functor.ofOpSequence_map_homOfLE_succ]
  have hrep : EpiπAppZeroOfEpi
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ell E) X)) :=
    Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat
  have hepi : Epi (𝟙 _ - t) :=
    epi_one_sub_of_epiπAppZeroOfEpi hrep hF hP t ht
  letI : Epi (OriginalIntegralQuotientSequence.sequence ell M).g := by
    change Epi (𝟙 _ - OriginalIntegralQuotientSequence.shift ell M)
    exact hepi
  obtain ⟨hk⟩ := originalIntegralOrdinaryQuotientKernel ell E X M hM
  letI : Mono (OriginalIntegralQuotientSequence.sequence ell M).f := by
    change Mono (OriginalIntegralQuotientSequence.augmentation ell M)
    exact mono_of_isLimit_fork hk
  exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }

end AlgebraicGeometry.ProEtale.CondensedRing
