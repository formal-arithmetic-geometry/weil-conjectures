/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformConstructibleExtTorsion
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartCommonStratification
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NoetherianStratifiedLattice
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Subobject.Lattice
import WeilConjectures.AlgebraicGeometry.RationalExtFiniteSourceModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.AlgebraicGeometry.LisseFiniteDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UniformConstructibleExtIntegral
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleExtContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Vanishing for a prepared rational source

Source: latest blueprint, rational Ext proof, localization and the two devissages.
(blueprint: lem-rational-ext-prepared-vanishing).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
universe w v

namespace CategoryTheory.Abelian.Ext

private theorem constructibleExt_subsingleton_of_source_iso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A B N : C} {q : ℕ} (e : A ≅ B)
    (h : Subsingleton (Ext A N q)) : Subsingleton (Ext B N q) := by
  refine ⟨fun x y ↦ ?_⟩
  have hh := h.elim ((mk₀ e.hom).comp x (zero_add q))
    ((mk₀ e.hom).comp y (zero_add q))
  have hh' := congrArg (fun z ↦ (mk₀ e.inv).comp z (zero_add q)) hh
  simpa only [mk₀_comp_mk₀_assoc, e.inv_hom_id, mk₀_id_comp] using hh'

private theorem constructibleExt_subsingleton_of_source_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {A N : C} {q : ℕ} (h : IsZero A) : Subsingleton (Ext A N q) := by
  have hz (x : Ext A N q) : x = 0 := by
    rw [← mk₀_id_comp x, h.eq_of_src (𝟙 A) 0, mk₀_zero, zero_comp]
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

/-- Ext from an object vanishes if it vanishes from each quotient of a finite filtration.
Source: latest blueprint, rational Ext proof, source filtration induction, and Mathlib's
contravariant Ext exact sequence (blueprint: lem-rational-ext-prepared-vanishing).

Proof: The bottom subobject has zero underlying object, so its Ext is zero in every
degree. At a successor the subobject inclusion is monic and its cokernel gives a short
exact sequence. Exactness of Ext in the first variable makes every class in the middle
come from the quotient, because its image in the previous subobject is zero. The
quotient's Ext is zero, so the middle class is zero. Induct over the finite index. The
top subobject is isomorphic to the whole object, and Ext transports along this iso.
This proof includes filtrations of length zero. -/
private theorem constructibleExt_finiteSubobjectFiltration
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤)
    (hquot : ∀ a : Fin n,
      Subsingleton (Ext (cokernel (Subobject.ofLE _ _ (hstep a))) N q)) :
    Subsingleton (Ext M N q) := by
  have hF (a : Fin (n + 1)) : Subsingleton (Ext (F a : C) N q) := by
    induction a using Fin.induction with
    | zero =>
      rw [hbot]
      exact constructibleExt_subsingleton_of_source_zero
        (initialIsInitial.isZero.of_iso Subobject.botCoeIsoInitial)
    | succ a ih =>
      let f := Subobject.ofLE _ _ (hstep a)
      let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f) }
      have hz (x : Ext (F a.succ : C) N q) : x = 0 := by
        obtain ⟨z, hz⟩ := contravariant_sequence_exact₂ hS N x (ih.elim _ _)
        rw [← hz, (hquot a).elim z 0, comp_zero]
      exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  exact constructibleExt_subsingleton_of_source_iso
    (Subobject.isoOfEq _ _ htop ≪≫ Subobject.underlyingIso (𝟙 M)) (hF _)

/-- Isomorphic models for the successive quotients suffice in finite Ext devissage.
Source: the same finite-filtration argument, transporting the quotient groups along
isomorphisms (blueprint: lem-rational-ext-prepared-vanishing).

Proof: transport each quotient's Ext vanishing along its specified source isomorphism,
then apply the finite subobject filtration theorem. -/
private theorem constructibleExt_finiteSubobjectFiltrationOfIso
    {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] (M N : C) (q n : ℕ) (F : Fin (n + 1) → Subobject M)
    (hstep : ∀ a : Fin n, F a.castSucc ≤ F a.succ)
    (hbot : F 0 = ⊥) (htop : F (Fin.last n) = ⊤) (G : Fin n → C)
    (hiso : ∀ a : Fin n,
      Nonempty (cokernel (Subobject.ofLE _ _ (hstep a)) ≅ G a))
    (hquot : ∀ a : Fin n, Subsingleton (Ext (G a) N q)) :
    Subsingleton (Ext M N q) := by
  apply constructibleExt_finiteSubobjectFiltration M N q n F hstep hbot htop
  intro a
  obtain ⟨e⟩ := hiso a
  exact constructibleExt_subsingleton_of_source_iso e.symm (hquot a)

end CategoryTheory.Abelian.Ext

namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 2000000 in
-- The assembly checks the actual coefficient functors and dependent quotient isomorphisms.
/-- Assemble the prepared graded bound by the actual coefficient-heart filtration.
Source: latest blueprint, rational Ext proof, source devissage.
(blueprint: lem-rational-ext-prepared-vanishing).

Proof: Finite type and quasi-compactness over a field make X Noetherian. Form the open
prefixes of the supplied ordered partition. The coefficient-heart filtration theorem
identifies the bottom and top subobjects and each successive cokernel with the
canonical locally closed extension of the source restriction. The graded vanishing
lemma kills the Ext groups of these cokernels. Apply finite contravariant Ext devissage
to conclude for the whole source. The global-lattice assertion is passed through from
the graded lemma, where its proof uses only target devissage and the unrefined source.
This assembly works also for a filtration with zero strata. -/
-- The filtration assembly retains the actual coefficient functors and quotient isomorphisms.
end AlgebraicGeometry.ProEtale
