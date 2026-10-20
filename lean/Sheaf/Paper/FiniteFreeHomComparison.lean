/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! # Evaluation comparison for a bounded finite free etale complex

Source: Weil blueprint, sec-six-functors, sk-prop-sf-rf-shriek-preservation,
node lem-sf-hom-comparison-finite-free; Stacks Project, Tags 08JI, 03EO and 03EL
(blueprint: lem-sf-hom-comparison-finite-free).

Fixed-coefficient module sheaves use the recorded ModuleCat-valued encoding.
The canonical comparison below is the curry of pulled-back evaluation, using the
canonical derived tensor comparison and the exact-functor identification.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open MonoidalClosed Functor.LaxMonoidal Functor.OplaxMonoidal

-- Use finite coefficients directly when synthesizing Noetherianity.
attribute [local instance 20000] isNoetherian_of_finite
-- The ring structures do not require expanding the chosen DVR data.
attribute [local irreducible] Padic.coefficientExtensionAbsoluteValue
  Padic.coefficientExtensionIntegers Padic.coefficientExtensionUniformizer
  Padic.coefficientExtensionIdeal

private theorem finite_copower_dualizable
    {A : Type*} [Category A] [Preadditive A] [MonoidalCategory A]
    [MonoidalPreadditive A] [HasFiniteCoproducts A]
    (U : A) (hU : IsDualizable U) (n : ℕ) :
    IsDualizable (∐ fun _ : Fin n ↦ U) := by
  let : HasBinaryCoproducts A := inferInstance
  let : HasBinaryBiproducts A := HasBinaryBiproducts.of_hasBinaryCoproducts
  induction n with
  | zero =>
    apply IsZero.isDualizable
    rw [IsZero.iff_id_eq_zero]
    apply Sigma.hom_ext
    intro i
    exact Fin.elim0 i
  | succ n hn =>
    let V := ∐ fun _ : Fin n ↦ U
    let e : U ⊞ V ≅ ∐ (fun _ : Fin (n + 1) ↦ U) :=
      { hom := biprod.desc (Sigma.ι (fun _ : Fin (n + 1) ↦ U) 0)
          (Sigma.desc fun i : Fin n ↦ Sigma.ι (fun _ : Fin (n + 1) ↦ U) i.succ)
        inv := Sigma.desc (Fin.cases biprod.inl
          (fun i ↦ Sigma.ι (fun _ : Fin n ↦ U) i ≫ biprod.inr))
        hom_inv_id := by
          apply biprod.hom_ext'
          · simp
          · apply Sigma.hom_ext
            intro i
            simp
            rfl
        inv_hom_id := by
          apply Sigma.hom_ext
          intro i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · simp }
    exact (hU.biprod hn).of_iso e

private theorem isIso_ihomComparison_of_dualizable
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C]
    (G : C ⥤ D) [G.Monoidal] (K M : C) (hK : IsDualizable K) :
    IsIso ((ihomComparison G K).natTrans.app M) := by
  obtain ⟨hd⟩ := hK
  let : HasRightDual K := hd
  let := BraidedCategory.exactPairing_swap K Kᘁ
  exact Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing G Kᘁ K M

namespace AlgebraicGeometry.ProEtale

private theorem isIso_siteComparisonEvaluationHom_of_dualizable
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) [(comparisonUpperStar A T).PreservesFlat]
    (K M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology A))
    (hdual : IsDualizable K) : IsIso (siteComparisonEvaluationHom A T K M) := by
  let : (comparisonUpperStar A T).mapDerivedCategory.Monoidal :=
    siteComparisonDerivedMonoidal A T
  unfold siteComparisonEvaluationHom
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf T.smallEtaleTopology A)
  exact isIso_ihomComparison_of_dualizable
    (comparisonUpperStar A T).mapDerivedCategory K M hdual

private theorem isIso_finiteFreeHomComparison_aux
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (T : Scheme.{u}) [(comparisonUpperStar A T).PreservesFlat]
    (P N : CochainComplex (Sheaf T.smallEtaleTopology A) ℤ)
    (hP : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ ∐ fun _ : Fin r ↦
      (constantSheaf T.smallEtaleTopology A).obj (𝟙_ A))) :
    IsIso (siteComparisonEvaluationHom A T
      (_root_.DerivedCategory.Q.obj P) (_root_.DerivedCategory.Q.obj N)) := by
  classical
  let U := (constantSheaf T.smallEtaleTopology A).obj (𝟙_ A)
  have hU : IsDualizable U :=
    (isDualizable_unit (C := A)).map (constantSheaf T.smallEtaleTopology A)
  let : IsGrothendieckAbelian.{u + 1} (Sheaf T.smallEtaleTopology A) :=
    GrothendieckTopology.isGrothendieckAbelian_sheaf_smallEtaleTopology A T
  let : HasColimitsOfSize.{u + 1, u + 1} (Sheaf T.smallEtaleTopology A) :=
    IsGrothendieckAbelian.hasColimits (Sheaf T.smallEtaleTopology A)
  let : HasFiniteColimits (Sheaf T.smallEtaleTopology A) :=
    hasFiniteColimits_of_hasColimitsOfSize (Sheaf T.smallEtaleTopology A)
  let : HasFiniteCoproducts (Sheaf T.smallEtaleTopology A) :=
    hasFiniteCoproducts_of_hasFiniteColimits (Sheaf T.smallEtaleTopology A)
  have hterms (i : ℤ) : IsDualizable (P.X i) := by
    obtain ⟨r, ⟨e⟩⟩ := hfree i
    exact IsDualizable.of_iso (C := Sheaf T.smallEtaleTopology A) e.symm
      (finite_copower_dualizable (A := Sheaf T.smallEtaleTopology A) U hU r)
  obtain ⟨a, b, _, hbound⟩ := hP
  have : P.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff P a).2
    (fun i hi ↦ hbound i (Or.inl hi))
  have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).2
    (fun i hi ↦ hbound i (Or.inr hi))
  have hdual := _root_.DerivedCategory.isDualizable_Q_obj P a b hterms
  exact isIso_siteComparisonEvaluationHom_of_dualizable A T _ _ hdual

/-- Positive coefficient levels are finite, using the recorded coefficient theorem.
Source: blueprint coefficient convention and Serre, Local Fields, II §2
(blueprint: lem-sf-hom-comparison-finite-free). -/
noncomputable instance finiteFreeHomComparison_coefficientFinite
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (Padic.coefficientExtensionRing l E n) :=
  Padic.finite_coefficientExtensionRing l E n n.property

/-- The specified evaluation comparison is invertible for a bounded finite free first
complex and a bounded complex with constructible cohomology in the second variable.
Source: blueprint lem-sf-hom-comparison-finite-free, order 2083; Stacks Tags 08JI and 099R
(blueprint: lem-sf-hom-comparison-finite-free).

Proof: the coefficient unit is dualizable, and the strong monoidal constant-sheaf
functor preserves its dual. Finite biproducts of this unit are dualizable (including
rank zero), so every term of P is dualizable. The bounded-complex duality theorem
`DerivedCategory.isDualizable_Q_obj` makes Q(P) dualizable; this is the signed
dual-complex computation of the current blueprint, already proved in the library.
The exact comparison pullback has the canonical strong derived monoidal structure,
obtained from its K-flat tensor comparison and transported to its termwise derived
functor. Its internal-Hom comparison is the specified pulled-back evaluation map:
the tensorator is the inverse of the canonical oplax comparison, and both maps
are its composite with pullback of evaluation, followed by currying. The library's
`Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing` proves this map invertible
for dualizable Q(P) and every second argument. Thus the bounds and constructibility
hypotheses on N are unnecessary for the proof; the stated theorem is unchanged. -/
theorem isIso_finiteFreeHomComparison
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p) (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ+) (T : Scheme.{u})
    (_hinv : IsUnit (l : T.presheaf.obj (op ⊤)))
    (P N : CochainComplex (Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ℤ)
    (_hP : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i))
    (_hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ ∐ fun _ : Fin r ↦
      (constantSheaf T.smallEtaleTopology
        (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
          (ModuleCat.of (Padic.coefficientExtensionRing l E n)
            (Padic.coefficientExtensionRing l E n))))
    (_hN : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, (i < a ∨ b < i) → IsZero (N.X i))
    (_hc : Etale.DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing l E n) T (_root_.DerivedCategory.Q.obj N)) :
    IsIso (siteComparisonEvaluationHom
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) T
      (_root_.DerivedCategory.Q.obj P) (_root_.DerivedCategory.Q.obj N)) := by
  exact isIso_finiteFreeHomComparison_aux
    (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) T P N _hP _hfree

end AlgebraicGeometry.ProEtale
