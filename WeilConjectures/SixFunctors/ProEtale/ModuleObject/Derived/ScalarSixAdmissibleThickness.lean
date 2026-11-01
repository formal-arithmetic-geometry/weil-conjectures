/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import all WeilConjectures.AlgebraicGeometry.SixFunctors.BrownHypothesesSmall
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated

/-! # Thickness of bounded constant-model constructible complexes for admissible rings.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-admissible-thickness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Thickness of bounded constant-model constructible complexes for admissible rings.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (3), thickness and scalar induction.
(blueprint: lem-sfb-scalar-six-admissible-thickness).

Proof in words: use the coefficient isomorphism from admissibility to reduce to a
native coefficient. In the finite case the normalized finite discrete equivalence
identifies bounded constant-model constructibility with the ordinary finite-ring
notion; proEtale_bounded_constructible_isTriangulated supplies triangles and shifts.
A retract has cohomology the kernel of its complementary idempotent; descend this
idempotent to the etale constructible heart and use its kernel closure, as in
finiteCtfRetractEtaleImages (the argument for constructibility uses only boundedness).
For integral coefficients integralConstantModelHeart gives triangulation and ambient
kernel closure; a cohomological retract is the kernel of one minus its idempotent,
so it remains constructible. For fields coefficientHeartTriangulated gives all three
properties directly. Vanishing outside a bounded interval is inherited by retracts
in all cases. The coefficient-isomorphism equivalence preserves cohomology, shifts,
triangles and the same finite constant models, hence transports these conclusions.
Zero coefficients and the empty scheme give the zero category and satisfy them too. -/
theorem sfbAdmissibleConstructibleThickness (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (constantModelBoundedConstructible Λ.X X.left).IsTriangulated ∧
      (constantModelBoundedConstructible Λ.X X.left).IsStableUnderRetracts := by
  classical
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  let E₀ : PadicAlgCl.FiniteIntermediateField ell := ⟨⊥, inferInstance⟩
  have hi (E : PadicAlgCl.FiniteIntermediateField ell) :
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E) X.left
        ).IsTriangulated ∧
      (constantModelBoundedConstructible (Profinite.padicIntegersRingObj ell E) X.left
        ).IsStableUnderRetracts := by
    obtain ⟨hk, he⟩ := isConstantModelConstructible_serre_padicIntegers X.left ell E
    exact thick_of_heart_closure _ X.left hk he
  have hf := constantModelBoundedConstructible_field_triangulated ell X.left
  obtain ⟨_, _, _, _, _, _, _, _, qIso, zIso, _⟩ :=
    Profinite.base_coefficient_condensed_identification.{u} ell
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
    have : Finite A := hfin
    obtain ⟨j⟩ := AdmissibleTriangulated.finiteCoefficientLiftIso.{u} A
    exact thick_coefficient_iso (e ≪≫ j).symm X.left
      (finite_bounded_thick (ULift.{u} A) X.left)
  · obtain ⟨e⟩ := h
    exact thick_coefficient_iso (e ≪≫ zIso).symm X.left (hi E₀)
  · obtain ⟨e⟩ := h
    exact thick_coefficient_iso (e ≪≫ qIso).symm X.left
      ⟨(hf.1 E₀).2.1, (hf.1 E₀).2.2⟩
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact thick_coefficient_iso e.symm X.left ⟨(hf.1 E).2.1, (hf.1 E).2.2⟩
  · obtain ⟨E, ⟨e⟩⟩ := h
    exact thick_coefficient_iso e.symm X.left (hi E)
  · obtain ⟨e⟩ := h
    exact thick_coefficient_iso e.symm X.left ⟨hf.2.2.1, hf.2.2.2⟩

end AlgebraicGeometry.ProEtale.CondensedRing
