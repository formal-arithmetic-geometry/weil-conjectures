/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PointFibreQbarScalarModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.QbarRestrictionScalarCup

/-! # Native normalized point data for rational coefficients

Source: `sk-thm-sf-kunneth-relative`, point specialization, Step 1 of
`lem-sf-point-fibre-qbar-scalar-coherence`
(blueprint: lem-sf-qbar-native-point-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.PointTensorReduction
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Rational geometric-point tensor data with the native cup normalization.
Source: latest blueprint, `sk-thm-sf-kunneth-relative`, compact-support point
specialization; Step 1 of `lem-sf-point-fibre-qbar-scalar-coherence`
(blueprint: lem-sf-qbar-native-point-models).

Proof: evaluate regular-module sections at 1 and restrict along the inverse
singleton section-ring isomorphism. This gives the displayed sections isomorphism
with its specified value on every regular-module morphism. Restriction along that
ring isomorphism is exact symmetric monoidal, with ordinary cup x tensor y mapped
to x tensor y and coefficient unit r mapped through the inverse ring isomorphism.
Apply these ordinary maps on each total-complex summand and localize to obtain its
exact derived cup. For each admissible rational coefficient the perfect-point
realization writes a constructible finite-Tor N as C(Gamma N). Apply the ambient
comparison at (M,C(Gamma N)); its balanced K-flat representative identifies the
inverse tensor comparison with the exact scalar sections cup. Pure tensors,
total-summand extensionality and full faithfulness of localization identify it
with the transported native regular-sections cup. The same argument on the
coefficient in degree zero proves both unit equations and the stated unit model.
Naturality, associativity, the Koszul symmetry and both unit laws follow on the
same representatives: reassociation multiplies the same scalar factors, and
interchanging bidegrees i,j contributes the same (-1)^(ij) on both routes. -/
theorem qbarNativePointModelsOfRestriction
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (Λ : ScalarSixRing.{u}) (hΛ : IsRationalCoefficient ell Λ)
    (q : condensedRingCoefficientSections Λ.X (Spec (.of D.k)) ⋙ qbarNativeRestriction Λ ≅
      CohomologyTransport.sections Λ.X (Spec (.of D.k)))
    (hq : ∀ (M : ModuleRingedComparison.internalModules Λ.X (Spec (.of D.k)))
      (f : (condensedRingCoefficientSections Λ.X (Spec (.of D.k))).obj M),
      (q.hom.app M) f =
        (((constantSheafAdj (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}
          (MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of D.k)))).homEquiv
            (𝟙_ Ab.{u + 1}) M.X)
              (η[condensedRingObj Λ.X (Spec (.of D.k))] ≫ f.hom)).hom (ULift.up 1))
    (r : ExactSectionsDerivedCup (qbarNativeRestriction Λ))
    (hr : ∀ (M N : ModuleCat.{u + 1} (MonObj.Γ Λ.X)) (x : M) (y : N),
      (r.ordinary.μ M N) (x ⊗ₜ[condensedScalarRing Λ.X] y) =
        x ⊗ₜ[MonObj.Γ Λ.X] y)
    (hu : ∀ a : condensedScalarRing Λ.X,
      r.ordinary.ε a = (InternalAbelianSheafModule.sectionGlobalEquiv
        (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm a) :
    Nonempty (Σ P : PointData Λ D.k, { N : QbarPointNativeData Λ D.k P //
      N.sectionsIso = q ∧ N.restrictionCup = r }) := by
  sorry

/-- Rational geometric-point tensor data with the native cup normalization.
Source: latest blueprint, `sk-thm-sf-kunneth-relative`, compact-support point
specialization; Step 1 of `lem-sf-point-fibre-qbar-scalar-coherence`
(blueprint: lem-sf-qbar-native-point-models).

Proof: evaluate regular-module sections at 1 and restrict along the inverse
singleton section-ring isomorphism. This gives the displayed sections isomorphism
with its specified value on every regular-module morphism. Restriction along that
ring isomorphism is exact symmetric monoidal, with ordinary cup x tensor y mapped
to x tensor y and coefficient unit r mapped through the inverse ring isomorphism.
Apply these ordinary maps on each total-complex summand and localize to obtain its
exact derived cup. For each admissible rational coefficient the perfect-point
realization writes a constructible finite-Tor N as C(Gamma N). Apply the ambient
comparison at (M,C(Gamma N)); its balanced K-flat representative identifies the
inverse tensor comparison with the exact scalar sections cup. Pure tensors,
total-summand extensionality and full faithfulness of localization identify it
with the transported native regular-sections cup. The same argument on the
coefficient in degree zero proves both unit equations and the stated unit model.
Naturality, associativity, the Koszul symmetry and both unit laws follow on the
same representatives: reassociation multiplies the same scalar factors, and
interchanging bidegrees i,j contributes the same (-1)^(ij) on both routes. -/
theorem qbarNativePointModels
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D.p) (Λ : ScalarSixRing.{u}) (hΛ : IsRationalCoefficient ell Λ)
    (q : condensedRingCoefficientSections Λ.X (Spec (.of D.k)) ⋙ qbarNativeRestriction Λ ≅
      CohomologyTransport.sections Λ.X (Spec (.of D.k)))
    (hq : ∀ (M : ModuleRingedComparison.internalModules Λ.X (Spec (.of D.k)))
      (f : (condensedRingCoefficientSections Λ.X (Spec (.of D.k))).obj M),
      (q.hom.app M) f =
        (((constantSheafAdj (Scheme.ProEt.topology (Spec (.of D.k))) Ab.{u + 1}
          (MorphismProperty.Over.mkIdTerminal @WeaklyEtale (Spec (.of D.k)))).homEquiv
            (𝟙_ Ab.{u + 1}) M.X)
              (η[condensedRingObj Λ.X (Spec (.of D.k))] ≫ f.hom)).hom (ULift.up 1)) :
    Nonempty (Σ P : PointData Λ D.k, { N : QbarPointNativeData Λ D.k P //
      N.sectionsIso = q }) := by
  obtain ⟨r, hr, hu⟩ := qbarRestrictionScalarCup
    (InternalAbelianSheafModule.sectionGlobalEquiv
      (coherentTopology Profinite.{u}) Λ.X (⊤_ Profinite.{u}) terminalIsTerminal).symm
  obtain ⟨P, N, hqN, _⟩ :=
    qbarNativePointModelsOfRestriction D ell hell Λ hΛ q hq r hr hu
  exact ⟨P, N, hqN⟩

end AlgebraicGeometry.ProEtale.CondensedRing
