/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SfStrictDirectImageScalarCoherence

/-! # Integral scalar comparisons from normalized strict direct-image models

Source: strict direct-image scalar comparison, Steps 3--5 and 7.
(blueprint: lem-sf-strict-direct-image-integral-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (integralTransition)

/-- Construct the normalized scalar comparisons for any specified normalized strict models.
No rational category or rational direct image occurs in this assertion.

Source: the proof of `lem-sf-strict-direct-image-scalar-comparison`, Steps 3--5 and 7.
(blueprint: lem-sf-strict-direct-image-integral-comparisons)

Proof:
The finite-free completed scalar extension commutes with ordinary direct image:
on a sheafified tensor generator the comparison is s tensor x mapped to f(s) tensor x.
Its derived comparison is fixed by the universal unit/counit square. These give the
ambient comparison data. Write beta for its derived isomorphism, chi for the
ordinary-to-strict completed tensor comparison and psi for the given reconstruction.
On a complete constructible K define the integral comparison by
psi_L inverse, then F_L(chi_Z inverse), beta inverse, chi_X, and S_X(psi_E).
Each factor is invertible on these inputs. Naturality and full faithfulness of the
constructible inclusion give a natural isomorphism, with exactly IsIntegralNormalization.
For three coefficient fields, precompose the two routes with the twofold chi.
The scalar-completion associator normalization replaces its composite with chi by
the ordinary tensor associator followed by chi. Move chi past beta by naturality;
the ambient scalar cocycle then identifies the two routes. Cancel the invertible chi.
Inserting the reconstruction conjugates cancels adjacent psi inverse/psi pairs;
naturality of psi and of the scalar associator gives HasIntegralCoherence's cocycle.
For the repeated field the same calculation uses the tensor multiplication and
completeness units and yields the prescribed integralUnit equation.
The given reconstruction commutes with shifts. The completed-scalar chain-shift
comparison gives this property for chi, and the ambient scalar comparison gives it
for beta. Composition, inverse and whiskering preserve these equations, proving
the integral comparison's CommShift law. -/
theorem strictDirectImageIntegralComparisons
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (f : Z ⟶ X) [f.IsOver (Spec (.of k))]
    (I : ∀ E : Index l Ω, IntegralModel l (Coefficient.{u} l Ω E) f) :
    ∃ (A : ∀ (E L : Index l Ω) (h : E ≤ L),
        AmbientComparison l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
          (coefficientInclusion l Ω E L h) f)
      (c : ∀ (E L : Index l Ω) (h : E ≤ L),
        integralTransition l Ω Z E L h ⋙ (I L).image ≅
          (I E).image ⋙ integralTransition l Ω X E L h),
      HasIntegralLaws l Ω f ⟨A, I, c⟩ ∧ HasIntegralCoherence l Ω f ⟨A, I, c⟩ := by sorry

end WeilConjectures.SfStrictDirectImageScalar
