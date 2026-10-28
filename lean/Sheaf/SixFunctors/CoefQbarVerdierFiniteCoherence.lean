/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.SixFunctors.CoefQbarVerdierData
import Sheaf.SixFunctors.RationalHomIdentifications

/-! # Normalized coherence of the finite Verdier comparisons

Source: thm-coef-qbar-verdier, proof steps 1--2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CoefQbarVerdier

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

open AlgebraicallyClosedCoefficients (Index Coefficient)

omit [IsAlgClosure (Padic l) Ω] in
/-- Simultaneous finite data from rational Verdier duality and finite Hom identification.
Source: blueprint thm-coef-qbar-verdier, proof steps 1 and 5
(blueprint: lem-coef-qbar-verdier-finite-coherence).

Proof: apply the simultaneous rational duality theorem. Choose integral dualizing
presentations at each finite coefficient field, specialize its duality and scalar
families, and use the finite Hom-identification theorem for each identity field map.
The normalized scalar comparisons themselves supply beta, so betaNormalized is reflexive. -/
theorem finiteData_nonempty : Nonempty (Finite D l hl Ω X) := by
  classical
  obtain ⟨d, s, hs, _, _⟩ := coef_rational_verdier D l hl X
  let w := fun E : Index l Ω ↦ Classical.choice
    (IntegralFiniteExtension.dualizingDatum_nonempty l X D hl (Coefficient.{u} l Ω E))
  let a := fun E : Index l Ω ↦ d (Coefficient.{u} l Ω E) (w E)
  let e := fun (E L : Index l Ω) (h : E ≤ L) ↦
    s (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  have H (E : Index l Ω) : Nonempty
      (RationalOperations.HomIdentification l (Coefficient.{u} l Ω E) X D hl (w E) (a E)) := by
    obtain ⟨h, _, _⟩ := RationalOperations.rationalHom_identifications
      D l hl X (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω E)
      (AlgHom.id (Padic l) (Coefficient.{u} l Ω E)) (w E) (w E) (a E) (a E)
    exact ⟨h⟩
  refine ⟨{ omega := w, datum := a, hom := fun E ↦ Classical.choice (H E)
            scalar := e, normalized := ?_, beta := ?_, betaNormalized := ?_ }⟩
  · intro E L h
    exact hs (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω L)
      (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h) (w E) (w L)
  · intro E L h
    exact (e E L h).comparison
  · intro E L h
    exact HEq.rfl


/-- The normalized finite comparisons obey the prescribed unit and tower equations.
Source: thm-coef-qbar-verdier, proof steps 1--2; thm-coef-rational-verdier,
identity and composition clauses
(blueprint: lem-coef-qbar-verdier-finite-coherence).

Proof: replace each beta by the scalar comparison using betaNormalized. For an
identity inclusion, coefficientInclusion_laws identifies its field map with the
identity. Apply RationalVerdier.extension_unit to the normalized scalar datum.
Its unit j equals the prescribed rational scalar unit: both are localizations
of the integral multiplication unit conjugated by the normalized completion map.
Every rational object has the same underlying integral representative, so the
component normalization proves equality of these natural isomorphisms. This is
the unitor used in FiniteCoherent. For a tower E <= L <= M, apply
RationalVerdier.extension_composition to the three normalized scalar data,
using coefficientInclusion_laws to identify the composite field map. Its a equals
the prescribed scalar associator: their components are the localizations of the
same integral balanced tensor associator conjugated by the three completion
comparisons. The defining uniqueness of the rational scalar comparison and
associator_existsUnique identify a with associator. Substitute in the rational
tower equation, retaining the heterogeneous equality at its dependent endpoints.
Both arguments include repeated coefficient fields, the zero object and the empty scheme. -/
theorem finite_coherent (F : Finite D l hl Ω X) : FiniteCoherent D l hl Ω X F := by sorry

end WeilConjectures.CoefQbarVerdier
