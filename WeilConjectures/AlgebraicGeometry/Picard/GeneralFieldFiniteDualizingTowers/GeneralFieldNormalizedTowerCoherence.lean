/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldFiniteDualizingTowerData

/-! # Finite-counit normalization of tensor units and composites

Source: current blueprint, `sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`.
(blueprint: lem-sf-general-field-normalized-tower-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteDualizingTowers
namespace WeilConjectures.GeneralFieldFiniteDualizingTowers
variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The specified derived tensor unit and composite of normalized comparisons satisfy
the defining finite-counit evaluation equations. This asserts normalization only.
Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, final paragraph
(blueprint: lem-sf-general-field-normalized-tower-coherence).
Proof: transpose the derived unit using adjoint uniqueness for identity restriction.
Its transpose is the inverse canonical identity-restriction map. Evaluating that
map and using the section-normalized intrinsic realization/restriction comparison
gives the identity finite counit mate, by the identity clause of the general-field
finite coefficient theorem. For composition, transpose the displayed map twice.
The left-adjoint uniqueness definition of the balanced tensor associator identifies
this with successive restriction of the two transposes followed by canonical
restriction composition. Evaluation of exact restriction is the identity-on-sections
square. Its compatibility with successive restriction follows first on ordinary
modules by their unchanged underlying sections, and then on complexes and roofs by
exact localization. The intrinsic realization restriction comparisons have the same
composition normalization: check on constant generating sections and use their
unique characterization; localize the resulting equality. Substituting the two
given normalization equations reduces the result to the pro-etale finite counit
composition equation, transposed under the specified finite scalar adjunctions.
The latter is the pro_site_composition clause of the general-field finite theorem.
All transports are thus fixed by scalar units and counits. -/
theorem normalized_unit_and_composition
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p) :
    (∀ (s : Stage l E)
      (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
        (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1}
          (ringMap X (identity s)))) (P : Realization k X s),
      IsComparison k X (identity s) A P P
        ((SheafOfModules.systemScalarModelDerivedUnit.{u + 1, u, u + 1}
          (sequenceMap_identity X s) A).hom.app P.obj)) ∧
    (∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
      (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
        (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
      (B : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
        (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X b)))
      (D : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
        (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1}
          (ringMap X (composite a b))))
      (P : Realization k X s) (Q : Realization k X t) (R : Realization k X v)
      (f : A.model.T.obj P.obj ⟶ Q.obj) (g : B.model.T.obj Q.obj ⟶ R.obj),
      IsComparison k X a A P Q f → IsComparison k X b B Q R g →
      IsComparison k X (composite a b) D P R
        ((SheafOfModules.systemScalarModelDerivedComposition.{u + 1, u, u + 1}
          (sequenceMap_composite X a b) A B D).inv.app P.obj ≫ B.model.T.map f ≫ g)) := by
  sorry

end WeilConjectures.GeneralFieldFiniteDualizingTowers
