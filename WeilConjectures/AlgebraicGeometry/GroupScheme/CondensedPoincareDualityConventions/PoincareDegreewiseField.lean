/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.CondensedPoincareDualityConventions.PoincareDualityConventionsCondensed
public import WeilConjectures.PoincareDuality.DegreeOfPairing
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedPointPerfectness

/-! # Degreewise Poincare duality over the coefficient fields

Source: latest blueprint, part-duality-trace-formula/sec-poincare-duality/
sec-global-duality-and-the-poincare-pairing/sk-thm-derived-duality/
thm-pod-degreewise-perfectness-over-a-field.md
(blueprint: thm-pod-degreewise-perfectness-over-a-field).

Cohomology is represented by maps from the regular scalar unit to a shifted
scalar complex. The pairing is fixed by the existing cup/evaluation/trace
composite and its evaluation-normalized elimination of the point Tate line.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open WeilConjectures.SixFunctors WeilConjectures.PoincareDuality
open scoped CategoryTheory.Obj TensorProduct

namespace WeilConjectures.CondensedPoincareDualityConventions

variable (P : CondensedPoincareDualityConventions.{u}) (c : PoincareCoefficient)

/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingIsAlgClosed : IsAlgClosed P.datum.k := IsAlgClosure.isAlgClosed P.datum.k₀
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingFiniteType : LocallyOfFiniteType P.structureMap := by
  change LocallyOfFiniteType P.smoothIndex.map
  exact P.smoothIndex.finiteType
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingQuasiCompact : QuasiCompact P.structureMap := by
  change QuasiCompact P.smoothIndex.map
  exact P.smoothIndex.quasiCompact
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingSeparated : IsSeparated P.structureMap := by
  change IsSeparated P.smoothIndex.map
  exact P.smoothIndex.separated
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingSmooth : SmoothOfRelativeDimension P.dimension P.structureMap := by
  change SmoothOfRelativeDimension P.dimension P.smoothIndex.map
  exact P.smoothIndex.smooth
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingResidueInverse : ∀ x : P.X, Invertible (P.ell : P.X.residueField x) :=
  TraceCup.residueInverse P.ell P.datum P.different (Over.mk P.structureMap)
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingPointResidueInverse : ∀ x : P.s, Invertible (P.ell : P.s.residueField x) :=
  TraceCup.residueInverse P.ell P.datum P.different (Over.mk (𝟙 P.s))

/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingOverFiniteType : LocallyOfFiniteType (Over.mk P.structureMap).hom := by
  change LocallyOfFiniteType P.structureMap
  infer_instance
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingOverQuasiCompact : QuasiCompact (Over.mk P.structureMap).hom := by
  change QuasiCompact P.structureMap
  infer_instance
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingOverSeparated : IsSeparated (Over.mk P.structureMap).hom := by
  change IsSeparated P.structureMap
  infer_instance
/-- Inherited from the fixed Poincare conventions.
Source: fixed setting (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
instance pairingOverSmooth :
    SmoothOfRelativeDimension P.dimension (Over.mk P.structureMap).hom := by
  change SmoothOfRelativeDimension P.dimension P.structureMap
  infer_instance

/-- The scalar ring is terminal evaluation of the existing condensed coefficient.
Source: coefficient convention (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingScalar := condensedScalarRing ((P.presentation c).obj P.ell)

/-- H^i is Hom from the regular scalar unit into the i-th shift.
Source: degreewise cohomology convention
(blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingH (M : P.ambient c P.X) (i : ℤ) :=
  𝟙_ _ ⟶ ((P.pairingOrdinary c).obj M) ⟦i⟧

/-- H_c^i in the same scalar coordinates.
Source: degreewise cohomology convention
(blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingHc (M : P.ambient c P.X) (i : ℤ) :=
  𝟙_ _ ⟶ ((P.pairingCompact c).obj M) ⟦i⟧

/-- The actual positive coefficient Tate line in the existing ring coordinates.
Source: K^vee(d) in the first display
(blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingLine :=
  smoothTraceCoefficientLine P.ell ((P.presentation c).bundled P.ell)
    (P.presentation c) (Iso.refl _) P.X P.dimension

/-- Sections of the actual positive point Tate line.
Source: twist elimination (blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingL :=
  (CohomologyTransport.sections ((P.presentation c).obj P.ell) P.s).obj
    (pairingPointLine P.ell ((P.presentation c).bundled P.ell)
      (P.presentation c) (Iso.refl _) P.s P.dimension)

/-- H^0 of the negative point Tate line.
Source: the final line-valued pairing
(blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
abbrev pairingLinv :=
  pairingInverseSections P.ell ((P.presentation c).bundled P.ell)
    (P.presentation c) (Iso.refl _) P.datum.k P.dimension

/-- All arrows in FieldPairingData are uniquely determined by their displayed equations.
Source: degree-zero decomposition and twist elimination
(blueprint: thm-pod-degreewise-perfectness-over-a-field).
Proof: degreeOfPairing supplies B, the pure-tensor-normalized projection, the
inverse-line evaluation isomorphism and B'. The value equation determines B
pointwise; pure tensors generate the tensor product, so the projection is unique.
The evaluation equation determines the inverse-line isomorphism pointwise.
Its injectivity then determines B'. Proof fields are propositionally irrelevant.
No finiteness or field hypothesis is required for these identifications. -/
theorem fieldPairingData_unique (K : P.ctf c P.X)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.obj) (i : ℤ) :
    ∃! _b : P.FieldPairingData c K hK i, True := by
  sorry

/-- The unique degreewise pairing; only its proof of existence is postponed.
The preceding theorem determines all its data up to equality.
Source: the two displayed pairings
(blueprint: thm-pod-degreewise-perfectness-over-a-field). -/
def fieldPairingData (K : P.ctf c P.X)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.obj) (i : ℤ) :
    P.FieldPairingData c K hK i :=
  Classical.choose (P.fieldPairingData_unique c K hK i)

/-- Finite-dimensionality and perfectness for the actual normalized pairings.
Free and finite over the scalar field is finite-dimensionality; the untwisted
clause holds for every trivialization of the negative Tate line.
Source: all clauses of thm-pod-degreewise-perfectness-over-a-field
(blueprint: thm-pod-degreewise-perfectness-over-a-field).
Proof: derived Poincare duality identifies the twisted ordinary complex shifted
by 2d with the scalar dual of the compact complex, both perfect point complexes.
Over E or Qbar, split the bounded scalar complexes into their finite-dimensional
cohomology: H^(-i)(C^vee) is the linear dual of H^i(C), with its evaluation
pairing. The canonical shift gives H^(2d-i) on the twisted side. This proves
finite-dimensionality and perfectness of the specified scalar form. The point
Tate line is free of rank one, since every cover of Spec k splits. Elimination
of that line by the projection and evaluation equations transfers perfectness
to the untwisted line-valued form in every frame. Zero groups and all integer
degrees are included. -/
theorem degreewiseFieldPerfect (hc : c = .rational ∨ c = .qbar)
    (K : P.ctf c P.X)
    (hK : IsPerfectOnCoefficientSite ((P.presentation c).obj P.ell) P.X K.obj) (i : ℤ) :
    Module.Free (P.pairingScalar c) (P.pairingHc c K.obj i) ∧
    Module.Finite (P.pairingScalar c) (P.pairingHc c K.obj i) ∧
    Module.Free (P.pairingScalar c)
      (P.pairingH c (P.coefficientDual c K) (2 * (P.dimension : ℤ) - i)) ∧
    Module.Finite (P.pairingScalar c)
      (P.pairingH c (P.coefficientDual c K) (2 * (P.dimension : ℤ) - i)) ∧
    Module.Free (P.pairingScalar c)
      (P.pairingH c (P.coefficientDual c K ⊗ P.pairingLine c)
        (2 * (P.dimension : ℤ) - i)) ∧
    Module.Finite (P.pairingScalar c)
      (P.pairingH c (P.coefficientDual c K ⊗ P.pairingLine c)
        (2 * (P.dimension : ℤ) - i)) ∧
    (P.fieldPairingData c K hK i).twisted.IsPerfPair ∧
    Nonempty (P.pairingLinv c ≃ₗ[P.pairingScalar c] P.pairingScalar c) ∧
    ∀ t : P.pairingLinv c ≃ₗ[P.pairingScalar c] P.pairingScalar c,
      ((P.fieldPairingData c K hK i).untwisted.compr₂ t.toLinearMap).IsPerfPair := by
  sorry

end WeilConjectures.CondensedPoincareDualityConventions
