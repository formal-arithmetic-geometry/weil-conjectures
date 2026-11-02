/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeEnvelope.NativeNormalizedRealEnvelope
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights

/-! # Eigenvalues of the native constant twist

Source: latest blueprint, the normalization step of lem-wf-envelope-real.
(blueprint: lem-wf-envelope-real-native-twist-spectrum)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeEnvelope

/-- The normalizing constant twist multiplies local eigenvalues by b to the residue degree.
This is a statement about the actual native local operators, with no purity hypothesis.
Source: latest blueprint, lem-wf-constant-twist-weight.proof.md, first sentence.
(blueprint: lem-wf-envelope-real-native-twist-spectrum).

Proof: pull back the right unitor F tensor 1 to the geometric point and take actual
unit sections, obtaining a linear equivalence between the twisted and original fibres.
The constant line is the coefficient unit with structure equal to the canonical unit
structure followed by scalar b. Its d-fold Weil structure is scalar b^d times the
canonical unit structure. Induct on the positive-power index: the pullback compositors
preserve multiplication by constant scalars, and the monoidal unit axioms identify the
untwisted tensor structure under the right unitor. The point-return comparison fixes
the constant section 1, so the resulting local operator is b^d A. Conjugacy preserves
eigenvalues. For an eigenvector of b^d A with eigenvalue alpha, divide by b^d to get
an A-eigenvector with eigenvalue beta and alpha = b^d beta. The nonzero vector stays
nonzero under the unitor, and b is a unit. The formula holds for every compatible lift
and has a vacuous conclusion when there are no eigenvalues. -/
theorem normalizedTwist_eigenvalues
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (F : condensedWeilModules (Profinite.padicAlgClRingObj l)
      (D.geometricFrobenius X₀).hom)
    (b : (PadicAlgCl l)ˣ)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue
      (NativeL2.closedOperator D l X₀ (normalizedTwist D l X₀ hl F b) x i hi).hom α) :
    ∃ β : ULift.{u + 1} (PadicAlgCl l),
      Module.End.HasEigenvalue (NativeL2.closedOperator D l X₀ F x i hi).hom β ∧
      α.down = (b : PadicAlgCl l) ^ NativeCondensedModule.localClosedPointDegree D X₀ x *
        β.down := by
  sorry

end WeilConjectures.NativeEnvelope
