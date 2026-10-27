/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.SfOpenClosedTriangleData
public import Sheaf.Paper.FieldWeilShriekShiftData

/-! # The normalized rational closed unit and the actual proper adjunction -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Identification of the normalized rational closed term with the actual adjunction
unit for the base-changed closed immersion.
Source: blueprint localization proof, exact closed direct image and coefficient-passage
paragraphs (blueprint: lem-sf-normalized-rational-closed-comparison).
Proof: exact completed-ring inverse image along the closed immersion identifies with
its specified completed pullback, by the quotient-normalized immersion comparison.
Exact closed direct image is its right adjoint. Apply these functors termwise and
pass their unit to the derived categories. The integral normalization identifies
P.closedTerm and P.unit with that exact composite and unit on representative complexes;
essential surjectivity of the derived quotient and naturality extend the identities
to every integral constructible object. Rational localization transports the adjunction
and its unit: on integral arrows this is localization of the same unit equation,
and tensor bilinearity extends naturality to all rational arrows. Uniqueness of right
adjoints identifies this localized right adjoint with fieldWeilProper and retains the
unit equation. Finally conjugate by the closed comparison in the rational normalization
of Q. This gives the displayed natural isomorphism with its prescribed unit equation.
No Frobenius, open complement, or localization triangle is involved; the empty closed
subscheme and zero objects are included by the same adjunction argument. -/
theorem sfNormalizedRationalRecollement_closed_comparison
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ Z₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Z₀.hom] [QuasiCompact Z₀.hom]
    (i₀ : Z₀ ⟶ X₀) [IsClosedImmersion i₀.left]
    (i : (D.geometricFiber Z₀).left ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i]
    (_hi : i = ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map i₀).left)
    (P : SfRecollementPresentation
      (sfIntegralConstructibleCategory l E (D.geometricFiber X₀).left))
    (Q : SfRecollementPresentation
      (sfRationalConstructibleCategory l E (D.geometricFiber X₀).left))
    (_hP : SfIntegralRecollementNormalization l E i (sfRecollementGeometricNoetherian D X₀) P)
    (_hQ : SfRationalRecollementNormalization l E (D.geometricFiber X₀).left P Q) :
    ∃ c : Q.closedTerm ≅ fieldWeilPull D l hl E i₀ ⋙ fieldWeilProper D l hl E i₀,
      ∀ K, Q.unit.app K ≫ c.hom.app K = (fieldWeilProperAdj D l hl E i₀).unit.app K := by
  sorry

end WeilConjectures
